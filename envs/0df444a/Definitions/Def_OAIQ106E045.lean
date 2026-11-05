-- Prove2me | Definitions.Def_OAIQ106E045
-- name    : OAIQ106E045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:56:45.813138+00:00
-- url     : https://prove2.me/theorems/2b735106-1421-4e11-860b-ca0bccf5e3f6
-- title:
--   Definitions bundle OAIQ106E045 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2155 declarations of OpenAI's Lean: 2155 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow11061`, `OAI.MUB6.Certificate.GramRows.rawRow11062`, `OAI.MUB6.Certificate.GramRows.rawRow11063`, `OAI.MUB6.Certificate.GramRows.rawRow11064`, `OAI.MUB6.Certificate.GramRows.rawRow11065`, `OAI.MUB6.Certificate.GramRows.rawRow11066`, `OAI.MUB6.Certificate.GramRows.rawRow11067`, `OAI.MUB6.Certificate.GramRows.rawRow11068`, `OAI.MUB6.Certificate.GramRows.rawRow11069`, `OAI.MUB6.Certificate.GramRows.rawRow1107`, `OAI.MUB6.Certificate.GramRows.rawRow11070`, `OAI.MUB6.Certificate.GramRows.rawRow11071`, `OAI.MUB6.Certificate.GramRows.rawRow11072`, `OAI.MUB6.Certificate.GramRows.rawRow11073`, `OAI.MUB6.Certificate.GramRows.rawRow11074`, `OAI.MUB6.Certificate.GramRows.rawRow11075`, `OAI.MUB6.Certificate.GramRows.rawRow11076`, `OAI.MUB6.Certificate.GramRows.rawRow11077`, `OAI.MUB6.Certificate.GramRows.rawRow11078`, `OAI.MUB6.Certificate.GramRows.rawRow11079`, `OAI.MUB6.Certificate.GramRows.rawRow1108`, `OAI.MUB6.Certificate.GramRows.rawRow11080`, `OAI.MUB6.Certificate.GramRows.rawRow11081`, `OAI.MUB6.Certificate.GramRows.rawRow11082`, `OAI.MUB6.Certificate.GramRows.rawRow11083`, `OAI.MUB6.Certificate.GramRows.rawRow11084`, `OAI.MUB6.Certificate.GramRows.rawRow11085`, `OAI.MUB6.Certificate.GramRows.rawRow11086`, `OAI.MUB6.Certificate.GramRows.rawRow11087`, `OAI.MUB6.Certificate.GramRows.rawRow11088`, `OAI.MUB6.Certificate.GramRows.rawRow11089`, `OAI.MUB6.Certificate.GramRows.rawRow1109`, `OAI.MUB6.Certificate.GramRows.rawRow11090`, `OAI.MUB6.Certificate.GramRows.rawRow11091`, `OAI.MUB6.Certificate.GramRows.rawRow11092`, `OAI.MUB6.Certificate.GramRows.rawRow11093`, `OAI.MUB6.Certificate.GramRows.rawRow11094`, `OAI.MUB6.Certificate.GramRows.rawRow11095`, `OAI.MUB6.Certificate.GramRows.rawRow11096`, `OAI.MUB6.Certificate.GramRows.rawRow11097` and 2115 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block1`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block111`, `MutuallyUnbiased_GramRows_Block112`, `MutuallyUnbiased_GramRows_Block113`, `MutuallyUnbiased_GramRows_Block114`, `MutuallyUnbiased_GramRows_Block115`, `MutuallyUnbiased_GramRows_Block116`, `MutuallyUnbiased_GramRows_Block117`, `MutuallyUnbiased_GramRows_Block118`, `MutuallyUnbiased_GramRows_Block119`, `MutuallyUnbiased_GramRows_Block120`, `MutuallyUnbiased_GramRows_Block121`, `MutuallyUnbiased_GramRows_Block122`, `MutuallyUnbiased_GramRows_Block123`, `MutuallyUnbiased_GramRows_Block124`, `MutuallyUnbiased_GramRows_Block125`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block31`, `MutuallyUnbiased_GramRows_Block32`, `MutuallyUnbiased_GramRows_Block33`, `MutuallyUnbiased_GramRows_Block34`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval26_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow25_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow26_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1_e`.
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

def rawRow12 : Integer.Sparse Key := [(key305, -1), (key305, -1), (key302, 2), (key335, 1), (key335, 1), (key316, -1), (key316, -1), (key340, -2), (key328, 1), (key328, 1), (key239, 1), (key239, 1), (key236, -2), (key418, -1), (key418, -1), (key406, 1), (key406, 1), (key583, 2), (key578, -1), (key578, -1), (key260, -1), (key260, -1), (key248, 1), (key248, 1), (key328, 1), (key328, 1), (key316, -1), (key316, -1), (key601, -1), (key601, -1), (key595, 1), (key595, 1), (key271, 2), (key267, -1), (key267, -1), (key340, -2), (key335, 1), (key335, 1), (key475, 1), (key475, 1), (key469, -1), (key469, -1)]

def rawRow13 : Integer.Sparse Key := [(key316, -1), (key319, -1), (key328, 2), (key302, 1), (key305, 1), (key328, -1), (key340, -1), (key305, -2), (key319, 1), (key335, 1), (key406, 1), (key409, 1), (key418, -2), (key236, -1), (key239, -1), (key578, 1), (key583, 1), (key239, 2), (key409, -1), (key418, -1), (key316, -1), (key319, -1), (key593, 1), (key595, 1), (key248, 1), (key251, 1), (key593, -1), (key601, -1), (key251, -1), (key260, -1), (key319, 1), (key328, 1), (key335, 2), (key467, -1), (key469, -1), (key267, -2), (key467, 1), (key475, 1), (key267, 1), (key271, 1), (key335, -1), (key340, -1)]

def rawRow111 : Integer.Sparse Key := [(key2899, -2), (key2915, 1), (key2906, 1), (key2797, 2), (key2915, -1), (key2833, -1), (key2797, -1), (key2787, -1), (key2899, 1), (key2810, 1), (key2978, 2), (key2994, -1), (key2985, -1), (key2643, -2), (key2994, 1), (key2730, 1), (key2643, 1), (key2633, 1), (key2978, -1), (key2707, -1), (key2945, -2), (key3004, 1), (key2962, 1), (key2655, 2), (key3004, -1), (key2749, -1), (key2655, -1), (key2617, -1), (key2749, 1), (key2672, 1), (key2751, 1), (key2730, 1), (key2915, -1), (key2833, -1), (key2656, -1), (key2643, -1), (key2915, 1), (key2797, 1), (key2656, 1), (key2620, 1), (key2751, -1), (key2675, -1)]

def rawRow112 : Integer.Sparse Key := [(key2906, -2), (key2899, 1), (key2915, 1), (key2833, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2833, -1), (key2787, 1), (key2906, 1), (key2985, 2), (key2978, -1), (key2994, -1), (key2730, -2), (key2643, 1), (key2994, 1), (key2707, 1), (key2730, 1), (key2633, -1), (key2985, -1), (key2962, -2), (key2945, 1), (key3004, 1), (key2749, 2), (key2655, -1), (key3004, -1), (key2672, -1), (key2749, -1), (key2617, 1), (key2962, 1), (key2833, 1), (key2964, 1), (key2730, -1), (key2994, -1), (key2797, -1), (key2946, -1), (key2643, 1), (key2994, 1), (key2675, 1), (key2946, 1), (key2620, -1), (key2964, -1)]

def rawRow113 : Integer.Sparse Key := [(key2906, -2), (key2915, 1), (key2899, 1), (key2833, 2), (key2915, -1), (key2797, -1), (key2833, -1), (key2810, -1), (key2906, 1), (key2787, 1), (key2985, 2), (key2994, -1), (key2978, -1), (key2730, -2), (key2994, 1), (key2643, 1), (key2730, 1), (key2707, 1), (key2985, -1), (key2633, -1), (key2962, -2), (key3004, 1), (key2945, 1), (key2749, 2), (key3004, -1), (key2655, -1), (key2749, -1), (key2672, -1), (key2962, 1), (key2617, 1), (key2964, 1), (key2833, 1), (key2994, -1), (key2730, -1), (key2946, -1), (key2797, -1), (key2994, 1), (key2643, 1), (key2946, 1), (key2675, 1), (key2964, -1), (key2620, -1)]

def rawRow114 : Integer.Sparse Key := [(key2940, -2), (key2945, 1), (key2946, 1), (key2952, 2), (key2978, -1), (key2999, -1), (key2962, -1), (key2964, -1), (key2985, 1), (key3001, 1), (key2650, 2), (key2655, -1), (key2656, -1), (key2739, -2), (key2899, 1), (key2999, 1), (key2749, 1), (key2751, 1), (key2906, -1), (key3001, -1), (key2620, -2), (key2643, 1), (key2656, 1), (key2675, 2), (key2797, -1), (key2946, -1), (key2730, -1), (key2751, -1), (key2833, 1), (key2964, 1), (key2617, 1), (key2620, 1), (key2633, -1), (key2643, -1), (key2672, -1), (key2675, -1), (key2707, 1), (key2730, 1), (key2787, 1), (key2797, 1), (key2810, -1), (key2833, -1)]

def rawRow115 : Integer.Sparse Key := [(key2940, -2), (key2946, 1), (key2945, 1), (key2952, 2), (key2999, -1), (key2978, -1), (key2964, -1), (key2962, -1), (key3001, 1), (key2985, 1), (key2650, 2), (key2656, -1), (key2655, -1), (key2739, -2), (key2999, 1), (key2899, 1), (key2751, 1), (key2749, 1), (key3001, -1), (key2906, -1), (key2620, -2), (key2656, 1), (key2643, 1), (key2675, 2), (key2946, -1), (key2797, -1), (key2751, -1), (key2730, -1), (key2964, 1), (key2833, 1), (key2620, 1), (key2617, 1), (key2643, -1), (key2633, -1), (key2675, -1), (key2672, -1), (key2730, 1), (key2707, 1), (key2797, 1), (key2787, 1), (key2833, -1), (key2810, -1)]

def rawRow116 : Integer.Sparse Key := [(key2945, -2), (key2940, 1), (key2946, 1), (key2978, 2), (key2952, -1), (key2999, -1), (key2985, -1), (key2994, -1), (key2962, 1), (key3004, 1), (key2655, 2), (key2650, -1), (key2656, -1), (key2899, -2), (key2739, 1), (key2999, 1), (key2906, 1), (key2915, 1), (key2749, -1), (key3004, -1), (key2643, -2), (key2620, 1), (key2656, 1), (key2797, 2), (key2675, -1), (key2946, -1), (key2833, -1), (key2915, -1), (key2730, 1), (key2994, 1), (key2633, 1), (key2643, 1), (key2617, -1), (key2655, -1), (key2707, -1), (key2739, -1), (key2672, 1), (key2749, 1), (key2810, 1), (key2899, 1), (key2787, -1), (key2906, -1)]

def rawRow117 : Integer.Sparse Key := [(key2945, -2), (key2946, 1), (key2940, 1), (key2978, 2), (key2999, -1), (key2952, -1), (key2994, -1), (key2985, -1), (key3004, 1), (key2962, 1), (key2655, 2), (key2656, -1), (key2650, -1), (key2899, -2), (key2999, 1), (key2739, 1), (key2915, 1), (key2906, 1), (key3004, -1), (key2749, -1), (key2643, -2), (key2656, 1), (key2620, 1), (key2797, 2), (key2946, -1), (key2675, -1), (key2915, -1), (key2833, -1), (key2994, 1), (key2730, 1), (key2643, 1), (key2633, 1), (key2655, -1), (key2617, -1), (key2739, -1), (key2707, -1), (key2749, 1), (key2672, 1), (key2899, 1), (key2810, 1), (key2906, -1), (key2787, -1)]

def rawRow118 : Integer.Sparse Key := [(key2952, -2), (key2962, 1), (key2964, 1), (key2940, 2), (key2985, -1), (key3001, -1), (key2945, -1), (key2946, -1), (key2978, 1), (key2999, 1), (key2739, 2), (key2749, -1), (key2751, -1), (key2650, -2), (key2906, 1), (key3001, 1), (key2655, 1), (key2656, 1), (key2899, -1), (key2999, -1), (key2675, -2), (key2730, 1), (key2751, 1), (key2620, 2), (key2833, -1), (key2964, -1), (key2643, -1), (key2656, -1), (key2797, 1), (key2946, 1), (key2672, 1), (key2675, 1), (key2707, -1), (key2739, -1), (key2617, -1), (key2620, -1), (key2810, 1), (key2833, 1), (key2633, 1), (key2643, 1), (key2707, -1), (key2730, -1)]

def rawRow119 : Integer.Sparse Key := [(key2952, -2), (key2964, 1), (key2962, 1), (key2940, 2), (key3001, -1), (key2985, -1), (key2946, -1), (key2945, -1), (key2999, 1), (key2978, 1), (key2739, 2), (key2751, -1), (key2749, -1), (key2650, -2), (key3001, 1), (key2906, 1), (key2656, 1), (key2655, 1), (key2999, -1), (key2899, -1), (key2675, -2), (key2751, 1), (key2730, 1), (key2620, 2), (key2964, -1), (key2833, -1), (key2656, -1), (key2643, -1), (key2946, 1), (key2797, 1), (key2675, 1), (key2672, 1), (key2739, -1), (key2707, -1), (key2620, -1), (key2617, -1), (key2833, 1), (key2810, 1), (key2643, 1), (key2633, 1), (key2730, -1), (key2707, -1)]

def rawRow120 : Integer.Sparse Key := [(key2962, -2), (key2952, 1), (key2964, 1), (key2985, 2), (key2940, -1), (key3001, -1), (key2978, -1), (key2994, -1), (key2945, 1), (key3004, 1), (key2749, 2), (key2739, -1), (key2751, -1), (key2906, -2), (key2650, 1), (key3001, 1), (key2899, 1), (key2915, 1), (key2655, -1), (key3004, -1), (key2730, -2), (key2675, 1), (key2751, 1), (key2833, 2), (key2620, -1), (key2964, -1), (key2797, -1), (key2915, -1), (key2643, 1), (key2994, 1), (key2707, 1), (key2730, 1), (key2672, -1), (key2749, -1), (key2810, -1), (key2833, -1), (key2617, 1), (key2962, 1), (key2707, 1), (key2978, 1), (key2633, -1), (key2985, -1)]

def rawRow121 : Integer.Sparse Key := [(key2962, -2), (key2964, 1), (key2952, 1), (key2985, 2), (key3001, -1), (key2940, -1), (key2994, -1), (key2978, -1), (key3004, 1), (key2945, 1), (key2749, 2), (key2751, -1), (key2739, -1), (key2906, -2), (key3001, 1), (key2650, 1), (key2915, 1), (key2899, 1), (key3004, -1), (key2655, -1), (key2730, -2), (key2751, 1), (key2675, 1), (key2833, 2), (key2964, -1), (key2620, -1), (key2915, -1), (key2797, -1), (key2994, 1), (key2643, 1), (key2730, 1), (key2707, 1), (key2749, -1), (key2672, -1), (key2833, -1), (key2810, -1), (key2962, 1), (key2617, 1), (key2978, 1), (key2707, 1), (key2985, -1), (key2633, -1)]

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow128 : Integer.Sparse Key := [(key1298, -1), (key1298, -1), (key1292, 2), (key1351, 1), (key1351, 1), (key1312, -1), (key1312, -1), (key1354, -2), (key1326, 1), (key1326, 1), (key1393, 1), (key1393, 1), (key1387, -2), (key1896, -1), (key1896, -1), (key1542, 1), (key1542, 1), (key1899, 2), (key1556, -1), (key1556, -1), (key1472, -1), (key1472, -1), (key1420, 1), (key1420, 1), (key1903, 1), (key1903, 1), (key1569, -1), (key1569, -1), (key1920, -1), (key1920, -1), (key1683, 1), (key1683, 1), (key1480, 2), (key1444, -1), (key1444, -1), (key1911, -2), (key1593, 1), (key1593, 1), (key1926, 1), (key1926, 1), (key1689, -1), (key1689, -1)]

def rawRow129 : Integer.Sparse Key := [(key1312, -1), (key1318, -1), (key1326, 2), (key1292, 1), (key1298, 1), (key1326, -1), (key1354, -1), (key1298, -2), (key1318, 1), (key1351, 1), (key1542, 1), (key1548, 1), (key1556, -2), (key1387, -1), (key1393, -1), (key1556, 1), (key1899, 1), (key1393, 2), (key1548, -1), (key1896, -1), (key1569, -1), (key1575, -1), (key1624, 1), (key1683, 1), (key1420, 1), (key1426, 1), (key1624, -1), (key1920, -1), (key1426, -1), (key1472, -1), (key1575, 1), (key1903, 1), (key1593, 2), (key1633, -1), (key1689, -1), (key1444, -2), (key1633, 1), (key1926, 1), (key1444, 1), (key1480, 1), (key1593, -1), (key1911, -1)]

def rawRow130 : Integer.Sparse Key := [(key1318, -1), (key1312, -1), (key1326, 2), (key1298, 1), (key1292, 1), (key1354, -1), (key1326, -1), (key1298, -2), (key1351, 1), (key1318, 1), (key1548, 1), (key1542, 1), (key1556, -2), (key1393, -1), (key1387, -1), (key1899, 1), (key1556, 1), (key1393, 2), (key1896, -1), (key1548, -1), (key1575, -1), (key1569, -1), (key1683, 1), (key1624, 1), (key1426, 1), (key1420, 1), (key1920, -1), (key1624, -1), (key1472, -1), (key1426, -1), (key1903, 1), (key1575, 1), (key1593, 2), (key1689, -1), (key1633, -1), (key1444, -2), (key1926, 1), (key1633, 1), (key1480, 1), (key1444, 1), (key1911, -1), (key1593, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11061 : Integer.Sparse Key := [(key1416, -6), (key1308, -6), (key1810, -6), (key1614, -6), (key1383, 2), (key1452, 2), (key1416, 2), (key1288, 2), (key1785, 2), (key1565, 2), (key1334, 2), (key1308, 2), (key1769, 2), (key1538, 2), (key1810, 2), (key1652, 2)]

def rawRow11062 : Integer.Sparse Key := [(key1416, -6), (key1614, -6), (key1308, -6), (key1810, -6), (key1416, 2), (key1383, 2), (key1452, 2), (key1565, 2), (key1288, 2), (key1785, 2), (key1538, 2), (key1652, 2), (key1308, 2), (key1810, 2), (key1334, 2), (key1769, 2)]

def rawRow11063 : Integer.Sparse Key := [(key1416, -6), (key1614, -6), (key1810, -6), (key1308, -6), (key1416, 2), (key1452, 2), (key1383, 2), (key1565, 2), (key1785, 2), (key1288, 2), (key1652, 2), (key1538, 2), (key1810, 2), (key1308, 2), (key1769, 2), (key1334, 2)]

def rawRow11064 : Integer.Sparse Key := [(key1416, -6), (key1810, -6), (key1308, -6), (key1614, -6), (key1452, 2), (key1383, 2), (key1416, 2), (key1785, 2), (key1288, 2), (key1565, 2), (key1769, 2), (key1810, 2), (key1334, 2), (key1652, 2), (key1308, 2), (key1538, 2)]

def rawRow11065 : Integer.Sparse Key := [(key1416, -6), (key1810, -6), (key1614, -6), (key1308, -6), (key1452, 2), (key1416, 2), (key1383, 2), (key1785, 2), (key1565, 2), (key1288, 2), (key1810, 2), (key1769, 2), (key1652, 2), (key1334, 2), (key1538, 2), (key1308, 2)]

def rawRow11066 : Integer.Sparse Key := [(key1614, -6), (key1308, -6), (key1416, -6), (key1810, -6), (key1538, 2), (key1565, 2), (key1652, 2), (key1308, 2), (key1416, 2), (key1810, 2), (key1288, 2), (key1334, 2), (key1383, 2), (key1769, 2), (key1452, 2), (key1785, 2)]

def rawRow11067 : Integer.Sparse Key := [(key1614, -6), (key1308, -6), (key1810, -6), (key1416, -6), (key1538, 2), (key1652, 2), (key1565, 2), (key1308, 2), (key1810, 2), (key1416, 2), (key1334, 2), (key1288, 2), (key1769, 2), (key1383, 2), (key1785, 2), (key1452, 2)]

def rawRow11068 : Integer.Sparse Key := [(key1614, -6), (key1416, -6), (key1308, -6), (key1810, -6), (key1565, 2), (key1538, 2), (key1652, 2), (key1416, 2), (key1308, 2), (key1810, 2), (key1383, 2), (key1452, 2), (key1288, 2), (key1785, 2), (key1334, 2), (key1769, 2)]

def rawRow11069 : Integer.Sparse Key := [(key1614, -6), (key1416, -6), (key1810, -6), (key1308, -6), (key1565, 2), (key1652, 2), (key1538, 2), (key1416, 2), (key1810, 2), (key1308, 2), (key1452, 2), (key1383, 2), (key1785, 2), (key1288, 2), (key1769, 2), (key1334, 2)]

def rawRow11070 : Integer.Sparse Key := [(key1614, -6), (key1810, -6), (key1308, -6), (key1416, -6), (key1652, 2), (key1538, 2), (key1565, 2), (key1810, 2), (key1308, 2), (key1416, 2), (key1769, 2), (key1785, 2), (key1334, 2), (key1452, 2), (key1288, 2), (key1383, 2)]

def rawRow11071 : Integer.Sparse Key := [(key1614, -6), (key1810, -6), (key1416, -6), (key1308, -6), (key1652, 2), (key1565, 2), (key1538, 2), (key1810, 2), (key1416, 2), (key1308, 2), (key1785, 2), (key1769, 2), (key1452, 2), (key1334, 2), (key1383, 2), (key1288, 2)]

def rawRow11072 : Integer.Sparse Key := [(key1810, -6), (key1308, -6), (key1416, -6), (key1614, -6), (key1769, 2), (key1785, 2), (key1810, 2), (key1334, 2), (key1452, 2), (key1652, 2), (key1288, 2), (key1308, 2), (key1383, 2), (key1538, 2), (key1416, 2), (key1565, 2)]

def rawRow11073 : Integer.Sparse Key := [(key1810, -6), (key1308, -6), (key1614, -6), (key1416, -6), (key1769, 2), (key1810, 2), (key1785, 2), (key1334, 2), (key1652, 2), (key1452, 2), (key1308, 2), (key1288, 2), (key1538, 2), (key1383, 2), (key1565, 2), (key1416, 2)]

def rawRow11074 : Integer.Sparse Key := [(key1810, -6), (key1416, -6), (key1308, -6), (key1614, -6), (key1785, 2), (key1769, 2), (key1810, 2), (key1452, 2), (key1334, 2), (key1652, 2), (key1383, 2), (key1416, 2), (key1288, 2), (key1565, 2), (key1308, 2), (key1538, 2)]

def rawRow11075 : Integer.Sparse Key := [(key1810, -6), (key1416, -6), (key1614, -6), (key1308, -6), (key1785, 2), (key1810, 2), (key1769, 2), (key1452, 2), (key1652, 2), (key1334, 2), (key1416, 2), (key1383, 2), (key1565, 2), (key1288, 2), (key1538, 2), (key1308, 2)]

def rawRow11076 : Integer.Sparse Key := [(key1810, -6), (key1614, -6), (key1308, -6), (key1416, -6), (key1810, 2), (key1769, 2), (key1785, 2), (key1652, 2), (key1334, 2), (key1452, 2), (key1538, 2), (key1565, 2), (key1308, 2), (key1416, 2), (key1288, 2), (key1383, 2)]

def rawRow11077 : Integer.Sparse Key := [(key1810, -6), (key1614, -6), (key1416, -6), (key1308, -6), (key1810, 2), (key1785, 2), (key1769, 2), (key1652, 2), (key1452, 2), (key1334, 2), (key1565, 2), (key1538, 2), (key1416, 2), (key1308, 2), (key1383, 2), (key1288, 2)]

def rawRow11078 : Integer.Sparse Key := [(key1334, -6), (key1452, -6), (key1652, -6), (key1652, -6), (key1288, 2), (key1308, 2), (key1308, 2), (key1383, 2), (key1538, 2), (key1538, 2), (key1416, 2), (key1416, 2), (key1565, 2), (key1565, 2), (key1614, 2), (key1614, 2)]

def rawRow11079 : Integer.Sparse Key := [(key1334, -6), (key1652, -6), (key1452, -6), (key1652, -6), (key1308, 2), (key1288, 2), (key1308, 2), (key1538, 2), (key1383, 2), (key1538, 2), (key1565, 2), (key1614, 2), (key1416, 2), (key1614, 2), (key1416, 2), (key1565, 2)]

def rawRow11080 : Integer.Sparse Key := [(key1334, -6), (key1652, -6), (key1652, -6), (key1452, -6), (key1308, 2), (key1308, 2), (key1288, 2), (key1538, 2), (key1538, 2), (key1383, 2), (key1614, 2), (key1565, 2), (key1614, 2), (key1416, 2), (key1565, 2), (key1416, 2)]

def rawRow11081 : Integer.Sparse Key := [(key1452, -6), (key1334, -6), (key1652, -6), (key1652, -6), (key1383, 2), (key1416, 2), (key1416, 2), (key1288, 2), (key1565, 2), (key1565, 2), (key1308, 2), (key1308, 2), (key1538, 2), (key1538, 2), (key1614, 2), (key1614, 2)]

def rawRow11082 : Integer.Sparse Key := [(key1452, -6), (key1652, -6), (key1334, -6), (key1652, -6), (key1416, 2), (key1383, 2), (key1416, 2), (key1565, 2), (key1288, 2), (key1565, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1614, 2), (key1308, 2), (key1538, 2)]

def rawRow11083 : Integer.Sparse Key := [(key1452, -6), (key1652, -6), (key1652, -6), (key1334, -6), (key1416, 2), (key1416, 2), (key1383, 2), (key1565, 2), (key1565, 2), (key1288, 2), (key1614, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1538, 2), (key1308, 2)]

def rawRow11084 : Integer.Sparse Key := [(key1652, -6), (key1334, -6), (key1452, -6), (key1652, -6), (key1538, 2), (key1565, 2), (key1614, 2), (key1308, 2), (key1416, 2), (key1614, 2), (key1288, 2), (key1308, 2), (key1383, 2), (key1538, 2), (key1416, 2), (key1565, 2)]

def rawRow11085 : Integer.Sparse Key := [(key1652, -6), (key1334, -6), (key1652, -6), (key1452, -6), (key1538, 2), (key1614, 2), (key1565, 2), (key1308, 2), (key1614, 2), (key1416, 2), (key1308, 2), (key1288, 2), (key1538, 2), (key1383, 2), (key1565, 2), (key1416, 2)]

def rawRow11086 : Integer.Sparse Key := [(key1652, -6), (key1452, -6), (key1334, -6), (key1652, -6), (key1565, 2), (key1538, 2), (key1614, 2), (key1416, 2), (key1308, 2), (key1614, 2), (key1383, 2), (key1416, 2), (key1288, 2), (key1565, 2), (key1308, 2), (key1538, 2)]

def rawRow11087 : Integer.Sparse Key := [(key1652, -6), (key1452, -6), (key1652, -6), (key1334, -6), (key1565, 2), (key1614, 2), (key1538, 2), (key1416, 2), (key1614, 2), (key1308, 2), (key1416, 2), (key1383, 2), (key1565, 2), (key1288, 2), (key1538, 2), (key1308, 2)]

def rawRow11088 : Integer.Sparse Key := [(key1652, -6), (key1652, -6), (key1334, -6), (key1452, -6), (key1614, 2), (key1538, 2), (key1565, 2), (key1614, 2), (key1308, 2), (key1416, 2), (key1538, 2), (key1565, 2), (key1308, 2), (key1416, 2), (key1288, 2), (key1383, 2)]

def rawRow11089 : Integer.Sparse Key := [(key1652, -6), (key1652, -6), (key1452, -6), (key1334, -6), (key1614, 2), (key1565, 2), (key1538, 2), (key1614, 2), (key1416, 2), (key1308, 2), (key1565, 2), (key1538, 2), (key1416, 2), (key1308, 2), (key1383, 2), (key1288, 2)]

def rawRow11090 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

def rawRow11091 : Integer.Sparse Key := [(key2467, 6), (key2464, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2874, -6), (key2842, -6)]

def rawRow11092 : Integer.Sparse Key := [(key2464, 6), (key2476, 6), (key2467, 6), (key2499, 6), (key2586, -6), (key2842, -6), (key2765, -6), (key2874, -6)]

def rawRow11093 : Integer.Sparse Key := [(key2476, 6), (key2464, 6), (key2467, 6), (key2499, 6), (key2586, -6), (key2842, -6), (key2874, -6), (key2765, -6)]

def rawRow11094 : Integer.Sparse Key := [(key2467, 6), (key2476, 6), (key2464, 6), (key2499, 6), (key2586, -6), (key2874, -6), (key2765, -6), (key2842, -6)]

def rawRow11095 : Integer.Sparse Key := [(key2476, 6), (key2467, 6), (key2464, 6), (key2499, 6), (key2586, -6), (key2874, -6), (key2842, -6), (key2765, -6)]

def rawRow11096 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2499, 6), (key2476, 6), (key2765, -6), (key2586, -6), (key2842, -6), (key2874, -6)]

def rawRow11097 : Integer.Sparse Key := [(key2467, 6), (key2464, 6), (key2499, 6), (key2476, 6), (key2765, -6), (key2586, -6), (key2874, -6), (key2842, -6)]

def rawRow11098 : Integer.Sparse Key := [(key2464, 6), (key2499, 6), (key2467, 6), (key2476, 6), (key2765, -6), (key2842, -6), (key2586, -6), (key2874, -6)]

def rawRow11099 : Integer.Sparse Key := [(key2499, 6), (key2464, 6), (key2467, 6), (key2476, 6), (key2765, -6), (key2842, -6), (key2874, -6), (key2586, -6)]

def rawRow11100 : Integer.Sparse Key := [(key2467, 6), (key2499, 6), (key2464, 6), (key2476, 6), (key2765, -6), (key2874, -6), (key2586, -6), (key2842, -6)]

def rawRow11101 : Integer.Sparse Key := [(key2499, 6), (key2467, 6), (key2464, 6), (key2476, 6), (key2765, -6), (key2874, -6), (key2842, -6), (key2586, -6)]

def rawRow11102 : Integer.Sparse Key := [(key2464, 6), (key2476, 6), (key2499, 6), (key2467, 6), (key2842, -6), (key2586, -6), (key2765, -6), (key2874, -6)]

def rawRow11103 : Integer.Sparse Key := [(key2476, 6), (key2464, 6), (key2499, 6), (key2467, 6), (key2842, -6), (key2586, -6), (key2874, -6), (key2765, -6)]

def rawRow11104 : Integer.Sparse Key := [(key2464, 6), (key2499, 6), (key2476, 6), (key2467, 6), (key2842, -6), (key2765, -6), (key2586, -6), (key2874, -6)]

def rawRow11105 : Integer.Sparse Key := [(key2499, 6), (key2464, 6), (key2476, 6), (key2467, 6), (key2842, -6), (key2765, -6), (key2874, -6), (key2586, -6)]

def rawRow11106 : Integer.Sparse Key := [(key2476, 6), (key2499, 6), (key2464, 6), (key2467, 6), (key2842, -6), (key2874, -6), (key2586, -6), (key2765, -6)]

def rawRow11107 : Integer.Sparse Key := [(key2499, 6), (key2476, 6), (key2464, 6), (key2467, 6), (key2842, -6), (key2874, -6), (key2765, -6), (key2586, -6)]

def rawRow11108 : Integer.Sparse Key := [(key2467, 6), (key2476, 6), (key2499, 6), (key2464, 6), (key2874, -6), (key2586, -6), (key2765, -6), (key2842, -6)]

def rawRow11109 : Integer.Sparse Key := [(key2476, 6), (key2467, 6), (key2499, 6), (key2464, 6), (key2874, -6), (key2586, -6), (key2842, -6), (key2765, -6)]

def rawRow11110 : Integer.Sparse Key := [(key2467, 6), (key2499, 6), (key2476, 6), (key2464, 6), (key2874, -6), (key2765, -6), (key2586, -6), (key2842, -6)]

def rawRow11111 : Integer.Sparse Key := [(key2499, 6), (key2467, 6), (key2476, 6), (key2464, 6), (key2874, -6), (key2765, -6), (key2842, -6), (key2586, -6)]

def rawRow11112 : Integer.Sparse Key := [(key2476, 6), (key2499, 6), (key2467, 6), (key2464, 6), (key2874, -6), (key2842, -6), (key2586, -6), (key2765, -6)]

def rawRow11113 : Integer.Sparse Key := [(key2499, 6), (key2476, 6), (key2467, 6), (key2464, 6), (key2874, -6), (key2842, -6), (key2765, -6), (key2586, -6)]

def rawRow11114 : Integer.Sparse Key := [(key2534, 6), (key2534, 6), (key2540, 6), (key2551, 6), (key2370, -6), (key2762, -6), (key2839, -6), (key2839, -6)]

def rawRow11115 : Integer.Sparse Key := [(key2534, 6), (key2540, 6), (key2534, 6), (key2551, 6), (key2370, -6), (key2839, -6), (key2762, -6), (key2839, -6)]

def rawRow11116 : Integer.Sparse Key := [(key2540, 6), (key2534, 6), (key2534, 6), (key2551, 6), (key2370, -6), (key2839, -6), (key2839, -6), (key2762, -6)]

def rawRow11117 : Integer.Sparse Key := [(key2534, 6), (key2534, 6), (key2551, 6), (key2540, 6), (key2398, -6), (key2583, -6), (key2839, -6), (key2839, -6)]

def rawRow11118 : Integer.Sparse Key := [(key2534, 6), (key2551, 6), (key2534, 6), (key2540, 6), (key2398, -6), (key2839, -6), (key2583, -6), (key2839, -6)]

def rawRow11119 : Integer.Sparse Key := [(key2551, 6), (key2534, 6), (key2534, 6), (key2540, 6), (key2398, -6), (key2839, -6), (key2839, -6), (key2583, -6)]

def rawRow11120 : Integer.Sparse Key := [(key2534, 6), (key2540, 6), (key2551, 6), (key2534, 6), (key2464, -6), (key2370, -6), (key2762, -6), (key2839, -6)]

def rawRow11121 : Integer.Sparse Key := [(key2540, 6), (key2534, 6), (key2551, 6), (key2534, 6), (key2464, -6), (key2370, -6), (key2839, -6), (key2762, -6)]

def rawRow11122 : Integer.Sparse Key := [(key2534, 6), (key2551, 6), (key2540, 6), (key2534, 6), (key2464, -6), (key2398, -6), (key2583, -6), (key2839, -6)]

def rawRow11123 : Integer.Sparse Key := [(key2551, 6), (key2534, 6), (key2540, 6), (key2534, 6), (key2464, -6), (key2398, -6), (key2839, -6), (key2583, -6)]

def rawRow11124 : Integer.Sparse Key := [(key2540, 6), (key2551, 6), (key2534, 6), (key2534, 6), (key2464, -6), (key2464, -6), (key2370, -6), (key2762, -6)]

def rawRow11125 : Integer.Sparse Key := [(key2551, 6), (key2540, 6), (key2534, 6), (key2534, 6), (key2464, -6), (key2464, -6), (key2398, -6), (key2583, -6)]

def rawRow11126 : Integer.Sparse Key := [(key2465, 6), (key2469, 6), (key2477, 6), (key2500, 6), (key2375, -6), (key2403, -6), (key2469, -6), (key2536, -6)]

def rawRow11127 : Integer.Sparse Key := [(key2469, 6), (key2465, 6), (key2477, 6), (key2500, 6), (key2375, -6), (key2403, -6), (key2536, -6), (key2469, -6)]

def rawRow11128 : Integer.Sparse Key := [(key2465, 6), (key2477, 6), (key2469, 6), (key2500, 6), (key2375, -6), (key2469, -6), (key2403, -6), (key2536, -6)]

def rawRow11129 : Integer.Sparse Key := [(key2477, 6), (key2465, 6), (key2469, 6), (key2500, 6), (key2375, -6), (key2469, -6), (key2536, -6), (key2403, -6)]

def rawRow11130 : Integer.Sparse Key := [(key2469, 6), (key2477, 6), (key2465, 6), (key2500, 6), (key2375, -6), (key2536, -6), (key2403, -6), (key2469, -6)]

def rawRow11131 : Integer.Sparse Key := [(key2477, 6), (key2469, 6), (key2465, 6), (key2500, 6), (key2375, -6), (key2536, -6), (key2469, -6), (key2403, -6)]

def rawRow11132 : Integer.Sparse Key := [(key2465, 6), (key2469, 6), (key2500, 6), (key2477, 6), (key2403, -6), (key2375, -6), (key2469, -6), (key2536, -6)]

def rawRow11133 : Integer.Sparse Key := [(key2469, 6), (key2465, 6), (key2500, 6), (key2477, 6), (key2403, -6), (key2375, -6), (key2536, -6), (key2469, -6)]

def rawRow11134 : Integer.Sparse Key := [(key2465, 6), (key2500, 6), (key2469, 6), (key2477, 6), (key2403, -6), (key2469, -6), (key2375, -6), (key2536, -6)]

def rawRow11135 : Integer.Sparse Key := [(key2500, 6), (key2465, 6), (key2469, 6), (key2477, 6), (key2403, -6), (key2469, -6), (key2536, -6), (key2375, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11136 : Integer.Sparse Key := [(key2469, 6), (key2500, 6), (key2465, 6), (key2477, 6), (key2403, -6), (key2536, -6), (key2375, -6), (key2469, -6)]

def rawRow11137 : Integer.Sparse Key := [(key2500, 6), (key2469, 6), (key2465, 6), (key2477, 6), (key2403, -6), (key2536, -6), (key2469, -6), (key2375, -6)]

def rawRow11138 : Integer.Sparse Key := [(key2465, 6), (key2477, 6), (key2500, 6), (key2469, 6), (key2469, -6), (key2375, -6), (key2403, -6), (key2536, -6)]

def rawRow11139 : Integer.Sparse Key := [(key2477, 6), (key2465, 6), (key2500, 6), (key2469, 6), (key2469, -6), (key2375, -6), (key2536, -6), (key2403, -6)]

def rawRow11140 : Integer.Sparse Key := [(key2465, 6), (key2500, 6), (key2477, 6), (key2469, 6), (key2469, -6), (key2403, -6), (key2375, -6), (key2536, -6)]

def rawRow11141 : Integer.Sparse Key := [(key2500, 6), (key2465, 6), (key2477, 6), (key2469, 6), (key2469, -6), (key2403, -6), (key2536, -6), (key2375, -6)]

def rawRow11142 : Integer.Sparse Key := [(key2477, 6), (key2500, 6), (key2465, 6), (key2469, 6), (key2469, -6), (key2536, -6), (key2375, -6), (key2403, -6)]

def rawRow11143 : Integer.Sparse Key := [(key2500, 6), (key2477, 6), (key2465, 6), (key2469, 6), (key2469, -6), (key2536, -6), (key2403, -6), (key2375, -6)]

def rawRow11144 : Integer.Sparse Key := [(key2469, 6), (key2477, 6), (key2500, 6), (key2465, 6), (key2536, -6), (key2375, -6), (key2403, -6), (key2469, -6)]

def rawRow11145 : Integer.Sparse Key := [(key2477, 6), (key2469, 6), (key2500, 6), (key2465, 6), (key2536, -6), (key2375, -6), (key2469, -6), (key2403, -6)]

def rawRow11146 : Integer.Sparse Key := [(key2469, 6), (key2500, 6), (key2477, 6), (key2465, 6), (key2536, -6), (key2403, -6), (key2375, -6), (key2469, -6)]

def rawRow11147 : Integer.Sparse Key := [(key2500, 6), (key2469, 6), (key2477, 6), (key2465, 6), (key2536, -6), (key2403, -6), (key2469, -6), (key2375, -6)]

def rawRow11148 : Integer.Sparse Key := [(key2477, 6), (key2500, 6), (key2469, 6), (key2465, 6), (key2536, -6), (key2469, -6), (key2375, -6), (key2403, -6)]

def rawRow11149 : Integer.Sparse Key := [(key2500, 6), (key2477, 6), (key2469, 6), (key2465, 6), (key2536, -6), (key2469, -6), (key2403, -6), (key2375, -6)]

def rawRow11150 : Integer.Sparse Key := [(key2536, 6), (key2536, 6), (key2541, 6), (key2552, 6), (key2371, -6), (key2399, -6), (key2465, -6), (key2465, -6)]

def rawRow11151 : Integer.Sparse Key := [(key2536, 6), (key2541, 6), (key2536, 6), (key2552, 6), (key2371, -6), (key2465, -6), (key2399, -6), (key2465, -6)]

def rawRow11152 : Integer.Sparse Key := [(key2541, 6), (key2536, 6), (key2536, 6), (key2552, 6), (key2371, -6), (key2465, -6), (key2465, -6), (key2399, -6)]

def rawRow11153 : Integer.Sparse Key := [(key2536, 6), (key2536, 6), (key2552, 6), (key2541, 6), (key2399, -6), (key2371, -6), (key2465, -6), (key2465, -6)]

def rawRow11154 : Integer.Sparse Key := [(key2536, 6), (key2552, 6), (key2536, 6), (key2541, 6), (key2399, -6), (key2465, -6), (key2371, -6), (key2465, -6)]

def rawRow11155 : Integer.Sparse Key := [(key2552, 6), (key2536, 6), (key2536, 6), (key2541, 6), (key2399, -6), (key2465, -6), (key2465, -6), (key2371, -6)]

def rawRow11156 : Integer.Sparse Key := [(key2536, 6), (key2541, 6), (key2552, 6), (key2536, 6), (key2465, -6), (key2371, -6), (key2399, -6), (key2465, -6)]

def rawRow11157 : Integer.Sparse Key := [(key2541, 6), (key2536, 6), (key2552, 6), (key2536, 6), (key2465, -6), (key2371, -6), (key2465, -6), (key2399, -6)]

def rawRow11158 : Integer.Sparse Key := [(key2536, 6), (key2552, 6), (key2541, 6), (key2536, 6), (key2465, -6), (key2399, -6), (key2371, -6), (key2465, -6)]

def rawRow11159 : Integer.Sparse Key := [(key2552, 6), (key2536, 6), (key2541, 6), (key2536, 6), (key2465, -6), (key2399, -6), (key2465, -6), (key2371, -6)]

def rawRow11160 : Integer.Sparse Key := [(key2541, 6), (key2552, 6), (key2536, 6), (key2536, 6), (key2465, -6), (key2465, -6), (key2371, -6), (key2399, -6)]

def rawRow11161 : Integer.Sparse Key := [(key2552, 6), (key2541, 6), (key2536, 6), (key2536, 6), (key2465, -6), (key2465, -6), (key2399, -6), (key2371, -6)]

def rawRow11162 : Integer.Sparse Key := [(key2302, -6), (key2303, -6), (key2305, -6), (key2310, -6), (key2091, 2), (key2092, 2), (key2095, 2), (key2193, 2), (key2194, 2), (key2302, 2), (key2341, 2), (key2305, 2), (key2343, 2), (key2200, 2), (key2310, 2), (key2347, 2)]

def rawRow11163 : Integer.Sparse Key := [(key2303, -6), (key2302, -6), (key2305, -6), (key2310, -6), (key2092, 2), (key2091, 2), (key2095, 2), (key2194, 2), (key2193, 2), (key2341, 2), (key2302, 2), (key2343, 2), (key2305, 2), (key2200, 2), (key2347, 2), (key2310, 2)]

def rawRow11164 : Integer.Sparse Key := [(key2302, -6), (key2305, -6), (key2303, -6), (key2310, -6), (key2091, 2), (key2095, 2), (key2092, 2), (key2302, 2), (key2305, 2), (key2193, 2), (key2343, 2), (key2194, 2), (key2341, 2), (key2310, 2), (key2200, 2), (key2347, 2)]

def rawRow11165 : Integer.Sparse Key := [(key2305, -6), (key2302, -6), (key2303, -6), (key2310, -6), (key2095, 2), (key2091, 2), (key2092, 2), (key2305, 2), (key2302, 2), (key2343, 2), (key2193, 2), (key2341, 2), (key2194, 2), (key2310, 2), (key2347, 2), (key2200, 2)]

def rawRow11166 : Integer.Sparse Key := [(key2303, -6), (key2305, -6), (key2302, -6), (key2310, -6), (key2092, 2), (key2095, 2), (key2091, 2), (key2341, 2), (key2343, 2), (key2194, 2), (key2305, 2), (key2193, 2), (key2302, 2), (key2347, 2), (key2200, 2), (key2310, 2)]

def rawRow11167 : Integer.Sparse Key := [(key2305, -6), (key2303, -6), (key2302, -6), (key2310, -6), (key2095, 2), (key2092, 2), (key2091, 2), (key2343, 2), (key2341, 2), (key2305, 2), (key2194, 2), (key2302, 2), (key2193, 2), (key2347, 2), (key2310, 2), (key2200, 2)]

def rawRow11168 : Integer.Sparse Key := [(key2302, -6), (key2303, -6), (key2310, -6), (key2305, -6), (key2193, 2), (key2194, 2), (key2200, 2), (key2091, 2), (key2092, 2), (key2302, 2), (key2341, 2), (key2310, 2), (key2347, 2), (key2095, 2), (key2305, 2), (key2343, 2)]

def rawRow11169 : Integer.Sparse Key := [(key2303, -6), (key2302, -6), (key2310, -6), (key2305, -6), (key2194, 2), (key2193, 2), (key2200, 2), (key2092, 2), (key2091, 2), (key2341, 2), (key2302, 2), (key2347, 2), (key2310, 2), (key2095, 2), (key2343, 2), (key2305, 2)]

def rawRow11170 : Integer.Sparse Key := [(key2302, -6), (key2310, -6), (key2303, -6), (key2305, -6), (key2193, 2), (key2200, 2), (key2194, 2), (key2302, 2), (key2310, 2), (key2091, 2), (key2347, 2), (key2092, 2), (key2341, 2), (key2305, 2), (key2095, 2), (key2343, 2)]

def rawRow11171 : Integer.Sparse Key := [(key2310, -6), (key2302, -6), (key2303, -6), (key2305, -6), (key2200, 2), (key2193, 2), (key2194, 2), (key2310, 2), (key2302, 2), (key2347, 2), (key2091, 2), (key2341, 2), (key2092, 2), (key2305, 2), (key2343, 2), (key2095, 2)]

def rawRow11172 : Integer.Sparse Key := [(key2303, -6), (key2310, -6), (key2302, -6), (key2305, -6), (key2194, 2), (key2200, 2), (key2193, 2), (key2341, 2), (key2347, 2), (key2092, 2), (key2310, 2), (key2091, 2), (key2302, 2), (key2343, 2), (key2095, 2), (key2305, 2)]

def rawRow11173 : Integer.Sparse Key := [(key2310, -6), (key2303, -6), (key2302, -6), (key2305, -6), (key2200, 2), (key2194, 2), (key2193, 2), (key2347, 2), (key2341, 2), (key2310, 2), (key2092, 2), (key2302, 2), (key2091, 2), (key2343, 2), (key2305, 2), (key2095, 2)]

def rawRow11174 : Integer.Sparse Key := [(key2302, -6), (key2305, -6), (key2310, -6), (key2303, -6), (key2302, 2), (key2305, 2), (key2310, 2), (key2091, 2), (key2095, 2), (key2193, 2), (key2343, 2), (key2200, 2), (key2347, 2), (key2092, 2), (key2194, 2), (key2341, 2)]

def rawRow11175 : Integer.Sparse Key := [(key2305, -6), (key2302, -6), (key2310, -6), (key2303, -6), (key2305, 2), (key2302, 2), (key2310, 2), (key2095, 2), (key2091, 2), (key2343, 2), (key2193, 2), (key2347, 2), (key2200, 2), (key2092, 2), (key2341, 2), (key2194, 2)]

def rawRow11176 : Integer.Sparse Key := [(key2302, -6), (key2310, -6), (key2305, -6), (key2303, -6), (key2302, 2), (key2310, 2), (key2305, 2), (key2193, 2), (key2200, 2), (key2091, 2), (key2347, 2), (key2095, 2), (key2343, 2), (key2194, 2), (key2092, 2), (key2341, 2)]

def rawRow11177 : Integer.Sparse Key := [(key2310, -6), (key2302, -6), (key2305, -6), (key2303, -6), (key2310, 2), (key2302, 2), (key2305, 2), (key2200, 2), (key2193, 2), (key2347, 2), (key2091, 2), (key2343, 2), (key2095, 2), (key2194, 2), (key2341, 2), (key2092, 2)]

def rawRow11178 : Integer.Sparse Key := [(key2305, -6), (key2310, -6), (key2302, -6), (key2303, -6), (key2305, 2), (key2310, 2), (key2302, 2), (key2343, 2), (key2347, 2), (key2095, 2), (key2200, 2), (key2091, 2), (key2193, 2), (key2341, 2), (key2092, 2), (key2194, 2)]

def rawRow11179 : Integer.Sparse Key := [(key2310, -6), (key2305, -6), (key2302, -6), (key2303, -6), (key2310, 2), (key2305, 2), (key2302, 2), (key2347, 2), (key2343, 2), (key2200, 2), (key2095, 2), (key2193, 2), (key2091, 2), (key2341, 2), (key2194, 2), (key2092, 2)]

def rawRow11180 : Integer.Sparse Key := [(key2303, -6), (key2305, -6), (key2310, -6), (key2302, -6), (key2341, 2), (key2343, 2), (key2347, 2), (key2092, 2), (key2095, 2), (key2194, 2), (key2305, 2), (key2200, 2), (key2310, 2), (key2091, 2), (key2193, 2), (key2302, 2)]

def rawRow11181 : Integer.Sparse Key := [(key2305, -6), (key2303, -6), (key2310, -6), (key2302, -6), (key2343, 2), (key2341, 2), (key2347, 2), (key2095, 2), (key2092, 2), (key2305, 2), (key2194, 2), (key2310, 2), (key2200, 2), (key2091, 2), (key2302, 2), (key2193, 2)]

def rawRow11182 : Integer.Sparse Key := [(key2303, -6), (key2310, -6), (key2305, -6), (key2302, -6), (key2341, 2), (key2347, 2), (key2343, 2), (key2194, 2), (key2200, 2), (key2092, 2), (key2310, 2), (key2095, 2), (key2305, 2), (key2193, 2), (key2091, 2), (key2302, 2)]

def rawRow11183 : Integer.Sparse Key := [(key2310, -6), (key2303, -6), (key2305, -6), (key2302, -6), (key2347, 2), (key2341, 2), (key2343, 2), (key2200, 2), (key2194, 2), (key2310, 2), (key2092, 2), (key2305, 2), (key2095, 2), (key2193, 2), (key2302, 2), (key2091, 2)]

def rawRow11184 : Integer.Sparse Key := [(key2305, -6), (key2310, -6), (key2303, -6), (key2302, -6), (key2343, 2), (key2347, 2), (key2341, 2), (key2305, 2), (key2310, 2), (key2095, 2), (key2200, 2), (key2092, 2), (key2194, 2), (key2302, 2), (key2091, 2), (key2193, 2)]

def rawRow11185 : Integer.Sparse Key := [(key2310, -6), (key2305, -6), (key2303, -6), (key2302, -6), (key2347, 2), (key2343, 2), (key2341, 2), (key2310, 2), (key2305, 2), (key2200, 2), (key2095, 2), (key2194, 2), (key2092, 2), (key2302, 2), (key2193, 2), (key2091, 2)]

def rawRow11186 : Integer.Sparse Key := [(key2341, -6), (key2341, -6), (key2343, -6), (key2347, -6), (key2092, 2), (key2092, 2), (key2095, 2), (key2194, 2), (key2194, 2), (key2303, 2), (key2303, 2), (key2305, 2), (key2305, 2), (key2200, 2), (key2310, 2), (key2310, 2)]

def rawRow11187 : Integer.Sparse Key := [(key2341, -6), (key2343, -6), (key2341, -6), (key2347, -6), (key2092, 2), (key2095, 2), (key2092, 2), (key2303, 2), (key2305, 2), (key2194, 2), (key2305, 2), (key2194, 2), (key2303, 2), (key2310, 2), (key2200, 2), (key2310, 2)]

def rawRow11188 : Integer.Sparse Key := [(key2343, -6), (key2341, -6), (key2341, -6), (key2347, -6), (key2095, 2), (key2092, 2), (key2092, 2), (key2305, 2), (key2303, 2), (key2305, 2), (key2194, 2), (key2303, 2), (key2194, 2), (key2310, 2), (key2310, 2), (key2200, 2)]

def rawRow11189 : Integer.Sparse Key := [(key2341, -6), (key2341, -6), (key2347, -6), (key2343, -6), (key2194, 2), (key2194, 2), (key2200, 2), (key2092, 2), (key2092, 2), (key2303, 2), (key2303, 2), (key2310, 2), (key2310, 2), (key2095, 2), (key2305, 2), (key2305, 2)]

def rawRow11190 : Integer.Sparse Key := [(key2341, -6), (key2347, -6), (key2341, -6), (key2343, -6), (key2194, 2), (key2200, 2), (key2194, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2305, 2), (key2095, 2), (key2305, 2)]

def rawRow11191 : Integer.Sparse Key := [(key2347, -6), (key2341, -6), (key2341, -6), (key2343, -6), (key2200, 2), (key2194, 2), (key2194, 2), (key2310, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2092, 2), (key2305, 2), (key2305, 2), (key2095, 2)]

def rawRow11192 : Integer.Sparse Key := [(key2341, -6), (key2343, -6), (key2347, -6), (key2341, -6), (key2303, 2), (key2305, 2), (key2310, 2), (key2092, 2), (key2095, 2), (key2194, 2), (key2305, 2), (key2200, 2), (key2310, 2), (key2092, 2), (key2194, 2), (key2303, 2)]

def rawRow11193 : Integer.Sparse Key := [(key2343, -6), (key2341, -6), (key2347, -6), (key2341, -6), (key2305, 2), (key2303, 2), (key2310, 2), (key2095, 2), (key2092, 2), (key2305, 2), (key2194, 2), (key2310, 2), (key2200, 2), (key2092, 2), (key2303, 2), (key2194, 2)]

def rawRow11194 : Integer.Sparse Key := [(key2341, -6), (key2347, -6), (key2343, -6), (key2341, -6), (key2303, 2), (key2310, 2), (key2305, 2), (key2194, 2), (key2200, 2), (key2092, 2), (key2310, 2), (key2095, 2), (key2305, 2), (key2194, 2), (key2092, 2), (key2303, 2)]

def rawRow11195 : Integer.Sparse Key := [(key2347, -6), (key2341, -6), (key2343, -6), (key2341, -6), (key2310, 2), (key2303, 2), (key2305, 2), (key2200, 2), (key2194, 2), (key2310, 2), (key2092, 2), (key2305, 2), (key2095, 2), (key2194, 2), (key2303, 2), (key2092, 2)]

def rawRow11196 : Integer.Sparse Key := [(key2343, -6), (key2347, -6), (key2341, -6), (key2341, -6), (key2305, 2), (key2310, 2), (key2303, 2), (key2305, 2), (key2310, 2), (key2095, 2), (key2200, 2), (key2092, 2), (key2194, 2), (key2303, 2), (key2092, 2), (key2194, 2)]

def rawRow11197 : Integer.Sparse Key := [(key2347, -6), (key2343, -6), (key2341, -6), (key2341, -6), (key2310, 2), (key2305, 2), (key2303, 2), (key2310, 2), (key2305, 2), (key2200, 2), (key2095, 2), (key2194, 2), (key2092, 2), (key2303, 2), (key2194, 2), (key2092, 2)]

def rawRow11198 : Integer.Sparse Key := [(key1107, 6), (key1112, 6), (key1121, 6), (key1148, 6), (key999, -6), (key1034, -6), (key1112, -6), (key1191, -6)]

def rawRow11199 : Integer.Sparse Key := [(key1112, 6), (key1107, 6), (key1121, 6), (key1148, 6), (key999, -6), (key1034, -6), (key1191, -6), (key1112, -6)]

def rawRow11200 : Integer.Sparse Key := [(key1107, 6), (key1121, 6), (key1112, 6), (key1148, 6), (key999, -6), (key1112, -6), (key1034, -6), (key1191, -6)]

def rawRow11201 : Integer.Sparse Key := [(key1121, 6), (key1107, 6), (key1112, 6), (key1148, 6), (key999, -6), (key1112, -6), (key1191, -6), (key1034, -6)]

def rawRow11202 : Integer.Sparse Key := [(key1112, 6), (key1121, 6), (key1107, 6), (key1148, 6), (key999, -6), (key1191, -6), (key1034, -6), (key1112, -6)]

def rawRow11203 : Integer.Sparse Key := [(key1121, 6), (key1112, 6), (key1107, 6), (key1148, 6), (key999, -6), (key1191, -6), (key1112, -6), (key1034, -6)]

def rawRow11204 : Integer.Sparse Key := [(key1107, 6), (key1112, 6), (key1148, 6), (key1121, 6), (key1034, -6), (key999, -6), (key1112, -6), (key1191, -6)]

def rawRow11205 : Integer.Sparse Key := [(key1112, 6), (key1107, 6), (key1148, 6), (key1121, 6), (key1034, -6), (key999, -6), (key1191, -6), (key1112, -6)]

def rawRow11206 : Integer.Sparse Key := [(key1107, 6), (key1148, 6), (key1112, 6), (key1121, 6), (key1034, -6), (key1112, -6), (key999, -6), (key1191, -6)]

def rawRow11207 : Integer.Sparse Key := [(key1148, 6), (key1107, 6), (key1112, 6), (key1121, 6), (key1034, -6), (key1112, -6), (key1191, -6), (key999, -6)]

def rawRow11208 : Integer.Sparse Key := [(key1112, 6), (key1148, 6), (key1107, 6), (key1121, 6), (key1034, -6), (key1191, -6), (key999, -6), (key1112, -6)]

def rawRow11209 : Integer.Sparse Key := [(key1148, 6), (key1112, 6), (key1107, 6), (key1121, 6), (key1034, -6), (key1191, -6), (key1112, -6), (key999, -6)]

def rawRow11210 : Integer.Sparse Key := [(key1107, 6), (key1121, 6), (key1148, 6), (key1112, 6), (key1112, -6), (key999, -6), (key1034, -6), (key1191, -6)]

def rawRow11211 : Integer.Sparse Key := [(key1121, 6), (key1107, 6), (key1148, 6), (key1112, 6), (key1112, -6), (key999, -6), (key1191, -6), (key1034, -6)]

def rawRow11212 : Integer.Sparse Key := [(key1107, 6), (key1148, 6), (key1121, 6), (key1112, 6), (key1112, -6), (key1034, -6), (key999, -6), (key1191, -6)]

def rawRow11213 : Integer.Sparse Key := [(key1148, 6), (key1107, 6), (key1121, 6), (key1112, 6), (key1112, -6), (key1034, -6), (key1191, -6), (key999, -6)]

def rawRow11214 : Integer.Sparse Key := [(key1121, 6), (key1148, 6), (key1107, 6), (key1112, 6), (key1112, -6), (key1191, -6), (key999, -6), (key1034, -6)]

def rawRow11215 : Integer.Sparse Key := [(key1148, 6), (key1121, 6), (key1107, 6), (key1112, 6), (key1112, -6), (key1191, -6), (key1034, -6), (key999, -6)]

def rawRow11216 : Integer.Sparse Key := [(key1112, 6), (key1121, 6), (key1148, 6), (key1107, 6), (key1191, -6), (key999, -6), (key1034, -6), (key1112, -6)]

def rawRow11217 : Integer.Sparse Key := [(key1121, 6), (key1112, 6), (key1148, 6), (key1107, 6), (key1191, -6), (key999, -6), (key1112, -6), (key1034, -6)]

def rawRow11218 : Integer.Sparse Key := [(key1112, 6), (key1148, 6), (key1121, 6), (key1107, 6), (key1191, -6), (key1034, -6), (key999, -6), (key1112, -6)]

def rawRow11219 : Integer.Sparse Key := [(key1148, 6), (key1112, 6), (key1121, 6), (key1107, 6), (key1191, -6), (key1034, -6), (key1112, -6), (key999, -6)]

def rawRow11220 : Integer.Sparse Key := [(key1121, 6), (key1148, 6), (key1112, 6), (key1107, 6), (key1191, -6), (key1112, -6), (key999, -6), (key1034, -6)]

def rawRow11221 : Integer.Sparse Key := [(key1148, 6), (key1121, 6), (key1112, 6), (key1107, 6), (key1191, -6), (key1112, -6), (key1034, -6), (key999, -6)]

def rawRow11222 : Integer.Sparse Key := [(key1191, 6), (key1191, 6), (key1197, 6), (key1210, 6), (key994, -6), (key1029, -6), (key1107, -6), (key1107, -6)]

def rawRow11223 : Integer.Sparse Key := [(key1191, 6), (key1197, 6), (key1191, 6), (key1210, 6), (key994, -6), (key1107, -6), (key1029, -6), (key1107, -6)]

def rawRow11224 : Integer.Sparse Key := [(key1197, 6), (key1191, 6), (key1191, 6), (key1210, 6), (key994, -6), (key1107, -6), (key1107, -6), (key1029, -6)]

def rawRow11225 : Integer.Sparse Key := [(key1191, 6), (key1191, 6), (key1210, 6), (key1197, 6), (key1029, -6), (key994, -6), (key1107, -6), (key1107, -6)]

def rawRow11226 : Integer.Sparse Key := [(key1191, 6), (key1210, 6), (key1191, 6), (key1197, 6), (key1029, -6), (key1107, -6), (key994, -6), (key1107, -6)]

def rawRow11227 : Integer.Sparse Key := [(key1210, 6), (key1191, 6), (key1191, 6), (key1197, 6), (key1029, -6), (key1107, -6), (key1107, -6), (key994, -6)]

def rawRow11228 : Integer.Sparse Key := [(key1191, 6), (key1197, 6), (key1210, 6), (key1191, 6), (key1107, -6), (key994, -6), (key1029, -6), (key1107, -6)]

def rawRow11229 : Integer.Sparse Key := [(key1197, 6), (key1191, 6), (key1210, 6), (key1191, 6), (key1107, -6), (key994, -6), (key1107, -6), (key1029, -6)]

def rawRow11230 : Integer.Sparse Key := [(key1191, 6), (key1210, 6), (key1197, 6), (key1191, 6), (key1107, -6), (key1029, -6), (key994, -6), (key1107, -6)]

def rawRow11231 : Integer.Sparse Key := [(key1210, 6), (key1191, 6), (key1197, 6), (key1191, 6), (key1107, -6), (key1029, -6), (key1107, -6), (key994, -6)]

def rawRow11232 : Integer.Sparse Key := [(key1197, 6), (key1210, 6), (key1191, 6), (key1191, 6), (key1107, -6), (key1107, -6), (key994, -6), (key1029, -6)]

def rawRow11233 : Integer.Sparse Key := [(key1210, 6), (key1197, 6), (key1191, 6), (key1191, 6), (key1107, -6), (key1107, -6), (key1029, -6), (key994, -6)]

def rawRow11234 : Integer.Sparse Key := [(key2464, -6), (key2467, -6), (key2476, -6), (key2499, -6), (key2370, 2), (key2373, 2), (key2386, 2), (key2762, 2), (key2765, 2), (key2839, 2), (key2874, 2), (key2886, 2), (key2908, 2), (key2928, 2), (key2965, 2), (key2987, 2)]

def rawRow11235 : Integer.Sparse Key := [(key2467, -6), (key2464, -6), (key2476, -6), (key2499, -6), (key2373, 2), (key2370, 2), (key2386, 2), (key2765, 2), (key2762, 2), (key2874, 2), (key2839, 2), (key2908, 2), (key2886, 2), (key2928, 2), (key2987, 2), (key2965, 2)]

def rawRow11236 : Integer.Sparse Key := [(key2464, -6), (key2476, -6), (key2467, -6), (key2499, -6), (key2370, 2), (key2386, 2), (key2373, 2), (key2839, 2), (key2886, 2), (key2762, 2), (key2908, 2), (key2765, 2), (key2874, 2), (key2965, 2), (key2928, 2), (key2987, 2)]

def rawRow11237 : Integer.Sparse Key := [(key2476, -6), (key2464, -6), (key2467, -6), (key2499, -6), (key2386, 2), (key2370, 2), (key2373, 2), (key2886, 2), (key2839, 2), (key2908, 2), (key2762, 2), (key2874, 2), (key2765, 2), (key2965, 2), (key2987, 2), (key2928, 2)]

def rawRow11238 : Integer.Sparse Key := [(key2467, -6), (key2476, -6), (key2464, -6), (key2499, -6), (key2373, 2), (key2386, 2), (key2370, 2), (key2874, 2), (key2908, 2), (key2765, 2), (key2886, 2), (key2762, 2), (key2839, 2), (key2987, 2), (key2928, 2), (key2965, 2)]

def rawRow11239 : Integer.Sparse Key := [(key2476, -6), (key2467, -6), (key2464, -6), (key2499, -6), (key2386, 2), (key2373, 2), (key2370, 2), (key2908, 2), (key2874, 2), (key2886, 2), (key2765, 2), (key2839, 2), (key2762, 2), (key2987, 2), (key2965, 2), (key2928, 2)]

def rawRow11240 : Integer.Sparse Key := [(key2464, -6), (key2467, -6), (key2499, -6), (key2476, -6), (key2398, 2), (key2401, 2), (key2433, 2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2597, 2), (key2886, 2), (key2908, 2)]

def rawRow11241 : Integer.Sparse Key := [(key2467, -6), (key2464, -6), (key2499, -6), (key2476, -6), (key2401, 2), (key2398, 2), (key2433, 2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2597, 2), (key2908, 2), (key2886, 2)]

def rawRow11242 : Integer.Sparse Key := [(key2464, -6), (key2499, -6), (key2467, -6), (key2476, -6), (key2398, 2), (key2433, 2), (key2401, 2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2886, 2), (key2597, 2), (key2908, 2)]

def rawRow11243 : Integer.Sparse Key := [(key2499, -6), (key2464, -6), (key2467, -6), (key2476, -6), (key2433, 2), (key2398, 2), (key2401, 2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2886, 2), (key2908, 2), (key2597, 2)]

def rawRow11244 : Integer.Sparse Key := [(key2467, -6), (key2499, -6), (key2464, -6), (key2476, -6), (key2401, 2), (key2433, 2), (key2398, 2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2908, 2), (key2597, 2), (key2886, 2)]

def rawRow11245 : Integer.Sparse Key := [(key2499, -6), (key2467, -6), (key2464, -6), (key2476, -6), (key2433, 2), (key2401, 2), (key2398, 2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2908, 2), (key2886, 2), (key2597, 2)]

def rawRow11246 : Integer.Sparse Key := [(key2464, -6), (key2476, -6), (key2499, -6), (key2467, -6), (key2464, 2), (key2476, 2), (key2499, 2), (key2370, 2), (key2386, 2), (key2762, 2), (key2908, 2), (key2928, 2), (key2987, 2), (key2586, 2), (key2765, 2), (key2874, 2)]

def rawRow11247 : Integer.Sparse Key := [(key2476, -6), (key2464, -6), (key2499, -6), (key2467, -6), (key2476, 2), (key2464, 2), (key2499, 2), (key2386, 2), (key2370, 2), (key2908, 2), (key2762, 2), (key2987, 2), (key2928, 2), (key2586, 2), (key2874, 2), (key2765, 2)]

def rawRow11248 : Integer.Sparse Key := [(key2464, -6), (key2499, -6), (key2476, -6), (key2467, -6), (key2464, 2), (key2499, 2), (key2476, 2), (key2398, 2), (key2433, 2), (key2583, 2), (key2987, 2), (key2597, 2), (key2908, 2), (key2765, 2), (key2586, 2), (key2874, 2)]

def rawRow11249 : Integer.Sparse Key := [(key2499, -6), (key2464, -6), (key2476, -6), (key2467, -6), (key2499, 2), (key2464, 2), (key2476, 2), (key2433, 2), (key2398, 2), (key2987, 2), (key2583, 2), (key2908, 2), (key2597, 2), (key2765, 2), (key2874, 2), (key2586, 2)]

def rawRow11250 : Integer.Sparse Key := [(key2476, -6), (key2499, -6), (key2464, -6), (key2467, -6), (key2476, 2), (key2499, 2), (key2464, 2), (key2540, 2), (key2551, 2), (key2386, 2), (key2433, 2), (key2370, 2), (key2762, 2), (key2874, 2), (key2586, 2), (key2765, 2)]

def rawRow11251 : Integer.Sparse Key := [(key2499, -6), (key2476, -6), (key2464, -6), (key2467, -6), (key2499, 2), (key2476, 2), (key2464, 2), (key2551, 2), (key2540, 2), (key2433, 2), (key2386, 2), (key2398, 2), (key2583, 2), (key2874, 2), (key2765, 2), (key2586, 2)]

def rawRow11252 : Integer.Sparse Key := [(key2467, -6), (key2476, -6), (key2499, -6), (key2464, -6), (key2534, 2), (key2540, 2), (key2551, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2370, 2), (key2762, 2), (key2839, 2)]

def rawRow11253 : Integer.Sparse Key := [(key2476, -6), (key2467, -6), (key2499, -6), (key2464, -6), (key2540, 2), (key2534, 2), (key2551, 2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2370, 2), (key2839, 2), (key2762, 2)]

def rawRow11254 : Integer.Sparse Key := [(key2467, -6), (key2499, -6), (key2476, -6), (key2464, -6), (key2534, 2), (key2551, 2), (key2540, 2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2398, 2), (key2583, 2), (key2839, 2)]

def rawRow11255 : Integer.Sparse Key := [(key2499, -6), (key2467, -6), (key2476, -6), (key2464, -6), (key2551, 2), (key2534, 2), (key2540, 2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2398, 2), (key2839, 2), (key2583, 2)]

def rawRow11256 : Integer.Sparse Key := [(key2476, -6), (key2499, -6), (key2467, -6), (key2464, -6), (key2540, 2), (key2551, 2), (key2534, 2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2464, 2), (key2370, 2), (key2762, 2)]

def rawRow11257 : Integer.Sparse Key := [(key2499, -6), (key2476, -6), (key2467, -6), (key2464, -6), (key2551, 2), (key2540, 2), (key2534, 2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2464, 2), (key2398, 2), (key2583, 2)]

def rawRow11258 : Integer.Sparse Key := [(key2534, -6), (key2534, -6), (key2540, -6), (key2551, -6), (key2373, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2401, 2), (key2467, 2), (key2467, 2), (key2476, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2499, 2)]

def rawRow11259 : Integer.Sparse Key := [(key2534, -6), (key2540, -6), (key2534, -6), (key2551, -6), (key2373, 2), (key2386, 2), (key2373, 2), (key2467, 2), (key2476, 2), (key2401, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2499, 2), (key2433, 2), (key2499, 2)]

def rawRow11260 : Integer.Sparse Key := [(key2540, -6), (key2534, -6), (key2534, -6), (key2551, -6), (key2386, 2), (key2373, 2), (key2373, 2), (key2476, 2), (key2467, 2), (key2476, 2), (key2401, 2), (key2467, 2), (key2401, 2), (key2499, 2), (key2499, 2), (key2433, 2)]

def rawRow11261 : Integer.Sparse Key := [(key2534, -6), (key2534, -6), (key2551, -6), (key2540, -6), (key2401, 2), (key2401, 2), (key2433, 2), (key2373, 2), (key2373, 2), (key2467, 2), (key2467, 2), (key2499, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2476, 2)]

def rawRow11262 : Integer.Sparse Key := [(key2534, -6), (key2551, -6), (key2534, -6), (key2540, -6), (key2401, 2), (key2433, 2), (key2401, 2), (key2467, 2), (key2499, 2), (key2373, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2476, 2), (key2386, 2), (key2476, 2)]

def rawRow11263 : Integer.Sparse Key := [(key2551, -6), (key2534, -6), (key2534, -6), (key2540, -6), (key2433, 2), (key2401, 2), (key2401, 2), (key2499, 2), (key2467, 2), (key2499, 2), (key2373, 2), (key2467, 2), (key2373, 2), (key2476, 2), (key2476, 2), (key2386, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11264 : Integer.Sparse Key := [(key2534, -6), (key2540, -6), (key2551, -6), (key2534, -6), (key2467, 2), (key2476, 2), (key2499, 2), (key2373, 2), (key2386, 2), (key2401, 2), (key2476, 2), (key2433, 2), (key2499, 2), (key2373, 2), (key2401, 2), (key2467, 2)]

def rawRow11265 : Integer.Sparse Key := [(key2540, -6), (key2534, -6), (key2551, -6), (key2534, -6), (key2476, 2), (key2467, 2), (key2499, 2), (key2386, 2), (key2373, 2), (key2476, 2), (key2401, 2), (key2499, 2), (key2433, 2), (key2373, 2), (key2467, 2), (key2401, 2)]

def rawRow11266 : Integer.Sparse Key := [(key2534, -6), (key2551, -6), (key2540, -6), (key2534, -6), (key2467, 2), (key2499, 2), (key2476, 2), (key2401, 2), (key2433, 2), (key2373, 2), (key2499, 2), (key2386, 2), (key2476, 2), (key2401, 2), (key2373, 2), (key2467, 2)]

def rawRow11267 : Integer.Sparse Key := [(key2551, -6), (key2534, -6), (key2540, -6), (key2534, -6), (key2499, 2), (key2467, 2), (key2476, 2), (key2433, 2), (key2401, 2), (key2499, 2), (key2373, 2), (key2476, 2), (key2386, 2), (key2401, 2), (key2467, 2), (key2373, 2)]

def rawRow11268 : Integer.Sparse Key := [(key2540, -6), (key2551, -6), (key2534, -6), (key2534, -6), (key2476, 2), (key2499, 2), (key2467, 2), (key2476, 2), (key2499, 2), (key2386, 2), (key2433, 2), (key2373, 2), (key2401, 2), (key2467, 2), (key2373, 2), (key2401, 2)]

def rawRow11269 : Integer.Sparse Key := [(key2551, -6), (key2540, -6), (key2534, -6), (key2534, -6), (key2499, 2), (key2476, 2), (key2467, 2), (key2499, 2), (key2476, 2), (key2433, 2), (key2386, 2), (key2401, 2), (key2373, 2), (key2467, 2), (key2401, 2), (key2373, 2)]

def rawRow11270 : Integer.Sparse Key := [(key2697, -6), (key2800, -6), (key2850, -6), (key2854, -6), (key2623, 6), (key2777, 6), (key2850, 6), (key2864, 6)]

def rawRow11271 : Integer.Sparse Key := [(key2697, -6), (key2800, -6), (key2854, -6), (key2850, -6), (key2623, 6), (key2777, 6), (key2864, 6), (key2850, 6)]

def rawRow11272 : Integer.Sparse Key := [(key2697, -6), (key2850, -6), (key2800, -6), (key2854, -6), (key2623, 6), (key2850, 6), (key2777, 6), (key2864, 6)]

def rawRow11273 : Integer.Sparse Key := [(key2697, -6), (key2850, -6), (key2854, -6), (key2800, -6), (key2623, 6), (key2850, 6), (key2864, 6), (key2777, 6)]

def rawRow11274 : Integer.Sparse Key := [(key2697, -6), (key2854, -6), (key2800, -6), (key2850, -6), (key2623, 6), (key2864, 6), (key2777, 6), (key2850, 6)]

def rawRow11275 : Integer.Sparse Key := [(key2697, -6), (key2854, -6), (key2850, -6), (key2800, -6), (key2623, 6), (key2864, 6), (key2850, 6), (key2777, 6)]

def rawRow11276 : Integer.Sparse Key := [(key2800, -6), (key2697, -6), (key2850, -6), (key2854, -6), (key2777, 6), (key2623, 6), (key2850, 6), (key2864, 6)]

def rawRow11277 : Integer.Sparse Key := [(key2800, -6), (key2697, -6), (key2854, -6), (key2850, -6), (key2777, 6), (key2623, 6), (key2864, 6), (key2850, 6)]

def rawRow11278 : Integer.Sparse Key := [(key2800, -6), (key2850, -6), (key2697, -6), (key2854, -6), (key2777, 6), (key2850, 6), (key2623, 6), (key2864, 6)]

def rawRow11279 : Integer.Sparse Key := [(key2800, -6), (key2850, -6), (key2854, -6), (key2697, -6), (key2777, 6), (key2850, 6), (key2864, 6), (key2623, 6)]

def rawRow11280 : Integer.Sparse Key := [(key2800, -6), (key2854, -6), (key2697, -6), (key2850, -6), (key2777, 6), (key2864, 6), (key2623, 6), (key2850, 6)]

def rawRow11281 : Integer.Sparse Key := [(key2800, -6), (key2854, -6), (key2850, -6), (key2697, -6), (key2777, 6), (key2864, 6), (key2850, 6), (key2623, 6)]

def rawRow11282 : Integer.Sparse Key := [(key2850, -6), (key2697, -6), (key2800, -6), (key2854, -6), (key2850, 6), (key2623, 6), (key2777, 6), (key2864, 6)]

def rawRow11283 : Integer.Sparse Key := [(key2850, -6), (key2697, -6), (key2854, -6), (key2800, -6), (key2850, 6), (key2623, 6), (key2864, 6), (key2777, 6)]

def rawRow11284 : Integer.Sparse Key := [(key2850, -6), (key2800, -6), (key2697, -6), (key2854, -6), (key2850, 6), (key2777, 6), (key2623, 6), (key2864, 6)]

def rawRow11285 : Integer.Sparse Key := [(key2850, -6), (key2800, -6), (key2854, -6), (key2697, -6), (key2850, 6), (key2777, 6), (key2864, 6), (key2623, 6)]

def rawRow11286 : Integer.Sparse Key := [(key2850, -6), (key2854, -6), (key2697, -6), (key2800, -6), (key2850, 6), (key2864, 6), (key2623, 6), (key2777, 6)]

def rawRow11287 : Integer.Sparse Key := [(key2850, -6), (key2854, -6), (key2800, -6), (key2697, -6), (key2850, 6), (key2864, 6), (key2777, 6), (key2623, 6)]

def rawRow11288 : Integer.Sparse Key := [(key2854, -6), (key2697, -6), (key2800, -6), (key2850, -6), (key2864, 6), (key2623, 6), (key2777, 6), (key2850, 6)]

def rawRow11289 : Integer.Sparse Key := [(key2854, -6), (key2697, -6), (key2850, -6), (key2800, -6), (key2864, 6), (key2623, 6), (key2850, 6), (key2777, 6)]

def rawRow11290 : Integer.Sparse Key := [(key2854, -6), (key2800, -6), (key2697, -6), (key2850, -6), (key2864, 6), (key2777, 6), (key2623, 6), (key2850, 6)]

def rawRow11291 : Integer.Sparse Key := [(key2854, -6), (key2800, -6), (key2850, -6), (key2697, -6), (key2864, 6), (key2777, 6), (key2850, 6), (key2623, 6)]

def rawRow11292 : Integer.Sparse Key := [(key2854, -6), (key2850, -6), (key2697, -6), (key2800, -6), (key2864, 6), (key2850, 6), (key2623, 6), (key2777, 6)]

def rawRow11293 : Integer.Sparse Key := [(key2854, -6), (key2850, -6), (key2800, -6), (key2697, -6), (key2864, 6), (key2850, 6), (key2777, 6), (key2623, 6)]

def rawRow11294 : Integer.Sparse Key := [(key2720, -6), (key2823, -6), (key2864, -6), (key2864, -6), (key2634, 6), (key2788, 6), (key2854, 6), (key2854, 6)]

def rawRow11295 : Integer.Sparse Key := [(key2720, -6), (key2864, -6), (key2823, -6), (key2864, -6), (key2634, 6), (key2854, 6), (key2788, 6), (key2854, 6)]

def rawRow11296 : Integer.Sparse Key := [(key2720, -6), (key2864, -6), (key2864, -6), (key2823, -6), (key2634, 6), (key2854, 6), (key2854, 6), (key2788, 6)]

def rawRow11297 : Integer.Sparse Key := [(key2823, -6), (key2720, -6), (key2864, -6), (key2864, -6), (key2788, 6), (key2634, 6), (key2854, 6), (key2854, 6)]

def rawRow11298 : Integer.Sparse Key := [(key2823, -6), (key2864, -6), (key2720, -6), (key2864, -6), (key2788, 6), (key2854, 6), (key2634, 6), (key2854, 6)]

def rawRow11299 : Integer.Sparse Key := [(key2823, -6), (key2864, -6), (key2864, -6), (key2720, -6), (key2788, 6), (key2854, 6), (key2854, 6), (key2634, 6)]

def rawRow11300 : Integer.Sparse Key := [(key2864, -6), (key2720, -6), (key2823, -6), (key2864, -6), (key2854, 6), (key2634, 6), (key2788, 6), (key2854, 6)]

def rawRow11301 : Integer.Sparse Key := [(key2864, -6), (key2720, -6), (key2864, -6), (key2823, -6), (key2854, 6), (key2634, 6), (key2854, 6), (key2788, 6)]

def rawRow11302 : Integer.Sparse Key := [(key2864, -6), (key2823, -6), (key2720, -6), (key2864, -6), (key2854, 6), (key2788, 6), (key2634, 6), (key2854, 6)]

def rawRow11303 : Integer.Sparse Key := [(key2864, -6), (key2823, -6), (key2864, -6), (key2720, -6), (key2854, 6), (key2788, 6), (key2854, 6), (key2634, 6)]

def rawRow11304 : Integer.Sparse Key := [(key2864, -6), (key2864, -6), (key2720, -6), (key2823, -6), (key2854, 6), (key2854, 6), (key2634, 6), (key2788, 6)]

def rawRow11305 : Integer.Sparse Key := [(key2864, -6), (key2864, -6), (key2823, -6), (key2720, -6), (key2854, 6), (key2854, 6), (key2788, 6), (key2634, 6)]

def rawRow11306 : Integer.Sparse Key := [(key2632, -2), (key2640, -2), (key2642, -2), (key2706, -2), (key2860, -2), (key2977, -2), (key2726, -2), (key2729, -2), (key2870, -2), (key2984, -2), (key2883, -2), (key2992, -2), (key2616, 2), (key2640, 2), (key2654, 2), (key2671, 2), (key2794, 2), (key2944, 2), (key2726, 2), (key2748, 2), (key2829, 2), (key2961, 2), (key2913, 2), (key2992, 2)]

def rawRow11307 : Integer.Sparse Key := [(key2632, -2), (key2642, -2), (key2640, -2), (key2706, -2), (key2977, -2), (key2860, -2), (key2729, -2), (key2726, -2), (key2984, -2), (key2870, -2), (key2992, -2), (key2883, -2), (key2616, 2), (key2654, 2), (key2640, 2), (key2671, 2), (key2944, 2), (key2794, 2), (key2748, 2), (key2726, 2), (key2961, 2), (key2829, 2), (key2992, 2), (key2913, 2)]

def rawRow11308 : Integer.Sparse Key := [(key2640, -2), (key2632, -2), (key2642, -2), (key2860, -2), (key2706, -2), (key2977, -2), (key2870, -2), (key2883, -2), (key2726, -2), (key2992, -2), (key2729, -2), (key2984, -2), (key2640, 2), (key2616, 2), (key2654, 2), (key2794, 2), (key2671, 2), (key2944, 2), (key2829, 2), (key2913, 2), (key2726, 2), (key2992, 2), (key2748, 2), (key2961, 2)]

def rawRow11309 : Integer.Sparse Key := [(key2640, -2), (key2642, -2), (key2632, -2), (key2860, -2), (key2977, -2), (key2706, -2), (key2883, -2), (key2870, -2), (key2992, -2), (key2726, -2), (key2984, -2), (key2729, -2), (key2640, 2), (key2654, 2), (key2616, 2), (key2794, 2), (key2944, 2), (key2671, 2), (key2913, 2), (key2829, 2), (key2992, 2), (key2726, 2), (key2961, 2), (key2748, 2)]

def rawRow11310 : Integer.Sparse Key := [(key2642, -2), (key2632, -2), (key2640, -2), (key2977, -2), (key2706, -2), (key2860, -2), (key2984, -2), (key2992, -2), (key2729, -2), (key2883, -2), (key2726, -2), (key2870, -2), (key2654, 2), (key2616, 2), (key2640, 2), (key2944, 2), (key2671, 2), (key2794, 2), (key2961, 2), (key2992, 2), (key2748, 2), (key2913, 2), (key2726, 2), (key2829, 2)]

def rawRow11311 : Integer.Sparse Key := [(key2642, -2), (key2640, -2), (key2632, -2), (key2977, -2), (key2860, -2), (key2706, -2), (key2992, -2), (key2984, -2), (key2883, -2), (key2729, -2), (key2870, -2), (key2726, -2), (key2654, 2), (key2640, 2), (key2616, 2), (key2944, 2), (key2794, 2), (key2671, 2), (key2992, 2), (key2961, 2), (key2913, 2), (key2748, 2), (key2829, 2), (key2726, 2)]

def rawRow11312 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2632, -2), (key2870, -2), (key2984, -2), (key2640, -2), (key2642, -2), (key2860, -2), (key2977, -2), (key2883, -2), (key2992, -2), (key2671, 2), (key2726, 2), (key2748, 2), (key2616, 2), (key2829, 2), (key2961, 2), (key2640, 2), (key2654, 2), (key2794, 2), (key2944, 2), (key2913, 2), (key2992, 2)]

def rawRow11313 : Integer.Sparse Key := [(key2706, -2), (key2729, -2), (key2726, -2), (key2632, -2), (key2984, -2), (key2870, -2), (key2642, -2), (key2640, -2), (key2977, -2), (key2860, -2), (key2992, -2), (key2883, -2), (key2671, 2), (key2748, 2), (key2726, 2), (key2616, 2), (key2961, 2), (key2829, 2), (key2654, 2), (key2640, 2), (key2944, 2), (key2794, 2), (key2992, 2), (key2913, 2)]

def rawRow11314 : Integer.Sparse Key := [(key2726, -2), (key2706, -2), (key2729, -2), (key2870, -2), (key2632, -2), (key2984, -2), (key2860, -2), (key2883, -2), (key2640, -2), (key2992, -2), (key2642, -2), (key2977, -2), (key2726, 2), (key2671, 2), (key2748, 2), (key2829, 2), (key2616, 2), (key2961, 2), (key2794, 2), (key2913, 2), (key2640, 2), (key2992, 2), (key2654, 2), (key2944, 2)]

def rawRow11315 : Integer.Sparse Key := [(key2726, -2), (key2729, -2), (key2706, -2), (key2870, -2), (key2984, -2), (key2632, -2), (key2883, -2), (key2860, -2), (key2992, -2), (key2640, -2), (key2977, -2), (key2642, -2), (key2726, 2), (key2748, 2), (key2671, 2), (key2829, 2), (key2961, 2), (key2616, 2), (key2913, 2), (key2794, 2), (key2992, 2), (key2640, 2), (key2944, 2), (key2654, 2)]

def rawRow11316 : Integer.Sparse Key := [(key2729, -2), (key2706, -2), (key2726, -2), (key2984, -2), (key2632, -2), (key2870, -2), (key2977, -2), (key2992, -2), (key2642, -2), (key2883, -2), (key2640, -2), (key2860, -2), (key2748, 2), (key2671, 2), (key2726, 2), (key2961, 2), (key2616, 2), (key2829, 2), (key2944, 2), (key2992, 2), (key2654, 2), (key2913, 2), (key2640, 2), (key2794, 2)]

def rawRow11317 : Integer.Sparse Key := [(key2729, -2), (key2726, -2), (key2706, -2), (key2984, -2), (key2870, -2), (key2632, -2), (key2992, -2), (key2977, -2), (key2883, -2), (key2642, -2), (key2860, -2), (key2640, -2), (key2748, 2), (key2726, 2), (key2671, 2), (key2961, 2), (key2829, 2), (key2616, 2), (key2992, 2), (key2944, 2), (key2913, 2), (key2654, 2), (key2794, 2), (key2640, 2)]

def rawRow11318 : Integer.Sparse Key := [(key2860, -2), (key2870, -2), (key2883, -2), (key2640, -2), (key2726, -2), (key2992, -2), (key2632, -2), (key2642, -2), (key2706, -2), (key2977, -2), (key2729, -2), (key2984, -2), (key2794, 2), (key2829, 2), (key2913, 2), (key2640, 2), (key2726, 2), (key2992, 2), (key2616, 2), (key2654, 2), (key2671, 2), (key2944, 2), (key2748, 2), (key2961, 2)]

def rawRow11319 : Integer.Sparse Key := [(key2860, -2), (key2883, -2), (key2870, -2), (key2640, -2), (key2992, -2), (key2726, -2), (key2642, -2), (key2632, -2), (key2977, -2), (key2706, -2), (key2984, -2), (key2729, -2), (key2794, 2), (key2913, 2), (key2829, 2), (key2640, 2), (key2992, 2), (key2726, 2), (key2654, 2), (key2616, 2), (key2944, 2), (key2671, 2), (key2961, 2), (key2748, 2)]

def rawRow11320 : Integer.Sparse Key := [(key2870, -2), (key2860, -2), (key2883, -2), (key2726, -2), (key2640, -2), (key2992, -2), (key2706, -2), (key2729, -2), (key2632, -2), (key2984, -2), (key2642, -2), (key2977, -2), (key2829, 2), (key2794, 2), (key2913, 2), (key2726, 2), (key2640, 2), (key2992, 2), (key2671, 2), (key2748, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2944, 2)]

def rawRow11321 : Integer.Sparse Key := [(key2870, -2), (key2883, -2), (key2860, -2), (key2726, -2), (key2992, -2), (key2640, -2), (key2729, -2), (key2706, -2), (key2984, -2), (key2632, -2), (key2977, -2), (key2642, -2), (key2829, 2), (key2913, 2), (key2794, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2944, 2), (key2654, 2)]

def rawRow11322 : Integer.Sparse Key := [(key2883, -2), (key2860, -2), (key2870, -2), (key2992, -2), (key2640, -2), (key2726, -2), (key2977, -2), (key2984, -2), (key2642, -2), (key2729, -2), (key2632, -2), (key2706, -2), (key2913, 2), (key2794, 2), (key2829, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2944, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2616, 2), (key2671, 2)]

def rawRow11323 : Integer.Sparse Key := [(key2883, -2), (key2870, -2), (key2860, -2), (key2992, -2), (key2726, -2), (key2640, -2), (key2984, -2), (key2977, -2), (key2729, -2), (key2642, -2), (key2706, -2), (key2632, -2), (key2913, 2), (key2829, 2), (key2794, 2), (key2992, 2), (key2726, 2), (key2640, 2), (key2961, 2), (key2944, 2), (key2748, 2), (key2654, 2), (key2671, 2), (key2616, 2)]

def rawRow11324 : Integer.Sparse Key := [(key2977, -2), (key2984, -2), (key2992, -2), (key2642, -2), (key2729, -2), (key2883, -2), (key2632, -2), (key2640, -2), (key2706, -2), (key2860, -2), (key2726, -2), (key2870, -2), (key2944, 2), (key2961, 2), (key2992, 2), (key2654, 2), (key2748, 2), (key2913, 2), (key2616, 2), (key2640, 2), (key2671, 2), (key2794, 2), (key2726, 2), (key2829, 2)]

def rawRow11325 : Integer.Sparse Key := [(key2977, -2), (key2992, -2), (key2984, -2), (key2642, -2), (key2883, -2), (key2729, -2), (key2640, -2), (key2632, -2), (key2860, -2), (key2706, -2), (key2870, -2), (key2726, -2), (key2944, 2), (key2992, 2), (key2961, 2), (key2654, 2), (key2913, 2), (key2748, 2), (key2640, 2), (key2616, 2), (key2794, 2), (key2671, 2), (key2829, 2), (key2726, 2)]

def rawRow11326 : Integer.Sparse Key := [(key2984, -2), (key2977, -2), (key2992, -2), (key2729, -2), (key2642, -2), (key2883, -2), (key2706, -2), (key2726, -2), (key2632, -2), (key2870, -2), (key2640, -2), (key2860, -2), (key2961, 2), (key2944, 2), (key2992, 2), (key2748, 2), (key2654, 2), (key2913, 2), (key2671, 2), (key2726, 2), (key2616, 2), (key2829, 2), (key2640, 2), (key2794, 2)]

def rawRow11327 : Integer.Sparse Key := [(key2984, -2), (key2992, -2), (key2977, -2), (key2729, -2), (key2883, -2), (key2642, -2), (key2726, -2), (key2706, -2), (key2870, -2), (key2632, -2), (key2860, -2), (key2640, -2), (key2961, 2), (key2992, 2), (key2944, 2), (key2748, 2), (key2913, 2), (key2654, 2), (key2726, 2), (key2671, 2), (key2829, 2), (key2616, 2), (key2794, 2), (key2640, 2)]

def rawRow11328 : Integer.Sparse Key := [(key2992, -2), (key2977, -2), (key2984, -2), (key2883, -2), (key2642, -2), (key2729, -2), (key2860, -2), (key2870, -2), (key2640, -2), (key2726, -2), (key2632, -2), (key2706, -2), (key2992, 2), (key2944, 2), (key2961, 2), (key2913, 2), (key2654, 2), (key2748, 2), (key2794, 2), (key2829, 2), (key2640, 2), (key2726, 2), (key2616, 2), (key2671, 2)]

def rawRow11329 : Integer.Sparse Key := [(key2992, -2), (key2984, -2), (key2977, -2), (key2883, -2), (key2729, -2), (key2642, -2), (key2870, -2), (key2860, -2), (key2726, -2), (key2640, -2), (key2706, -2), (key2632, -2), (key2992, 2), (key2961, 2), (key2944, 2), (key2913, 2), (key2748, 2), (key2654, 2), (key2829, 2), (key2794, 2), (key2726, 2), (key2640, 2), (key2671, 2), (key2616, 2)]

def rawRow11330 : Integer.Sparse Key := [(key2649, -2), (key2654, -2), (key2654, -2), (key2738, -2), (key2898, -2), (key2898, -2), (key2748, -2), (key2748, -2), (key2905, -2), (key2905, -2), (key2913, -2), (key2913, -2), (key2619, 2), (key2642, 2), (key2642, 2), (key2674, 2), (key2796, 2), (key2796, 2), (key2729, 2), (key2729, 2), (key2832, 2), (key2832, 2), (key2883, 2), (key2883, 2)]

def rawRow11331 : Integer.Sparse Key := [(key2654, -2), (key2649, -2), (key2654, -2), (key2898, -2), (key2738, -2), (key2898, -2), (key2905, -2), (key2913, -2), (key2748, -2), (key2913, -2), (key2748, -2), (key2905, -2), (key2642, 2), (key2619, 2), (key2642, 2), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, 2), (key2883, 2), (key2729, 2), (key2883, 2), (key2729, 2), (key2832, 2)]

def rawRow11332 : Integer.Sparse Key := [(key2654, -2), (key2654, -2), (key2649, -2), (key2898, -2), (key2898, -2), (key2738, -2), (key2913, -2), (key2905, -2), (key2913, -2), (key2748, -2), (key2905, -2), (key2748, -2), (key2642, 2), (key2642, 2), (key2619, 2), (key2796, 2), (key2796, 2), (key2674, 2), (key2883, 2), (key2832, 2), (key2883, 2), (key2729, 2), (key2832, 2), (key2729, 2)]

def rawRow11333 : Integer.Sparse Key := [(key2738, -2), (key2748, -2), (key2748, -2), (key2649, -2), (key2905, -2), (key2905, -2), (key2654, -2), (key2654, -2), (key2898, -2), (key2898, -2), (key2913, -2), (key2913, -2), (key2674, 2), (key2729, 2), (key2729, 2), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, 2), (key2642, 2), (key2796, 2), (key2796, 2), (key2883, 2), (key2883, 2)]

def rawRow11334 : Integer.Sparse Key := [(key2748, -2), (key2738, -2), (key2748, -2), (key2905, -2), (key2649, -2), (key2905, -2), (key2898, -2), (key2913, -2), (key2654, -2), (key2913, -2), (key2654, -2), (key2898, -2), (key2729, 2), (key2674, 2), (key2729, 2), (key2832, 2), (key2619, 2), (key2832, 2), (key2796, 2), (key2883, 2), (key2642, 2), (key2883, 2), (key2642, 2), (key2796, 2)]

def rawRow11335 : Integer.Sparse Key := [(key2748, -2), (key2748, -2), (key2738, -2), (key2905, -2), (key2905, -2), (key2649, -2), (key2913, -2), (key2898, -2), (key2913, -2), (key2654, -2), (key2898, -2), (key2654, -2), (key2729, 2), (key2729, 2), (key2674, 2), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, 2), (key2796, 2), (key2883, 2), (key2642, 2), (key2796, 2), (key2642, 2)]

def rawRow11336 : Integer.Sparse Key := [(key2898, -2), (key2905, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2913, -2), (key2649, -2), (key2654, -2), (key2738, -2), (key2898, -2), (key2748, -2), (key2905, -2), (key2796, 2), (key2832, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2883, 2), (key2619, 2), (key2642, 2), (key2674, 2), (key2796, 2), (key2729, 2), (key2832, 2)]

def rawRow11337 : Integer.Sparse Key := [(key2898, -2), (key2913, -2), (key2905, -2), (key2654, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2649, -2), (key2898, -2), (key2738, -2), (key2905, -2), (key2748, -2), (key2796, 2), (key2883, 2), (key2832, 2), (key2642, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2619, 2), (key2796, 2), (key2674, 2), (key2832, 2), (key2729, 2)]

def rawRow11338 : Integer.Sparse Key := [(key2905, -2), (key2898, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2913, -2), (key2738, -2), (key2748, -2), (key2649, -2), (key2905, -2), (key2654, -2), (key2898, -2), (key2832, 2), (key2796, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2883, 2), (key2674, 2), (key2729, 2), (key2619, 2), (key2832, 2), (key2642, 2), (key2796, 2)]

def rawRow11339 : Integer.Sparse Key := [(key2905, -2), (key2913, -2), (key2898, -2), (key2748, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2738, -2), (key2905, -2), (key2649, -2), (key2898, -2), (key2654, -2), (key2832, 2), (key2883, 2), (key2796, 2), (key2729, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2674, 2), (key2832, 2), (key2619, 2), (key2796, 2), (key2642, 2)]

def rawRow11340 : Integer.Sparse Key := [(key2913, -2), (key2898, -2), (key2905, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2898, -2), (key2905, -2), (key2654, -2), (key2748, -2), (key2649, -2), (key2738, -2), (key2883, 2), (key2796, 2), (key2832, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2796, 2), (key2832, 2), (key2642, 2), (key2729, 2), (key2619, 2), (key2674, 2)]

def rawRow11341 : Integer.Sparse Key := [(key2913, -2), (key2905, -2), (key2898, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2905, -2), (key2898, -2), (key2748, -2), (key2654, -2), (key2738, -2), (key2649, -2), (key2883, 2), (key2832, 2), (key2796, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2832, 2), (key2796, 2), (key2729, 2), (key2642, 2), (key2674, 2), (key2619, 2)]

def rawRow11342 : Integer.Sparse Key := [(key1003, 2), (key1017, 2), (key1020, 2), (key1038, 2), (key1125, 2), (key1200, 2), (key1073, 2), (key1077, 2), (key1152, 2), (key1213, 2), (key1172, 2), (key1223, 2), (key1003, -2), (key1007, -2), (key1020, -2), (key1038, -2), (key1042, -2), (key1116, -2), (key1194, -2), (key1128, -2), (key1200, -2), (key1077, -2), (key1156, -2), (key1213, -2)]

def rawRow11343 : Integer.Sparse Key := [(key1003, 2), (key1020, 2), (key1017, 2), (key1038, 2), (key1200, 2), (key1125, 2), (key1077, 2), (key1073, 2), (key1213, 2), (key1152, 2), (key1223, 2), (key1172, 2), (key1007, -2), (key1003, -2), (key1020, -2), (key1042, -2), (key1038, -2), (key1194, -2), (key1116, -2), (key1200, -2), (key1128, -2), (key1077, -2), (key1213, -2), (key1156, -2)]

def rawRow11344 : Integer.Sparse Key := [(key1017, 2), (key1003, 2), (key1020, 2), (key1125, 2), (key1038, 2), (key1200, 2), (key1152, 2), (key1172, 2), (key1073, 2), (key1223, 2), (key1077, 2), (key1213, 2), (key1003, -2), (key1020, -2), (key1007, -2), (key1116, -2), (key1128, -2), (key1038, -2), (key1200, -2), (key1042, -2), (key1194, -2), (key1156, -2), (key1077, -2), (key1213, -2)]

def rawRow11345 : Integer.Sparse Key := [(key1017, 2), (key1020, 2), (key1003, 2), (key1125, 2), (key1200, 2), (key1038, 2), (key1172, 2), (key1152, 2), (key1223, 2), (key1073, 2), (key1213, 2), (key1077, 2), (key1020, -2), (key1003, -2), (key1007, -2), (key1128, -2), (key1116, -2), (key1200, -2), (key1038, -2), (key1194, -2), (key1042, -2), (key1156, -2), (key1213, -2), (key1077, -2)]

def rawRow11346 : Integer.Sparse Key := [(key1020, 2), (key1003, 2), (key1017, 2), (key1200, 2), (key1038, 2), (key1125, 2), (key1213, 2), (key1223, 2), (key1077, 2), (key1172, 2), (key1073, 2), (key1152, 2), (key1007, -2), (key1020, -2), (key1003, -2), (key1194, -2), (key1200, -2), (key1042, -2), (key1128, -2), (key1038, -2), (key1116, -2), (key1213, -2), (key1077, -2), (key1156, -2)]

def rawRow11347 : Integer.Sparse Key := [(key1020, 2), (key1017, 2), (key1003, 2), (key1200, 2), (key1125, 2), (key1038, 2), (key1223, 2), (key1213, 2), (key1172, 2), (key1077, 2), (key1152, 2), (key1073, 2), (key1020, -2), (key1007, -2), (key1003, -2), (key1200, -2), (key1194, -2), (key1128, -2), (key1042, -2), (key1116, -2), (key1038, -2), (key1213, -2), (key1156, -2), (key1077, -2)]

def rawRow11348 : Integer.Sparse Key := [(key1038, 2), (key1073, 2), (key1077, 2), (key1003, 2), (key1152, 2), (key1213, 2), (key1017, 2), (key1020, 2), (key1125, 2), (key1200, 2), (key1172, 2), (key1223, 2), (key1038, -2), (key1042, -2), (key1077, -2), (key1003, -2), (key1007, -2), (key1116, -2), (key1194, -2), (key1156, -2), (key1213, -2), (key1020, -2), (key1128, -2), (key1200, -2)]

def rawRow11349 : Integer.Sparse Key := [(key1038, 2), (key1077, 2), (key1073, 2), (key1003, 2), (key1213, 2), (key1152, 2), (key1020, 2), (key1017, 2), (key1200, 2), (key1125, 2), (key1223, 2), (key1172, 2), (key1042, -2), (key1038, -2), (key1077, -2), (key1007, -2), (key1003, -2), (key1194, -2), (key1116, -2), (key1213, -2), (key1156, -2), (key1020, -2), (key1200, -2), (key1128, -2)]

def rawRow11350 : Integer.Sparse Key := [(key1073, 2), (key1038, 2), (key1077, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1125, 2), (key1172, 2), (key1017, 2), (key1223, 2), (key1020, 2), (key1200, 2), (key1038, -2), (key1077, -2), (key1042, -2), (key1116, -2), (key1156, -2), (key1003, -2), (key1213, -2), (key1007, -2), (key1194, -2), (key1128, -2), (key1020, -2), (key1200, -2)]

def rawRow11351 : Integer.Sparse Key := [(key1073, 2), (key1077, 2), (key1038, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1172, 2), (key1125, 2), (key1223, 2), (key1017, 2), (key1200, 2), (key1020, 2), (key1077, -2), (key1038, -2), (key1042, -2), (key1156, -2), (key1116, -2), (key1213, -2), (key1003, -2), (key1194, -2), (key1007, -2), (key1128, -2), (key1200, -2), (key1020, -2)]

def rawRow11352 : Integer.Sparse Key := [(key1077, 2), (key1038, 2), (key1073, 2), (key1213, 2), (key1003, 2), (key1152, 2), (key1200, 2), (key1223, 2), (key1020, 2), (key1172, 2), (key1017, 2), (key1125, 2), (key1042, -2), (key1077, -2), (key1038, -2), (key1194, -2), (key1213, -2), (key1007, -2), (key1156, -2), (key1003, -2), (key1116, -2), (key1200, -2), (key1020, -2), (key1128, -2)]

def rawRow11353 : Integer.Sparse Key := [(key1077, 2), (key1073, 2), (key1038, 2), (key1213, 2), (key1152, 2), (key1003, 2), (key1223, 2), (key1200, 2), (key1172, 2), (key1020, 2), (key1125, 2), (key1017, 2), (key1077, -2), (key1042, -2), (key1038, -2), (key1213, -2), (key1194, -2), (key1156, -2), (key1007, -2), (key1116, -2), (key1003, -2), (key1200, -2), (key1128, -2), (key1020, -2)]

def rawRow11354 : Integer.Sparse Key := [(key1125, 2), (key1152, 2), (key1172, 2), (key1017, 2), (key1073, 2), (key1223, 2), (key1003, 2), (key1020, 2), (key1038, 2), (key1200, 2), (key1077, 2), (key1213, 2), (key1116, -2), (key1128, -2), (key1156, -2), (key1003, -2), (key1020, -2), (key1038, -2), (key1200, -2), (key1077, -2), (key1213, -2), (key1007, -2), (key1042, -2), (key1194, -2)]

def rawRow11355 : Integer.Sparse Key := [(key1125, 2), (key1172, 2), (key1152, 2), (key1017, 2), (key1223, 2), (key1073, 2), (key1020, 2), (key1003, 2), (key1200, 2), (key1038, 2), (key1213, 2), (key1077, 2), (key1128, -2), (key1116, -2), (key1156, -2), (key1020, -2), (key1003, -2), (key1200, -2), (key1038, -2), (key1213, -2), (key1077, -2), (key1007, -2), (key1194, -2), (key1042, -2)]

def rawRow11356 : Integer.Sparse Key := [(key1152, 2), (key1125, 2), (key1172, 2), (key1073, 2), (key1017, 2), (key1223, 2), (key1038, 2), (key1077, 2), (key1003, 2), (key1213, 2), (key1020, 2), (key1200, 2), (key1116, -2), (key1156, -2), (key1128, -2), (key1038, -2), (key1077, -2), (key1003, -2), (key1213, -2), (key1020, -2), (key1200, -2), (key1042, -2), (key1007, -2), (key1194, -2)]

def rawRow11357 : Integer.Sparse Key := [(key1152, 2), (key1172, 2), (key1125, 2), (key1073, 2), (key1223, 2), (key1017, 2), (key1077, 2), (key1038, 2), (key1213, 2), (key1003, 2), (key1200, 2), (key1020, 2), (key1156, -2), (key1116, -2), (key1128, -2), (key1077, -2), (key1038, -2), (key1213, -2), (key1003, -2), (key1200, -2), (key1020, -2), (key1042, -2), (key1194, -2), (key1007, -2)]

def rawRow11358 : Integer.Sparse Key := [(key1172, 2), (key1125, 2), (key1152, 2), (key1223, 2), (key1017, 2), (key1073, 2), (key1200, 2), (key1213, 2), (key1020, 2), (key1077, 2), (key1003, 2), (key1038, 2), (key1128, -2), (key1156, -2), (key1116, -2), (key1200, -2), (key1213, -2), (key1020, -2), (key1077, -2), (key1003, -2), (key1038, -2), (key1194, -2), (key1007, -2), (key1042, -2)]

def rawRow11359 : Integer.Sparse Key := [(key1172, 2), (key1152, 2), (key1125, 2), (key1223, 2), (key1073, 2), (key1017, 2), (key1213, 2), (key1200, 2), (key1077, 2), (key1020, 2), (key1038, 2), (key1003, 2), (key1156, -2), (key1128, -2), (key1116, -2), (key1213, -2), (key1200, -2), (key1077, -2), (key1020, -2), (key1038, -2), (key1003, -2), (key1194, -2), (key1042, -2), (key1007, -2)]

def rawRow11360 : Integer.Sparse Key := [(key1200, 2), (key1213, 2), (key1223, 2), (key1020, 2), (key1077, 2), (key1172, 2), (key1003, 2), (key1017, 2), (key1038, 2), (key1125, 2), (key1073, 2), (key1152, 2), (key1194, -2), (key1200, -2), (key1213, -2), (key1007, -2), (key1020, -2), (key1042, -2), (key1128, -2), (key1077, -2), (key1156, -2), (key1003, -2), (key1038, -2), (key1116, -2)]

def rawRow11361 : Integer.Sparse Key := [(key1200, 2), (key1223, 2), (key1213, 2), (key1020, 2), (key1172, 2), (key1077, 2), (key1017, 2), (key1003, 2), (key1125, 2), (key1038, 2), (key1152, 2), (key1073, 2), (key1200, -2), (key1194, -2), (key1213, -2), (key1020, -2), (key1007, -2), (key1128, -2), (key1042, -2), (key1156, -2), (key1077, -2), (key1003, -2), (key1116, -2), (key1038, -2)]

def rawRow11362 : Integer.Sparse Key := [(key1213, 2), (key1200, 2), (key1223, 2), (key1077, 2), (key1020, 2), (key1172, 2), (key1038, 2), (key1073, 2), (key1003, 2), (key1152, 2), (key1017, 2), (key1125, 2), (key1194, -2), (key1213, -2), (key1200, -2), (key1042, -2), (key1077, -2), (key1007, -2), (key1156, -2), (key1020, -2), (key1128, -2), (key1038, -2), (key1003, -2), (key1116, -2)]

def rawRow11363 : Integer.Sparse Key := [(key1213, 2), (key1223, 2), (key1200, 2), (key1077, 2), (key1172, 2), (key1020, 2), (key1073, 2), (key1038, 2), (key1152, 2), (key1003, 2), (key1125, 2), (key1017, 2), (key1213, -2), (key1194, -2), (key1200, -2), (key1077, -2), (key1042, -2), (key1156, -2), (key1007, -2), (key1128, -2), (key1020, -2), (key1038, -2), (key1116, -2), (key1003, -2)]

def rawRow11364 : Integer.Sparse Key := [(key1223, 2), (key1200, 2), (key1213, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1125, 2), (key1152, 2), (key1017, 2), (key1073, 2), (key1003, 2), (key1038, 2), (key1200, -2), (key1213, -2), (key1194, -2), (key1128, -2), (key1156, -2), (key1020, -2), (key1077, -2), (key1007, -2), (key1042, -2), (key1116, -2), (key1003, -2), (key1038, -2)]

def rawRow11365 : Integer.Sparse Key := [(key1223, 2), (key1213, 2), (key1200, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1152, 2), (key1125, 2), (key1073, 2), (key1017, 2), (key1038, 2), (key1003, 2), (key1213, -2), (key1200, -2), (key1194, -2), (key1156, -2), (key1128, -2), (key1077, -2), (key1020, -2), (key1042, -2), (key1007, -2), (key1116, -2), (key1038, -2), (key1003, -2)]

def rawRow11366 : Integer.Sparse Key := [(key1007, 2), (key1020, 2), (key1020, 2), (key1042, 2), (key1128, 2), (key1128, 2), (key1077, 2), (key1077, 2), (key1156, 2), (key1156, 2), (key1172, 2), (key1172, 2), (key1003, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1152, -2)]

def rawRow11367 : Integer.Sparse Key := [(key1020, 2), (key1007, 2), (key1020, 2), (key1128, 2), (key1042, 2), (key1128, 2), (key1156, 2), (key1172, 2), (key1077, 2), (key1172, 2), (key1077, 2), (key1156, 2), (key1003, -2), (key1017, -2), (key1003, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1073, -2), (key1152, -2)]

def rawRow11368 : Integer.Sparse Key := [(key1020, 2), (key1020, 2), (key1007, 2), (key1128, 2), (key1128, 2), (key1042, 2), (key1172, 2), (key1156, 2), (key1172, 2), (key1077, 2), (key1156, 2), (key1077, 2), (key1017, -2), (key1003, -2), (key1003, -2), (key1125, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1038, -2), (key1152, -2), (key1152, -2), (key1073, -2)]

def rawRow11369 : Integer.Sparse Key := [(key1042, 2), (key1077, 2), (key1077, 2), (key1007, 2), (key1156, 2), (key1156, 2), (key1020, 2), (key1020, 2), (key1128, 2), (key1128, 2), (key1172, 2), (key1172, 2), (key1038, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1003, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1125, -2)]

def rawRow11370 : Integer.Sparse Key := [(key1077, 2), (key1042, 2), (key1077, 2), (key1156, 2), (key1007, 2), (key1156, 2), (key1128, 2), (key1172, 2), (key1020, 2), (key1172, 2), (key1020, 2), (key1128, 2), (key1038, -2), (key1073, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1125, -2), (key1017, -2), (key1125, -2)]

def rawRow11371 : Integer.Sparse Key := [(key1077, 2), (key1077, 2), (key1042, 2), (key1156, 2), (key1156, 2), (key1007, 2), (key1172, 2), (key1128, 2), (key1172, 2), (key1020, 2), (key1128, 2), (key1020, 2), (key1073, -2), (key1038, -2), (key1038, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1125, -2), (key1125, -2), (key1017, -2)]

def rawRow11372 : Integer.Sparse Key := [(key1128, 2), (key1156, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1172, 2), (key1007, 2), (key1020, 2), (key1042, 2), (key1128, 2), (key1077, 2), (key1156, 2), (key1116, -2), (key1125, -2), (key1152, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1125, -2), (key1073, -2), (key1152, -2), (key1003, -2), (key1038, -2), (key1116, -2)]

def rawRow11373 : Integer.Sparse Key := [(key1128, 2), (key1172, 2), (key1156, 2), (key1020, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1007, 2), (key1128, 2), (key1042, 2), (key1156, 2), (key1077, 2), (key1125, -2), (key1116, -2), (key1152, -2), (key1017, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1073, -2), (key1003, -2), (key1116, -2), (key1038, -2)]

def rawRow11374 : Integer.Sparse Key := [(key1156, 2), (key1128, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1172, 2), (key1042, 2), (key1077, 2), (key1007, 2), (key1156, 2), (key1020, 2), (key1128, 2), (key1116, -2), (key1152, -2), (key1125, -2), (key1038, -2), (key1073, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1038, -2), (key1003, -2), (key1116, -2)]

def rawRow11375 : Integer.Sparse Key := [(key1156, 2), (key1172, 2), (key1128, 2), (key1077, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1042, 2), (key1156, 2), (key1007, 2), (key1128, 2), (key1020, 2), (key1152, -2), (key1116, -2), (key1125, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1017, -2), (key1038, -2), (key1116, -2), (key1003, -2)]

def rawRow11376 : Integer.Sparse Key := [(key1172, 2), (key1128, 2), (key1156, 2), (key1172, 2), (key1020, 2), (key1077, 2), (key1128, 2), (key1156, 2), (key1020, 2), (key1077, 2), (key1007, 2), (key1042, 2), (key1125, -2), (key1152, -2), (key1116, -2), (key1125, -2), (key1152, -2), (key1017, -2), (key1073, -2), (key1003, -2), (key1038, -2), (key1116, -2), (key1003, -2), (key1038, -2)]

def rawRow11377 : Integer.Sparse Key := [(key1172, 2), (key1156, 2), (key1128, 2), (key1172, 2), (key1077, 2), (key1020, 2), (key1156, 2), (key1128, 2), (key1077, 2), (key1020, 2), (key1042, 2), (key1007, 2), (key1152, -2), (key1125, -2), (key1116, -2), (key1152, -2), (key1125, -2), (key1073, -2), (key1017, -2), (key1038, -2), (key1003, -2), (key1116, -2), (key1038, -2), (key1003, -2)]

def rawRow11378 : Integer.Sparse Key := [(key2678, -4), (key2709, -4), (key2713, -4), (key2812, -4), (key2816, -4), (key2862, -4), (key2678, 6), (key2687, 6), (key2713, 6), (key2816, 6)]

def rawRow11379 : Integer.Sparse Key := [(key2678, -4), (key2713, -4), (key2709, -4), (key2816, -4), (key2812, -4), (key2862, -4), (key2687, 6), (key2678, 6), (key2713, 6), (key2816, 6)]

def rawRow11380 : Integer.Sparse Key := [(key2709, -4), (key2678, -4), (key2713, -4), (key2812, -4), (key2862, -4), (key2816, -4), (key2678, 6), (key2713, 6), (key2687, 6), (key2816, 6)]

def rawRow11381 : Integer.Sparse Key := [(key2709, -4), (key2713, -4), (key2678, -4), (key2862, -4), (key2812, -4), (key2816, -4), (key2713, 6), (key2678, 6), (key2687, 6), (key2816, 6)]

def rawRow11382 : Integer.Sparse Key := [(key2713, -4), (key2678, -4), (key2709, -4), (key2816, -4), (key2862, -4), (key2812, -4), (key2687, 6), (key2713, 6), (key2678, 6), (key2816, 6)]

def rawRow11383 : Integer.Sparse Key := [(key2713, -4), (key2709, -4), (key2678, -4), (key2862, -4), (key2816, -4), (key2812, -4), (key2713, 6), (key2687, 6), (key2678, 6), (key2816, 6)]

def rawRow11384 : Integer.Sparse Key := [(key2678, -4), (key2812, -4), (key2816, -4), (key2709, -4), (key2713, -4), (key2862, -4), (key2678, 6), (key2687, 6), (key2816, 6), (key2713, 6)]

def rawRow11385 : Integer.Sparse Key := [(key2678, -4), (key2816, -4), (key2812, -4), (key2713, -4), (key2709, -4), (key2862, -4), (key2687, 6), (key2678, 6), (key2816, 6), (key2713, 6)]

def rawRow11386 : Integer.Sparse Key := [(key2812, -4), (key2678, -4), (key2816, -4), (key2709, -4), (key2862, -4), (key2713, -4), (key2678, 6), (key2816, 6), (key2687, 6), (key2713, 6)]

def rawRow11387 : Integer.Sparse Key := [(key2812, -4), (key2816, -4), (key2678, -4), (key2862, -4), (key2709, -4), (key2713, -4), (key2816, 6), (key2678, 6), (key2687, 6), (key2713, 6)]

def rawRow11388 : Integer.Sparse Key := [(key2816, -4), (key2678, -4), (key2812, -4), (key2713, -4), (key2862, -4), (key2709, -4), (key2687, 6), (key2816, 6), (key2678, 6), (key2713, 6)]

def rawRow11389 : Integer.Sparse Key := [(key2816, -4), (key2812, -4), (key2678, -4), (key2862, -4), (key2713, -4), (key2709, -4), (key2816, 6), (key2687, 6), (key2678, 6), (key2713, 6)]

def rawRow11390 : Integer.Sparse Key := [(key2709, -4), (key2812, -4), (key2862, -4), (key2678, -4), (key2713, -4), (key2816, -4), (key2678, 6), (key2713, 6), (key2816, 6), (key2687, 6)]

def rawRow11391 : Integer.Sparse Key := [(key2709, -4), (key2862, -4), (key2812, -4), (key2713, -4), (key2678, -4), (key2816, -4), (key2713, 6), (key2678, 6), (key2816, 6), (key2687, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11392 : Integer.Sparse Key := [(key2812, -4), (key2709, -4), (key2862, -4), (key2678, -4), (key2816, -4), (key2713, -4), (key2678, 6), (key2816, 6), (key2713, 6), (key2687, 6)]

def rawRow11393 : Integer.Sparse Key := [(key2812, -4), (key2862, -4), (key2709, -4), (key2816, -4), (key2678, -4), (key2713, -4), (key2816, 6), (key2678, 6), (key2713, 6), (key2687, 6)]

def rawRow11394 : Integer.Sparse Key := [(key2862, -4), (key2709, -4), (key2812, -4), (key2713, -4), (key2816, -4), (key2678, -4), (key2713, 6), (key2816, 6), (key2678, 6), (key2687, 6)]

def rawRow11395 : Integer.Sparse Key := [(key2862, -4), (key2812, -4), (key2709, -4), (key2816, -4), (key2713, -4), (key2678, -4), (key2816, 6), (key2713, 6), (key2678, 6), (key2687, 6)]

def rawRow11396 : Integer.Sparse Key := [(key2713, -4), (key2816, -4), (key2862, -4), (key2678, -4), (key2709, -4), (key2812, -4), (key2687, 6), (key2713, 6), (key2816, 6), (key2678, 6)]

def rawRow11397 : Integer.Sparse Key := [(key2713, -4), (key2862, -4), (key2816, -4), (key2709, -4), (key2678, -4), (key2812, -4), (key2713, 6), (key2687, 6), (key2816, 6), (key2678, 6)]

def rawRow11398 : Integer.Sparse Key := [(key2816, -4), (key2713, -4), (key2862, -4), (key2678, -4), (key2812, -4), (key2709, -4), (key2687, 6), (key2816, 6), (key2713, 6), (key2678, 6)]

def rawRow11399 : Integer.Sparse Key := [(key2816, -4), (key2862, -4), (key2713, -4), (key2812, -4), (key2678, -4), (key2709, -4), (key2816, 6), (key2687, 6), (key2713, 6), (key2678, 6)]

def rawRow11400 : Integer.Sparse Key := [(key2862, -4), (key2713, -4), (key2816, -4), (key2709, -4), (key2812, -4), (key2678, -4), (key2713, 6), (key2816, 6), (key2687, 6), (key2678, 6)]

def rawRow11401 : Integer.Sparse Key := [(key2862, -4), (key2816, -4), (key2713, -4), (key2812, -4), (key2709, -4), (key2678, -4), (key2816, 6), (key2713, 6), (key2687, 6), (key2678, 6)]

def rawRow11402 : Integer.Sparse Key := [(key2687, -4), (key2713, -4), (key2713, -4), (key2816, -4), (key2816, -4), (key2862, -4), (key2678, 6), (key2678, 6), (key2709, 6), (key2812, 6)]

def rawRow11403 : Integer.Sparse Key := [(key2713, -4), (key2687, -4), (key2713, -4), (key2816, -4), (key2862, -4), (key2816, -4), (key2678, 6), (key2709, 6), (key2678, 6), (key2812, 6)]

def rawRow11404 : Integer.Sparse Key := [(key2713, -4), (key2713, -4), (key2687, -4), (key2862, -4), (key2816, -4), (key2816, -4), (key2709, 6), (key2678, 6), (key2678, 6), (key2812, 6)]

def rawRow11405 : Integer.Sparse Key := [(key2687, -4), (key2816, -4), (key2816, -4), (key2713, -4), (key2713, -4), (key2862, -4), (key2678, 6), (key2678, 6), (key2812, 6), (key2709, 6)]

def rawRow11406 : Integer.Sparse Key := [(key2816, -4), (key2687, -4), (key2816, -4), (key2713, -4), (key2862, -4), (key2713, -4), (key2678, 6), (key2812, 6), (key2678, 6), (key2709, 6)]

def rawRow11407 : Integer.Sparse Key := [(key2816, -4), (key2816, -4), (key2687, -4), (key2862, -4), (key2713, -4), (key2713, -4), (key2812, 6), (key2678, 6), (key2678, 6), (key2709, 6)]

def rawRow11408 : Integer.Sparse Key := [(key2713, -4), (key2816, -4), (key2862, -4), (key2687, -4), (key2713, -4), (key2816, -4), (key2678, 6), (key2709, 6), (key2812, 6), (key2678, 6)]

def rawRow11409 : Integer.Sparse Key := [(key2713, -4), (key2862, -4), (key2816, -4), (key2713, -4), (key2687, -4), (key2816, -4), (key2709, 6), (key2678, 6), (key2812, 6), (key2678, 6)]

def rawRow11410 : Integer.Sparse Key := [(key2816, -4), (key2713, -4), (key2862, -4), (key2687, -4), (key2816, -4), (key2713, -4), (key2678, 6), (key2812, 6), (key2709, 6), (key2678, 6)]

def rawRow11411 : Integer.Sparse Key := [(key2816, -4), (key2862, -4), (key2713, -4), (key2816, -4), (key2687, -4), (key2713, -4), (key2812, 6), (key2678, 6), (key2709, 6), (key2678, 6)]

def rawRow11412 : Integer.Sparse Key := [(key2862, -4), (key2713, -4), (key2816, -4), (key2713, -4), (key2816, -4), (key2687, -4), (key2709, 6), (key2812, 6), (key2678, 6), (key2678, 6)]

def rawRow11413 : Integer.Sparse Key := [(key2862, -4), (key2816, -4), (key2713, -4), (key2816, -4), (key2713, -4), (key2687, -4), (key2812, 6), (key2709, 6), (key2678, 6), (key2678, 6)]

def rawRow11414 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1940, 6), (key1949, 6), (key1937, -24)]

def rawRow11415 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1940, 6), (key1949, 6), (key1937, -24)]

def rawRow11416 : Integer.Sparse Key := [(key1936, 6), (key1940, 6), (key1937, 6), (key1949, 6), (key1937, -24)]

def rawRow11417 : Integer.Sparse Key := [(key1940, 6), (key1936, 6), (key1937, 6), (key1949, 6), (key1937, -24)]

def rawRow11418 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1936, 6), (key1949, 6), (key1937, -24)]

def rawRow11419 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1936, 6), (key1949, 6), (key1937, -24)]

def rawRow11420 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1949, 6), (key1940, 6), (key1937, -24)]

def rawRow11421 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1949, 6), (key1940, 6), (key1937, -24)]

def rawRow11422 : Integer.Sparse Key := [(key1936, 6), (key1949, 6), (key1937, 6), (key1940, 6), (key1937, -24)]

def rawRow11423 : Integer.Sparse Key := [(key1949, 6), (key1936, 6), (key1937, 6), (key1940, 6), (key1937, -24)]

def rawRow11424 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1936, 6), (key1940, 6), (key1937, -24)]

def rawRow11425 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1936, 6), (key1940, 6), (key1937, -24)]

def rawRow11426 : Integer.Sparse Key := [(key1936, 6), (key1940, 6), (key1949, 6), (key1937, 6), (key1937, -24)]

def rawRow11427 : Integer.Sparse Key := [(key1940, 6), (key1936, 6), (key1949, 6), (key1937, 6), (key1937, -24)]

def rawRow11428 : Integer.Sparse Key := [(key1936, 6), (key1949, 6), (key1940, 6), (key1937, 6), (key1937, -24)]

def rawRow11429 : Integer.Sparse Key := [(key1949, 6), (key1936, 6), (key1940, 6), (key1937, 6), (key1937, -24)]

def rawRow11430 : Integer.Sparse Key := [(key1940, 6), (key1949, 6), (key1936, 6), (key1937, 6), (key1937, -24)]

def rawRow11431 : Integer.Sparse Key := [(key1949, 6), (key1940, 6), (key1936, 6), (key1937, 6), (key1937, -24)]

def rawRow11432 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1949, 6), (key1936, 6), (key1937, -24)]

def rawRow11433 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1949, 6), (key1936, 6), (key1937, -24)]

def rawRow11434 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1940, 6), (key1936, 6), (key1937, -24)]

def rawRow11435 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1940, 6), (key1936, 6), (key1937, -24)]

def rawRow11436 : Integer.Sparse Key := [(key1940, 6), (key1949, 6), (key1937, 6), (key1936, 6), (key1937, -24)]

def rawRow11437 : Integer.Sparse Key := [(key1949, 6), (key1940, 6), (key1937, 6), (key1936, 6), (key1937, -24)]

def rawRow11438 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1940, 6), (key1949, 6), (key1936, -24)]

def rawRow11439 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1937, 6), (key1949, 6), (key1936, -24)]

def rawRow11440 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1937, 6), (key1949, 6), (key1936, -24)]

def rawRow11441 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1949, 6), (key1940, 6), (key1936, -24)]

def rawRow11442 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1937, 6), (key1940, 6), (key1936, -24)]

def rawRow11443 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1937, 6), (key1940, 6), (key1936, -24)]

def rawRow11444 : Integer.Sparse Key := [(key1937, 6), (key1940, 6), (key1949, 6), (key1937, 6), (key1936, -24)]

def rawRow11445 : Integer.Sparse Key := [(key1940, 6), (key1937, 6), (key1949, 6), (key1937, 6), (key1936, -24)]

def rawRow11446 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1940, 6), (key1937, 6), (key1936, -24)]

def rawRow11447 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1940, 6), (key1937, 6), (key1936, -24)]

def rawRow11448 : Integer.Sparse Key := [(key1940, 6), (key1949, 6), (key1937, 6), (key1937, 6), (key1936, -24)]

def rawRow11449 : Integer.Sparse Key := [(key1949, 6), (key1940, 6), (key1937, 6), (key1937, 6), (key1936, -24)]

def rawRow11450 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1), (key2611, -2), (key2627, -2), (key2636, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2781, -2), (key2790, -2), (key2804, -2), (key2825, -2), (key2856, -2), (key2866, -2)]

def rawRow11451 : Integer.Sparse Key := [(key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2790, 1), (key2778, 1), (key2825, 1), (key2801, 1), (key2902, 1), (key2895, 1), (key2941, 1), (key2935, 1), (key2958, 1), (key2947, 1), (key2981, 1), (key2974, 1), (key2611, -2), (key2636, -2), (key2627, -2), (key2666, -2), (key2722, -2), (key2701, -2), (key2790, -2), (key2781, -2), (key2825, -2), (key2804, -2), (key2866, -2), (key2856, -2)]

def rawRow11452 : Integer.Sparse Key := [(key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2801, 1), (key2895, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2947, 1), (key2974, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2627, -2), (key2611, -2), (key2636, -2), (key2701, -2), (key2666, -2), (key2722, -2), (key2804, -2), (key2856, -2), (key2781, -2), (key2866, -2), (key2790, -2), (key2825, -2)]

def rawRow11453 : Integer.Sparse Key := [(key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2825, 1), (key2790, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2958, 1), (key2941, 1), (key2627, -2), (key2636, -2), (key2611, -2), (key2701, -2), (key2722, -2), (key2666, -2), (key2856, -2), (key2804, -2), (key2866, -2), (key2781, -2), (key2825, -2), (key2790, -2)]

def rawRow11454 : Integer.Sparse Key := [(key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2825, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2778, 1), (key2801, 1), (key2958, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2935, 1), (key2947, 1), (key2636, -2), (key2611, -2), (key2627, -2), (key2722, -2), (key2666, -2), (key2701, -2), (key2825, -2), (key2866, -2), (key2790, -2), (key2856, -2), (key2781, -2), (key2804, -2)]

def rawRow11455 : Integer.Sparse Key := [(key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2902, 1), (key2825, 1), (key2895, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2958, 1), (key2974, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2636, -2), (key2627, -2), (key2611, -2), (key2722, -2), (key2701, -2), (key2666, -2), (key2866, -2), (key2825, -2), (key2856, -2), (key2790, -2), (key2804, -2), (key2781, -2)]

def rawRow11456 : Integer.Sparse Key := [(key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1), (key2666, -2), (key2781, -2), (key2790, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2627, -2), (key2636, -2), (key2701, -2), (key2722, -2), (key2856, -2), (key2866, -2)]

def rawRow11457 : Integer.Sparse Key := [(key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1), (key2666, -2), (key2790, -2), (key2781, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2636, -2), (key2627, -2), (key2722, -2), (key2701, -2), (key2866, -2), (key2856, -2)]

def rawRow11458 : Integer.Sparse Key := [(key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2781, -2), (key2666, -2), (key2790, -2), (key2804, -2), (key2611, -2), (key2825, -2), (key2701, -2), (key2856, -2), (key2627, -2), (key2866, -2), (key2636, -2), (key2722, -2)]

def rawRow11459 : Integer.Sparse Key := [(key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1), (key2781, -2), (key2790, -2), (key2666, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2856, -2), (key2701, -2), (key2866, -2), (key2627, -2), (key2722, -2), (key2636, -2)]

def rawRow11460 : Integer.Sparse Key := [(key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1), (key2790, -2), (key2666, -2), (key2781, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2722, -2), (key2866, -2), (key2636, -2), (key2856, -2), (key2627, -2), (key2701, -2)]

def rawRow11461 : Integer.Sparse Key := [(key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2790, -2), (key2781, -2), (key2666, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2866, -2), (key2722, -2), (key2856, -2), (key2636, -2), (key2701, -2), (key2627, -2)]

def rawRow11462 : Integer.Sparse Key := [(key2778, 1), (key2790, 1), (key2801, 1), (key2895, 1), (key2825, 1), (key2902, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2974, 1), (key2722, 1), (key2981, 1), (key2608, 1), (key2651, 1), (key2663, 1), (key2745, 1), (key2941, 1), (key2958, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2722, 1), (key2790, 1), (key2825, 1), (key2701, -2), (key2804, -2), (key2856, -2), (key2627, -2), (key2781, -2), (key2866, -2), (key2611, -2), (key2636, -2), (key2666, -2), (key2722, -2), (key2790, -2), (key2825, -2)]

def rawRow11463 : Integer.Sparse Key := [(key2790, 1), (key2778, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2825, 1), (key2636, 1), (key2624, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2722, 1), (key2651, 1), (key2608, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2941, 1), (key2636, 1), (key2611, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2790, 1), (key2701, -2), (key2856, -2), (key2804, -2), (key2627, -2), (key2866, -2), (key2781, -2), (key2636, -2), (key2611, -2), (key2722, -2), (key2666, -2), (key2825, -2), (key2790, -2)]

def rawRow11464 : Integer.Sparse Key := [(key2801, 1), (key2825, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2698, 1), (key2722, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2663, 1), (key2745, 1), (key2608, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2666, 1), (key2790, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2804, -2), (key2701, -2), (key2856, -2), (key2781, -2), (key2627, -2), (key2866, -2), (key2666, -2), (key2790, -2), (key2611, -2), (key2825, -2), (key2636, -2), (key2722, -2)]

def rawRow11465 : Integer.Sparse Key := [(key2825, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2895, 1), (key2790, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2974, 1), (key2636, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2608, 1), (key2745, 1), (key2651, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2722, 1), (key2636, 1), (key2804, -2), (key2856, -2), (key2701, -2), (key2781, -2), (key2866, -2), (key2627, -2), (key2790, -2), (key2666, -2), (key2825, -2), (key2611, -2), (key2722, -2), (key2636, -2)]

def rawRow11466 : Integer.Sparse Key := [(key2895, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2778, 1), (key2801, 1), (key2974, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2624, 1), (key2698, 1), (key2941, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2608, 1), (key2663, 1), (key2722, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2611, 1), (key2666, 1), (key2856, -2), (key2701, -2), (key2804, -2), (key2866, -2), (key2627, -2), (key2781, -2), (key2722, -2), (key2825, -2), (key2636, -2), (key2790, -2), (key2611, -2), (key2666, -2)]

def rawRow11467 : Integer.Sparse Key := [(key2902, 1), (key2895, 1), (key2825, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2974, 1), (key2722, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2958, 1), (key2941, 1), (key2745, 1), (key2651, 1), (key2663, 1), (key2608, 1), (key2825, 1), (key2722, 1), (key2790, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2856, -2), (key2804, -2), (key2701, -2), (key2866, -2), (key2781, -2), (key2627, -2), (key2825, -2), (key2722, -2), (key2790, -2), (key2636, -2), (key2666, -2), (key2611, -2)]

def rawRow11468 : Integer.Sparse Key := [(key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1), (key2722, -2), (key2825, -2), (key2866, -2), (key2636, -2), (key2790, -2), (key2856, -2), (key2611, -2), (key2627, -2), (key2666, -2), (key2701, -2), (key2781, -2), (key2804, -2)]

def rawRow11469 : Integer.Sparse Key := [(key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1), (key2722, -2), (key2866, -2), (key2825, -2), (key2636, -2), (key2856, -2), (key2790, -2), (key2627, -2), (key2611, -2), (key2701, -2), (key2666, -2), (key2804, -2), (key2781, -2)]

def rawRow11470 : Integer.Sparse Key := [(key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2825, -2), (key2722, -2), (key2866, -2), (key2790, -2), (key2636, -2), (key2856, -2), (key2666, -2), (key2781, -2), (key2611, -2), (key2804, -2), (key2627, -2), (key2701, -2)]

def rawRow11471 : Integer.Sparse Key := [(key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1), (key2825, -2), (key2866, -2), (key2722, -2), (key2790, -2), (key2856, -2), (key2636, -2), (key2781, -2), (key2666, -2), (key2804, -2), (key2611, -2), (key2701, -2), (key2627, -2)]

def rawRow11472 : Integer.Sparse Key := [(key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1), (key2866, -2), (key2722, -2), (key2825, -2), (key2856, -2), (key2636, -2), (key2790, -2), (key2701, -2), (key2804, -2), (key2627, -2), (key2781, -2), (key2611, -2), (key2666, -2)]

def rawRow11473 : Integer.Sparse Key := [(key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1), (key2866, -2), (key2825, -2), (key2722, -2), (key2856, -2), (key2790, -2), (key2636, -2), (key2804, -2), (key2701, -2), (key2781, -2), (key2627, -2), (key2666, -2), (key2611, -2)]

def rawRow11474 : Integer.Sparse Key := [(key2611, 1), (key2611, 1), (key2627, 1), (key2627, 1), (key2636, 1), (key2636, 1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1), (key2701, 1), (key2701, 1), (key2804, 1), (key2804, 1), (key2856, 1), (key2856, 1), (key2722, 1), (key2722, 1), (key2825, 1), (key2825, 1), (key2866, 1), (key2866, 1), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2778, -2), (key2778, -2), (key2801, -2), (key2801, -2), (key2851, -2), (key2851, -2)]

def rawRow11475 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2611, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2804, 1), (key2856, 1), (key2701, 1), (key2856, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2866, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2825, 1), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2851, -2), (key2778, -2), (key2801, -2)]

def rawRow11476 : Integer.Sparse Key := [(key2636, 1), (key2627, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2611, 1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1), (key2856, 1), (key2804, 1), (key2856, 1), (key2701, 1), (key2804, 1), (key2701, 1), (key2866, 1), (key2825, 1), (key2866, 1), (key2722, 1), (key2825, 1), (key2722, 1), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2851, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2778, -2)]

def rawRow11477 : Integer.Sparse Key := [(key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2722, 1), (key2722, 1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2627, 1), (key2627, 1), (key2781, 1), (key2781, 1), (key2866, 1), (key2866, 1), (key2636, 1), (key2636, 1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, -2), (key2624, -2), (key2698, -2), (key2698, -2), (key2851, -2), (key2851, -2)]

def rawRow11478 : Integer.Sparse Key := [(key2701, 1), (key2722, 1), (key2666, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2781, 1), (key2866, 1), (key2627, 1), (key2866, 1), (key2627, 1), (key2781, 1), (key2790, 1), (key2856, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2790, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2851, -2), (key2624, -2), (key2698, -2)]

def rawRow11479 : Integer.Sparse Key := [(key2722, 1), (key2701, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2866, 1), (key2781, 1), (key2866, 1), (key2627, 1), (key2781, 1), (key2627, 1), (key2856, 1), (key2790, 1), (key2856, 1), (key2636, 1), (key2790, 1), (key2636, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2624, -2)]

def rawRow11480 : Integer.Sparse Key := [(key2781, 1), (key2790, 1), (key2804, 1), (key2856, 1), (key2825, 1), (key2866, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2611, 1), (key2627, 1), (key2666, 1), (key2781, 1), (key2701, 1), (key2804, 1), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2778, -2), (key2801, -2)]

def rawRow11481 : Integer.Sparse Key := [(key2790, 1), (key2781, 1), (key2856, 1), (key2804, 1), (key2866, 1), (key2825, 1), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2627, 1), (key2611, 1), (key2781, 1), (key2666, 1), (key2804, 1), (key2701, 1), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2778, -2)]

def rawRow11482 : Integer.Sparse Key := [(key2804, 1), (key2825, 1), (key2781, 1), (key2866, 1), (key2790, 1), (key2856, 1), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2666, 1), (key2701, 1), (key2611, 1), (key2804, 1), (key2627, 1), (key2781, 1), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2624, -2), (key2698, -2)]

def rawRow11483 : Integer.Sparse Key := [(key2825, 1), (key2804, 1), (key2866, 1), (key2781, 1), (key2856, 1), (key2790, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2701, 1), (key2666, 1), (key2804, 1), (key2611, 1), (key2781, 1), (key2627, 1), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2608, -2), (key2698, -2), (key2624, -2)]

def rawRow11484 : Integer.Sparse Key := [(key2856, 1), (key2866, 1), (key2790, 1), (key2825, 1), (key2781, 1), (key2804, 1), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2781, 1), (key2804, 1), (key2627, 1), (key2701, 1), (key2611, 1), (key2666, 1), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, -2), (key2801, -2), (key2624, -2), (key2698, -2), (key2608, -2), (key2663, -2)]

def rawRow11485 : Integer.Sparse Key := [(key2866, 1), (key2856, 1), (key2825, 1), (key2790, 1), (key2804, 1), (key2781, 1), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2804, 1), (key2781, 1), (key2701, 1), (key2627, 1), (key2666, 1), (key2611, 1), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, -2), (key2778, -2), (key2698, -2), (key2624, -2), (key2663, -2), (key2608, -2)]

def rawRow11486 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2381, 2), (key2472, 2), (key2472, 2), (key2538, 2), (key2503, 2), (key2506, 2), (key2503, 2), (key2554, 2), (key2506, 2), (key2554, 2), (key2390, -2), (key2392, -2), (key2392, -2), (key2480, -2), (key2482, -2), (key2480, -2), (key2543, -2), (key2482, -2), (key2543, -2), (key2522, -2), (key2522, -2), (key2563, -2)]

def rawRow11487 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2378, 2), (key2472, 2), (key2538, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2554, 2), (key2503, 2), (key2554, 2), (key2506, 2), (key2392, -2), (key2390, -2), (key2392, -2), (key2482, -2), (key2480, -2), (key2543, -2), (key2480, -2), (key2543, -2), (key2482, -2), (key2522, -2), (key2563, -2), (key2522, -2)]

def rawRow11488 : Integer.Sparse Key := [(key2381, 2), (key2378, 2), (key2378, 2), (key2538, 2), (key2472, 2), (key2472, 2), (key2554, 2), (key2554, 2), (key2506, 2), (key2506, 2), (key2503, 2), (key2503, 2), (key2392, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2543, -2), (key2482, -2), (key2482, -2), (key2480, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2522, -2)]

def rawRow11489 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2506, 2), (key2378, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2381, 2), (key2472, 2), (key2538, 2), (key2506, 2), (key2554, 2), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2392, -2), (key2482, -2), (key2543, -2)]

def rawRow11490 : Integer.Sparse Key := [(key2472, 2), (key2506, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2503, 2), (key2381, 2), (key2378, 2), (key2538, 2), (key2472, 2), (key2554, 2), (key2506, 2), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2392, -2), (key2543, -2), (key2482, -2)]

def rawRow11491 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2472, 2), (key2506, 2), (key2378, 2), (key2554, 2), (key2381, 2), (key2538, 2), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2482, -2), (key2392, -2), (key2543, -2)]

def rawRow11492 : Integer.Sparse Key := [(key2503, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2506, 2), (key2472, 2), (key2554, 2), (key2378, 2), (key2538, 2), (key2381, 2), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2482, -2), (key2543, -2), (key2392, -2)]

def rawRow11493 : Integer.Sparse Key := [(key2506, 2), (key2472, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2503, 2), (key2538, 2), (key2554, 2), (key2381, 2), (key2506, 2), (key2378, 2), (key2472, 2), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2543, -2), (key2392, -2), (key2482, -2)]

def rawRow11494 : Integer.Sparse Key := [(key2506, 2), (key2503, 2), (key2472, 2), (key2554, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2538, 2), (key2506, 2), (key2381, 2), (key2472, 2), (key2378, 2), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2543, -2), (key2482, -2), (key2392, -2)]

def rawRow11495 : Integer.Sparse Key := [(key2538, 2), (key2554, 2), (key2554, 2), (key2381, 2), (key2506, 2), (key2506, 2), (key2378, 2), (key2378, 2), (key2472, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

def rawRow11496 : Integer.Sparse Key := [(key2554, 2), (key2538, 2), (key2554, 2), (key2506, 2), (key2381, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

def rawRow11497 : Integer.Sparse Key := [(key2554, 2), (key2554, 2), (key2538, 2), (key2506, 2), (key2506, 2), (key2381, 2), (key2503, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2378, 2), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

def rawRow11498 : Integer.Sparse Key := [(key1025, -24), (key990, 6), (key1103, 6), (key1103, 6), (key1187, 6)]

def rawRow11499 : Integer.Sparse Key := [(key1025, -24), (key990, 6), (key1103, 6), (key1187, 6), (key1103, 6)]

def rawRow11500 : Integer.Sparse Key := [(key1025, -24), (key990, 6), (key1187, 6), (key1103, 6), (key1103, 6)]

def rawRow11501 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key990, 6), (key1103, 6), (key1187, 6)]

def rawRow11502 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key990, 6), (key1187, 6), (key1103, 6)]

def rawRow11503 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1103, 6), (key990, 6), (key1187, 6)]

def rawRow11504 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1103, 6), (key1187, 6), (key990, 6)]

def rawRow11505 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1187, 6), (key990, 6), (key1103, 6)]

def rawRow11506 : Integer.Sparse Key := [(key1025, -24), (key1103, 6), (key1187, 6), (key1103, 6), (key990, 6)]

def rawRow11507 : Integer.Sparse Key := [(key1025, -24), (key1187, 6), (key990, 6), (key1103, 6), (key1103, 6)]

def rawRow11508 : Integer.Sparse Key := [(key1025, -24), (key1187, 6), (key1103, 6), (key990, 6), (key1103, 6)]

def rawRow11509 : Integer.Sparse Key := [(key1025, -24), (key1187, 6), (key1103, 6), (key1103, 6), (key990, 6)]

def rawRow11510 : Integer.Sparse Key := [(key1029, -6), (key1034, -6), (key1034, -6), (key1069, -6), (key994, 2), (key999, 2), (key999, 2), (key1107, 2), (key1112, 2), (key1107, 2), (key1191, 2), (key1112, 2), (key1191, 2), (key1148, 2), (key1148, 2), (key1210, 2)]

def rawRow11511 : Integer.Sparse Key := [(key1034, -6), (key1029, -6), (key1034, -6), (key1069, -6), (key999, 2), (key994, 2), (key999, 2), (key1112, 2), (key1107, 2), (key1191, 2), (key1107, 2), (key1191, 2), (key1112, 2), (key1148, 2), (key1210, 2), (key1148, 2)]

def rawRow11512 : Integer.Sparse Key := [(key1034, -6), (key1034, -6), (key1029, -6), (key1069, -6), (key999, 2), (key999, 2), (key994, 2), (key1191, 2), (key1191, 2), (key1112, 2), (key1112, 2), (key1107, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key1148, 2)]

def rawRow11513 : Integer.Sparse Key := [(key1029, -6), (key1034, -6), (key1069, -6), (key1034, -6), (key1107, 2), (key1112, 2), (key1148, 2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key999, 2), (key1112, 2), (key1191, 2)]

def rawRow11514 : Integer.Sparse Key := [(key1034, -6), (key1029, -6), (key1069, -6), (key1034, -6), (key1112, 2), (key1107, 2), (key1148, 2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key999, 2), (key1191, 2), (key1112, 2)]

def rawRow11515 : Integer.Sparse Key := [(key1029, -6), (key1069, -6), (key1034, -6), (key1034, -6), (key1107, 2), (key1148, 2), (key1112, 2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1112, 2), (key999, 2), (key1191, 2)]

def rawRow11516 : Integer.Sparse Key := [(key1069, -6), (key1029, -6), (key1034, -6), (key1034, -6), (key1148, 2), (key1107, 2), (key1112, 2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1112, 2), (key1191, 2), (key999, 2)]

def rawRow11517 : Integer.Sparse Key := [(key1034, -6), (key1069, -6), (key1029, -6), (key1034, -6), (key1112, 2), (key1148, 2), (key1107, 2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1191, 2), (key999, 2), (key1112, 2)]

def rawRow11518 : Integer.Sparse Key := [(key1069, -6), (key1034, -6), (key1029, -6), (key1034, -6), (key1148, 2), (key1112, 2), (key1107, 2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1191, 2), (key1112, 2), (key999, 2)]

def rawRow11519 : Integer.Sparse Key := [(key1034, -6), (key1034, -6), (key1069, -6), (key1029, -6), (key1191, 2), (key1191, 2), (key1210, 2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1107, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11520 : Integer.Sparse Key := [(key1034, -6), (key1069, -6), (key1034, -6), (key1029, -6), (key1191, 2), (key1210, 2), (key1191, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1107, 2), (key994, 2), (key1107, 2)]

def rawRow11521 : Integer.Sparse Key := [(key1069, -6), (key1034, -6), (key1034, -6), (key1029, -6), (key1210, 2), (key1191, 2), (key1191, 2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1107, 2), (key1107, 2), (key994, 2)]

def rawRow11522 : Integer.Sparse Key := [(key2607, -6), (key2800, -6), (key2800, -6), (key2823, -6), (key2623, 2), (key2623, 2), (key2634, 2), (key2697, 2), (key2697, 2), (key2720, 2), (key2850, 2), (key2854, 2), (key2850, 2), (key2864, 2), (key2854, 2), (key2864, 2)]

def rawRow11523 : Integer.Sparse Key := [(key2607, -6), (key2800, -6), (key2823, -6), (key2800, -6), (key2623, 2), (key2634, 2), (key2623, 2), (key2697, 2), (key2720, 2), (key2697, 2), (key2854, 2), (key2850, 2), (key2864, 2), (key2850, 2), (key2864, 2), (key2854, 2)]

def rawRow11524 : Integer.Sparse Key := [(key2607, -6), (key2823, -6), (key2800, -6), (key2800, -6), (key2634, 2), (key2623, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2697, 2), (key2864, 2), (key2864, 2), (key2854, 2), (key2854, 2), (key2850, 2), (key2850, 2)]

def rawRow11525 : Integer.Sparse Key := [(key2800, -6), (key2607, -6), (key2800, -6), (key2823, -6), (key2697, 2), (key2850, 2), (key2854, 2), (key2623, 2), (key2850, 2), (key2864, 2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

def rawRow11526 : Integer.Sparse Key := [(key2800, -6), (key2607, -6), (key2823, -6), (key2800, -6), (key2697, 2), (key2854, 2), (key2850, 2), (key2623, 2), (key2864, 2), (key2850, 2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

def rawRow11527 : Integer.Sparse Key := [(key2800, -6), (key2800, -6), (key2607, -6), (key2823, -6), (key2850, 2), (key2697, 2), (key2854, 2), (key2850, 2), (key2623, 2), (key2864, 2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

def rawRow11528 : Integer.Sparse Key := [(key2800, -6), (key2800, -6), (key2823, -6), (key2607, -6), (key2850, 2), (key2854, 2), (key2697, 2), (key2850, 2), (key2864, 2), (key2623, 2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

def rawRow11529 : Integer.Sparse Key := [(key2800, -6), (key2823, -6), (key2607, -6), (key2800, -6), (key2854, 2), (key2697, 2), (key2850, 2), (key2864, 2), (key2623, 2), (key2850, 2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

def rawRow11530 : Integer.Sparse Key := [(key2800, -6), (key2823, -6), (key2800, -6), (key2607, -6), (key2854, 2), (key2850, 2), (key2697, 2), (key2864, 2), (key2850, 2), (key2623, 2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

def rawRow11531 : Integer.Sparse Key := [(key2823, -6), (key2607, -6), (key2800, -6), (key2800, -6), (key2720, 2), (key2864, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2854, 2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

def rawRow11532 : Integer.Sparse Key := [(key2823, -6), (key2800, -6), (key2607, -6), (key2800, -6), (key2864, 2), (key2720, 2), (key2864, 2), (key2854, 2), (key2634, 2), (key2854, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

def rawRow11533 : Integer.Sparse Key := [(key2823, -6), (key2800, -6), (key2800, -6), (key2607, -6), (key2864, 2), (key2864, 2), (key2720, 2), (key2854, 2), (key2854, 2), (key2634, 2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

def rawRow11534 : Integer.Sparse Key := [(key2399, -6), (key2403, -6), (key2403, -6), (key2434, -6), (key2371, 2), (key2375, 2), (key2375, 2), (key2465, 2), (key2469, 2), (key2465, 2), (key2536, 2), (key2469, 2), (key2536, 2), (key2500, 2), (key2500, 2), (key2552, 2)]

def rawRow11535 : Integer.Sparse Key := [(key2403, -6), (key2399, -6), (key2403, -6), (key2434, -6), (key2375, 2), (key2371, 2), (key2375, 2), (key2469, 2), (key2465, 2), (key2536, 2), (key2465, 2), (key2536, 2), (key2469, 2), (key2500, 2), (key2552, 2), (key2500, 2)]

def rawRow11536 : Integer.Sparse Key := [(key2403, -6), (key2403, -6), (key2399, -6), (key2434, -6), (key2375, 2), (key2375, 2), (key2371, 2), (key2536, 2), (key2536, 2), (key2469, 2), (key2469, 2), (key2465, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2500, 2)]

def rawRow11537 : Integer.Sparse Key := [(key2399, -6), (key2403, -6), (key2434, -6), (key2403, -6), (key2465, 2), (key2469, 2), (key2500, 2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2375, 2), (key2469, 2), (key2536, 2)]

def rawRow11538 : Integer.Sparse Key := [(key2403, -6), (key2399, -6), (key2434, -6), (key2403, -6), (key2469, 2), (key2465, 2), (key2500, 2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2375, 2), (key2536, 2), (key2469, 2)]

def rawRow11539 : Integer.Sparse Key := [(key2399, -6), (key2434, -6), (key2403, -6), (key2403, -6), (key2465, 2), (key2500, 2), (key2469, 2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2469, 2), (key2375, 2), (key2536, 2)]

def rawRow11540 : Integer.Sparse Key := [(key2434, -6), (key2399, -6), (key2403, -6), (key2403, -6), (key2500, 2), (key2465, 2), (key2469, 2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2469, 2), (key2536, 2), (key2375, 2)]

def rawRow11541 : Integer.Sparse Key := [(key2403, -6), (key2434, -6), (key2399, -6), (key2403, -6), (key2469, 2), (key2500, 2), (key2465, 2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2536, 2), (key2375, 2), (key2469, 2)]

def rawRow11542 : Integer.Sparse Key := [(key2434, -6), (key2403, -6), (key2399, -6), (key2403, -6), (key2500, 2), (key2469, 2), (key2465, 2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2536, 2), (key2469, 2), (key2375, 2)]

def rawRow11543 : Integer.Sparse Key := [(key2403, -6), (key2403, -6), (key2434, -6), (key2399, -6), (key2536, 2), (key2536, 2), (key2552, 2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2465, 2)]

def rawRow11544 : Integer.Sparse Key := [(key2403, -6), (key2434, -6), (key2403, -6), (key2399, -6), (key2536, 2), (key2552, 2), (key2536, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2465, 2), (key2371, 2), (key2465, 2)]

def rawRow11545 : Integer.Sparse Key := [(key2434, -6), (key2403, -6), (key2403, -6), (key2399, -6), (key2552, 2), (key2536, 2), (key2536, 2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2465, 2), (key2465, 2), (key2371, 2)]

def rawRow11546 : Integer.Sparse Key := [(key2609, -2), (key2613, -2), (key2613, -2), (key2802, -2), (key2806, -2), (key2802, -2), (key2949, -2), (key2806, -2), (key2949, -2), (key2826, -2), (key2826, -2), (key2959, -2), (key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2852, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2973, 1), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1)]

def rawRow11547 : Integer.Sparse Key := [(key2613, -2), (key2609, -2), (key2613, -2), (key2806, -2), (key2802, -2), (key2949, -2), (key2802, -2), (key2949, -2), (key2806, -2), (key2826, -2), (key2959, -2), (key2826, -2), (key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1)]

def rawRow11548 : Integer.Sparse Key := [(key2613, -2), (key2613, -2), (key2609, -2), (key2949, -2), (key2949, -2), (key2806, -2), (key2806, -2), (key2802, -2), (key2802, -2), (key2959, -2), (key2826, -2), (key2826, -2), (key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2973, 1), (key2973, 1), (key2894, 1), (key2894, 1), (key2852, 1), (key2852, 1), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1)]

def rawRow11549 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2609, -2), (key2613, -2), (key2802, -2), (key2949, -2), (key2826, -2), (key2959, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1)]

def rawRow11550 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2613, -2), (key2609, -2), (key2949, -2), (key2802, -2), (key2959, -2), (key2826, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1)]

def rawRow11551 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2802, -2), (key2826, -2), (key2609, -2), (key2959, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2949, -2), (key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1)]

def rawRow11552 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2802, -2), (key2959, -2), (key2609, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2613, -2), (key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1)]

def rawRow11553 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2949, -2), (key2959, -2), (key2613, -2), (key2826, -2), (key2609, -2), (key2802, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1)]

def rawRow11554 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2959, -2), (key2949, -2), (key2826, -2), (key2613, -2), (key2802, -2), (key2609, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

def rawRow11555 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2613, -2), (key2613, -2), (key2806, -2), (key2806, -2), (key2826, -2), (key2826, -2), (key2609, -2), (key2802, -2), (key2802, -2), (key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1)]

def rawRow11556 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2806, -2), (key2826, -2), (key2613, -2), (key2826, -2), (key2613, -2), (key2806, -2), (key2802, -2), (key2609, -2), (key2802, -2), (key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1)]

def rawRow11557 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2826, -2), (key2806, -2), (key2826, -2), (key2613, -2), (key2806, -2), (key2613, -2), (key2802, -2), (key2802, -2), (key2609, -2), (key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1)]

def rawRow11558 : Integer.Sparse Key := [(key2761, -24), (key2582, 6), (key2838, 6), (key2838, 6), (key2872, 6)]

def rawRow11559 : Integer.Sparse Key := [(key2761, -24), (key2582, 6), (key2838, 6), (key2872, 6), (key2838, 6)]

def rawRow11560 : Integer.Sparse Key := [(key2761, -24), (key2582, 6), (key2872, 6), (key2838, 6), (key2838, 6)]

def rawRow11561 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2582, 6), (key2838, 6), (key2872, 6)]

def rawRow11562 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2582, 6), (key2872, 6), (key2838, 6)]

def rawRow11563 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2838, 6), (key2582, 6), (key2872, 6)]

def rawRow11564 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2838, 6), (key2872, 6), (key2582, 6)]

def rawRow11565 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2872, 6), (key2582, 6), (key2838, 6)]

def rawRow11566 : Integer.Sparse Key := [(key2761, -24), (key2838, 6), (key2872, 6), (key2838, 6), (key2582, 6)]

def rawRow11567 : Integer.Sparse Key := [(key2761, -24), (key2872, 6), (key2582, 6), (key2838, 6), (key2838, 6)]

def rawRow11568 : Integer.Sparse Key := [(key2761, -24), (key2872, 6), (key2838, 6), (key2582, 6), (key2838, 6)]

def rawRow11569 : Integer.Sparse Key := [(key2761, -24), (key2872, 6), (key2838, 6), (key2838, 6), (key2582, 6)]

def rawRow11570 : Integer.Sparse Key := [(key2664, -2), (key2668, -2), (key2668, -2), (key2699, -2), (key2703, -2), (key2699, -2), (key2736, -2), (key2703, -2), (key2736, -2), (key2723, -2), (key2723, -2), (key2746, -2), (key2609, 2), (key2613, 2), (key2613, 2), (key2802, 2), (key2806, 2), (key2802, 2), (key2949, 2), (key2806, 2), (key2949, 2), (key2826, 2), (key2826, 2), (key2959, 2)]

def rawRow11571 : Integer.Sparse Key := [(key2668, -2), (key2664, -2), (key2668, -2), (key2703, -2), (key2699, -2), (key2736, -2), (key2699, -2), (key2736, -2), (key2703, -2), (key2723, -2), (key2746, -2), (key2723, -2), (key2613, 2), (key2609, 2), (key2613, 2), (key2806, 2), (key2802, 2), (key2949, 2), (key2802, 2), (key2949, 2), (key2806, 2), (key2826, 2), (key2959, 2), (key2826, 2)]

def rawRow11572 : Integer.Sparse Key := [(key2668, -2), (key2668, -2), (key2664, -2), (key2736, -2), (key2736, -2), (key2703, -2), (key2703, -2), (key2699, -2), (key2699, -2), (key2746, -2), (key2723, -2), (key2723, -2), (key2613, 2), (key2613, 2), (key2609, 2), (key2949, 2), (key2949, 2), (key2806, 2), (key2806, 2), (key2802, 2), (key2802, 2), (key2959, 2), (key2826, 2), (key2826, 2)]

def rawRow11573 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2664, -2), (key2668, -2), (key2699, -2), (key2736, -2), (key2723, -2), (key2746, -2), (key2668, -2), (key2703, -2), (key2736, -2), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, 2), (key2613, 2), (key2802, 2), (key2949, 2), (key2826, 2), (key2959, 2), (key2613, 2), (key2806, 2), (key2949, 2)]

def rawRow11574 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2668, -2), (key2664, -2), (key2736, -2), (key2699, -2), (key2746, -2), (key2723, -2), (key2668, -2), (key2736, -2), (key2703, -2), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, 2), (key2609, 2), (key2949, 2), (key2802, 2), (key2959, 2), (key2826, 2), (key2613, 2), (key2949, 2), (key2806, 2)]

def rawRow11575 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2699, -2), (key2723, -2), (key2664, -2), (key2746, -2), (key2668, -2), (key2736, -2), (key2703, -2), (key2668, -2), (key2736, -2), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, 2), (key2826, 2), (key2609, 2), (key2959, 2), (key2613, 2), (key2949, 2), (key2806, 2), (key2613, 2), (key2949, 2)]

def rawRow11576 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2723, -2), (key2699, -2), (key2746, -2), (key2664, -2), (key2736, -2), (key2668, -2), (key2703, -2), (key2736, -2), (key2668, -2), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, 2), (key2802, 2), (key2959, 2), (key2609, 2), (key2949, 2), (key2613, 2), (key2806, 2), (key2949, 2), (key2613, 2)]

def rawRow11577 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2736, -2), (key2746, -2), (key2668, -2), (key2723, -2), (key2664, -2), (key2699, -2), (key2736, -2), (key2668, -2), (key2703, -2), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, 2), (key2959, 2), (key2613, 2), (key2826, 2), (key2609, 2), (key2802, 2), (key2949, 2), (key2613, 2), (key2806, 2)]

def rawRow11578 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2746, -2), (key2736, -2), (key2723, -2), (key2668, -2), (key2699, -2), (key2664, -2), (key2736, -2), (key2703, -2), (key2668, -2), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, 2), (key2949, 2), (key2826, 2), (key2613, 2), (key2802, 2), (key2609, 2), (key2949, 2), (key2806, 2), (key2613, 2)]

def rawRow11579 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2668, -2), (key2668, -2), (key2703, -2), (key2703, -2), (key2723, -2), (key2723, -2), (key2664, -2), (key2699, -2), (key2699, -2), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, 2), (key2613, 2), (key2806, 2), (key2806, 2), (key2826, 2), (key2826, 2), (key2609, 2), (key2802, 2), (key2802, 2)]

def rawRow11580 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2703, -2), (key2723, -2), (key2668, -2), (key2723, -2), (key2668, -2), (key2703, -2), (key2699, -2), (key2664, -2), (key2699, -2), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, 2), (key2826, 2), (key2613, 2), (key2826, 2), (key2613, 2), (key2806, 2), (key2802, 2), (key2609, 2), (key2802, 2)]

def rawRow11581 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2723, -2), (key2703, -2), (key2723, -2), (key2668, -2), (key2703, -2), (key2668, -2), (key2699, -2), (key2699, -2), (key2664, -2), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, 2), (key2806, 2), (key2826, 2), (key2613, 2), (key2806, 2), (key2613, 2), (key2802, 2), (key2802, 2), (key2609, 2)]

def rawRow11582 : Integer.Sparse Key := [(key1292, -2), (key1297, -2), (key1297, -2), (key1569, -2), (key1574, -2), (key1569, -2), (key1789, -2), (key1574, -2), (key1789, -2), (key1592, -2), (key1592, -2), (key1797, -2), (key1312, 1), (key1317, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1338, 1), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1), (key1618, 1), (key1656, 1), (key1618, 1), (key1814, 1), (key1656, 1), (key1814, 1), (key1632, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1666, 1), (key1824, 1)]

def rawRow11583 : Integer.Sparse Key := [(key1297, -2), (key1292, -2), (key1297, -2), (key1574, -2), (key1569, -2), (key1789, -2), (key1569, -2), (key1789, -2), (key1574, -2), (key1592, -2), (key1797, -2), (key1592, -2), (key1317, 1), (key1312, 1), (key1338, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1656, 1), (key1618, 1), (key1814, 1), (key1618, 1), (key1814, 1), (key1656, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1632, 1), (key1824, 1), (key1666, 1)]

def rawRow11584 : Integer.Sparse Key := [(key1297, -2), (key1297, -2), (key1292, -2), (key1789, -2), (key1789, -2), (key1574, -2), (key1574, -2), (key1569, -2), (key1569, -2), (key1797, -2), (key1592, -2), (key1592, -2), (key1338, 1), (key1338, 1), (key1317, 1), (key1317, 1), (key1312, 1), (key1312, 1), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1), (key1814, 1), (key1814, 1), (key1656, 1), (key1656, 1), (key1618, 1), (key1618, 1), (key1824, 1), (key1824, 1), (key1666, 1), (key1666, 1), (key1632, 1), (key1632, 1)]

def rawRow11585 : Integer.Sparse Key := [(key1569, -2), (key1574, -2), (key1592, -2), (key1292, -2), (key1297, -2), (key1569, -2), (key1789, -2), (key1592, -2), (key1797, -2), (key1297, -2), (key1574, -2), (key1789, -2), (key1542, 1), (key1547, 1), (key1618, 1), (key1656, 1), (key1632, 1), (key1666, 1), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1), (key1312, 1), (key1338, 1), (key1542, 1), (key1773, 1), (key1666, 1), (key1824, 1), (key1317, 1), (key1338, 1), (key1547, 1), (key1773, 1), (key1656, 1), (key1814, 1)]

def rawRow11586 : Integer.Sparse Key := [(key1574, -2), (key1569, -2), (key1592, -2), (key1297, -2), (key1292, -2), (key1789, -2), (key1569, -2), (key1797, -2), (key1592, -2), (key1297, -2), (key1789, -2), (key1574, -2), (key1547, 1), (key1542, 1), (key1656, 1), (key1618, 1), (key1666, 1), (key1632, 1), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1), (key1338, 1), (key1312, 1), (key1773, 1), (key1542, 1), (key1824, 1), (key1666, 1), (key1338, 1), (key1317, 1), (key1773, 1), (key1547, 1), (key1814, 1), (key1656, 1)]

def rawRow11587 : Integer.Sparse Key := [(key1569, -2), (key1592, -2), (key1574, -2), (key1569, -2), (key1592, -2), (key1292, -2), (key1797, -2), (key1297, -2), (key1789, -2), (key1574, -2), (key1297, -2), (key1789, -2), (key1618, 1), (key1632, 1), (key1542, 1), (key1666, 1), (key1547, 1), (key1656, 1), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1), (key1542, 1), (key1666, 1), (key1312, 1), (key1824, 1), (key1338, 1), (key1773, 1), (key1547, 1), (key1656, 1), (key1317, 1), (key1814, 1), (key1338, 1), (key1773, 1)]

def rawRow11588 : Integer.Sparse Key := [(key1592, -2), (key1569, -2), (key1574, -2), (key1592, -2), (key1569, -2), (key1797, -2), (key1292, -2), (key1789, -2), (key1297, -2), (key1574, -2), (key1789, -2), (key1297, -2), (key1632, 1), (key1618, 1), (key1666, 1), (key1542, 1), (key1656, 1), (key1547, 1), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1), (key1666, 1), (key1542, 1), (key1824, 1), (key1312, 1), (key1773, 1), (key1338, 1), (key1656, 1), (key1547, 1), (key1814, 1), (key1317, 1), (key1773, 1), (key1338, 1)]

def rawRow11589 : Integer.Sparse Key := [(key1574, -2), (key1592, -2), (key1569, -2), (key1789, -2), (key1797, -2), (key1297, -2), (key1592, -2), (key1292, -2), (key1569, -2), (key1789, -2), (key1297, -2), (key1574, -2), (key1656, 1), (key1666, 1), (key1547, 1), (key1632, 1), (key1542, 1), (key1618, 1), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1), (key1773, 1), (key1824, 1), (key1338, 1), (key1666, 1), (key1312, 1), (key1542, 1), (key1773, 1), (key1814, 1), (key1338, 1), (key1656, 1), (key1317, 1), (key1547, 1)]

def rawRow11590 : Integer.Sparse Key := [(key1592, -2), (key1574, -2), (key1569, -2), (key1797, -2), (key1789, -2), (key1592, -2), (key1297, -2), (key1569, -2), (key1292, -2), (key1789, -2), (key1574, -2), (key1297, -2), (key1666, 1), (key1656, 1), (key1632, 1), (key1547, 1), (key1618, 1), (key1542, 1), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1), (key1824, 1), (key1773, 1), (key1666, 1), (key1338, 1), (key1542, 1), (key1312, 1), (key1814, 1), (key1773, 1), (key1656, 1), (key1338, 1), (key1547, 1), (key1317, 1)]

def rawRow11591 : Integer.Sparse Key := [(key1789, -2), (key1789, -2), (key1797, -2), (key1297, -2), (key1297, -2), (key1574, -2), (key1574, -2), (key1592, -2), (key1592, -2), (key1292, -2), (key1569, -2), (key1569, -2), (key1773, 1), (key1773, 1), (key1814, 1), (key1814, 1), (key1824, 1), (key1824, 1), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1), (key1317, 1), (key1317, 1), (key1547, 1), (key1547, 1), (key1632, 1), (key1632, 1), (key1312, 1), (key1312, 1), (key1542, 1), (key1542, 1), (key1618, 1), (key1618, 1)]

def rawRow11592 : Integer.Sparse Key := [(key1789, -2), (key1797, -2), (key1789, -2), (key1574, -2), (key1592, -2), (key1297, -2), (key1592, -2), (key1297, -2), (key1574, -2), (key1569, -2), (key1292, -2), (key1569, -2), (key1814, 1), (key1824, 1), (key1773, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1542, 1)]

def rawRow11593 : Integer.Sparse Key := [(key1797, -2), (key1789, -2), (key1789, -2), (key1592, -2), (key1574, -2), (key1592, -2), (key1297, -2), (key1574, -2), (key1297, -2), (key1569, -2), (key1569, -2), (key1292, -2), (key1824, 1), (key1814, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1773, 1), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1), (key1632, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1317, 1), (key1618, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1542, 1), (key1312, 1)]

def rawRow11594 : Integer.Sparse Key := [(key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2852, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2973, 1), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1), (key2637, -2), (key2637, -2), (key2652, -2), (key2791, -2), (key2791, -2), (key2942, -2), (key2857, -2), (key2896, -2), (key2857, -2), (key2975, -2), (key2896, -2), (key2975, -2)]

def rawRow11595 : Integer.Sparse Key := [(key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2637, -2), (key2652, -2), (key2637, -2), (key2791, -2), (key2942, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2975, -2), (key2857, -2), (key2975, -2), (key2896, -2)]

def rawRow11596 : Integer.Sparse Key := [(key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2973, 1), (key2973, 1), (key2894, 1), (key2894, 1), (key2852, 1), (key2852, 1), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1), (key2652, -2), (key2637, -2), (key2637, -2), (key2942, -2), (key2791, -2), (key2791, -2), (key2975, -2), (key2975, -2), (key2896, -2), (key2896, -2), (key2857, -2), (key2857, -2)]

def rawRow11597 : Integer.Sparse Key := [(key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1), (key2791, -2), (key2857, -2), (key2896, -2), (key2637, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2652, -2), (key2791, -2), (key2942, -2), (key2896, -2), (key2975, -2)]

def rawRow11598 : Integer.Sparse Key := [(key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1), (key2791, -2), (key2896, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2857, -2), (key2652, -2), (key2637, -2), (key2942, -2), (key2791, -2), (key2975, -2), (key2896, -2)]

def rawRow11599 : Integer.Sparse Key := [(key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1), (key2857, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2791, -2), (key2896, -2), (key2637, -2), (key2975, -2), (key2652, -2), (key2942, -2)]

def rawRow11600 : Integer.Sparse Key := [(key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1), (key2857, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2896, -2), (key2791, -2), (key2975, -2), (key2637, -2), (key2942, -2), (key2652, -2)]

def rawRow11601 : Integer.Sparse Key := [(key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1), (key2896, -2), (key2791, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2857, -2), (key2942, -2), (key2975, -2), (key2652, -2), (key2896, -2), (key2637, -2), (key2791, -2)]

def rawRow11602 : Integer.Sparse Key := [(key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1), (key2896, -2), (key2857, -2), (key2791, -2), (key2975, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2942, -2), (key2896, -2), (key2652, -2), (key2791, -2), (key2637, -2)]

def rawRow11603 : Integer.Sparse Key := [(key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1), (key2942, -2), (key2975, -2), (key2975, -2), (key2652, -2), (key2896, -2), (key2896, -2), (key2637, -2), (key2637, -2), (key2791, -2), (key2791, -2), (key2857, -2), (key2857, -2)]

def rawRow11604 : Integer.Sparse Key := [(key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2975, -2), (key2942, -2), (key2975, -2), (key2896, -2), (key2652, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2637, -2), (key2857, -2), (key2637, -2), (key2791, -2)]

def rawRow11605 : Integer.Sparse Key := [(key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1), (key2975, -2), (key2975, -2), (key2942, -2), (key2896, -2), (key2896, -2), (key2652, -2), (key2857, -2), (key2791, -2), (key2857, -2), (key2637, -2), (key2791, -2), (key2637, -2)]

def rawRow11606 : Integer.Sparse Key := [(key1288, -6), (key1565, -6), (key1565, -6), (key1785, -6), (key1308, 2), (key1308, 2), (key1334, 2), (key1538, 2), (key1538, 2), (key1769, 2), (key1614, 2), (key1652, 2), (key1614, 2), (key1810, 2), (key1652, 2), (key1810, 2)]

def rawRow11607 : Integer.Sparse Key := [(key1288, -6), (key1565, -6), (key1785, -6), (key1565, -6), (key1308, 2), (key1334, 2), (key1308, 2), (key1538, 2), (key1769, 2), (key1538, 2), (key1652, 2), (key1614, 2), (key1810, 2), (key1614, 2), (key1810, 2), (key1652, 2)]

def rawRow11608 : Integer.Sparse Key := [(key1288, -6), (key1785, -6), (key1565, -6), (key1565, -6), (key1334, 2), (key1308, 2), (key1308, 2), (key1769, 2), (key1538, 2), (key1538, 2), (key1810, 2), (key1810, 2), (key1652, 2), (key1652, 2), (key1614, 2), (key1614, 2)]

def rawRow11609 : Integer.Sparse Key := [(key1565, -6), (key1288, -6), (key1565, -6), (key1785, -6), (key1538, 2), (key1614, 2), (key1652, 2), (key1308, 2), (key1614, 2), (key1810, 2), (key1308, 2), (key1334, 2), (key1538, 2), (key1769, 2), (key1652, 2), (key1810, 2)]

def rawRow11610 : Integer.Sparse Key := [(key1565, -6), (key1288, -6), (key1785, -6), (key1565, -6), (key1538, 2), (key1652, 2), (key1614, 2), (key1308, 2), (key1810, 2), (key1614, 2), (key1334, 2), (key1308, 2), (key1769, 2), (key1538, 2), (key1810, 2), (key1652, 2)]

def rawRow11611 : Integer.Sparse Key := [(key1565, -6), (key1565, -6), (key1288, -6), (key1785, -6), (key1614, 2), (key1538, 2), (key1652, 2), (key1614, 2), (key1308, 2), (key1810, 2), (key1538, 2), (key1652, 2), (key1308, 2), (key1810, 2), (key1334, 2), (key1769, 2)]

def rawRow11612 : Integer.Sparse Key := [(key1565, -6), (key1565, -6), (key1785, -6), (key1288, -6), (key1614, 2), (key1652, 2), (key1538, 2), (key1614, 2), (key1810, 2), (key1308, 2), (key1652, 2), (key1538, 2), (key1810, 2), (key1308, 2), (key1769, 2), (key1334, 2)]

def rawRow11613 : Integer.Sparse Key := [(key1565, -6), (key1785, -6), (key1288, -6), (key1565, -6), (key1652, 2), (key1538, 2), (key1614, 2), (key1810, 2), (key1308, 2), (key1614, 2), (key1769, 2), (key1810, 2), (key1334, 2), (key1652, 2), (key1308, 2), (key1538, 2)]

def rawRow11614 : Integer.Sparse Key := [(key1565, -6), (key1785, -6), (key1565, -6), (key1288, -6), (key1652, 2), (key1614, 2), (key1538, 2), (key1810, 2), (key1614, 2), (key1308, 2), (key1810, 2), (key1769, 2), (key1652, 2), (key1334, 2), (key1538, 2), (key1308, 2)]

def rawRow11615 : Integer.Sparse Key := [(key1785, -6), (key1288, -6), (key1565, -6), (key1565, -6), (key1769, 2), (key1810, 2), (key1810, 2), (key1334, 2), (key1652, 2), (key1652, 2), (key1308, 2), (key1308, 2), (key1538, 2), (key1538, 2), (key1614, 2), (key1614, 2)]

def rawRow11616 : Integer.Sparse Key := [(key1785, -6), (key1565, -6), (key1288, -6), (key1565, -6), (key1810, 2), (key1769, 2), (key1810, 2), (key1652, 2), (key1334, 2), (key1652, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1614, 2), (key1308, 2), (key1538, 2)]

def rawRow11617 : Integer.Sparse Key := [(key1785, -6), (key1565, -6), (key1565, -6), (key1288, -6), (key1810, 2), (key1810, 2), (key1769, 2), (key1652, 2), (key1652, 2), (key1334, 2), (key1614, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1538, 2), (key1308, 2)]

def rawRow11618 : Integer.Sparse Key := [(key2398, 6), (key2401, 6), (key2401, 6), (key2433, 6), (key2597, -6), (key2886, -6), (key2886, -6), (key2908, -6)]

def rawRow11619 : Integer.Sparse Key := [(key2401, 6), (key2398, 6), (key2401, 6), (key2433, 6), (key2597, -6), (key2886, -6), (key2908, -6), (key2886, -6)]

def rawRow11620 : Integer.Sparse Key := [(key2401, 6), (key2401, 6), (key2398, 6), (key2433, 6), (key2597, -6), (key2908, -6), (key2886, -6), (key2886, -6)]

def rawRow11621 : Integer.Sparse Key := [(key2398, 6), (key2401, 6), (key2433, 6), (key2401, 6), (key2886, -6), (key2597, -6), (key2886, -6), (key2908, -6)]

def rawRow11622 : Integer.Sparse Key := [(key2401, 6), (key2398, 6), (key2433, 6), (key2401, 6), (key2886, -6), (key2597, -6), (key2908, -6), (key2886, -6)]

def rawRow11623 : Integer.Sparse Key := [(key2398, 6), (key2433, 6), (key2401, 6), (key2401, 6), (key2886, -6), (key2886, -6), (key2597, -6), (key2908, -6)]

def rawRow11624 : Integer.Sparse Key := [(key2433, 6), (key2398, 6), (key2401, 6), (key2401, 6), (key2886, -6), (key2886, -6), (key2908, -6), (key2597, -6)]

def rawRow11625 : Integer.Sparse Key := [(key2401, 6), (key2433, 6), (key2398, 6), (key2401, 6), (key2886, -6), (key2908, -6), (key2597, -6), (key2886, -6)]

def rawRow11626 : Integer.Sparse Key := [(key2433, 6), (key2401, 6), (key2398, 6), (key2401, 6), (key2886, -6), (key2908, -6), (key2886, -6), (key2597, -6)]

def rawRow11627 : Integer.Sparse Key := [(key2401, 6), (key2401, 6), (key2433, 6), (key2398, 6), (key2908, -6), (key2597, -6), (key2886, -6), (key2886, -6)]

def rawRow11628 : Integer.Sparse Key := [(key2401, 6), (key2433, 6), (key2401, 6), (key2398, 6), (key2908, -6), (key2886, -6), (key2597, -6), (key2886, -6)]

def rawRow11629 : Integer.Sparse Key := [(key2433, 6), (key2401, 6), (key2401, 6), (key2398, 6), (key2908, -6), (key2886, -6), (key2886, -6), (key2597, -6)]

def rawRow11630 : Integer.Sparse Key := [(key2399, 6), (key2403, 6), (key2403, 6), (key2434, 6), (key2387, -6), (key2477, -6), (key2477, -6), (key2541, -6)]

def rawRow11631 : Integer.Sparse Key := [(key2403, 6), (key2399, 6), (key2403, 6), (key2434, 6), (key2387, -6), (key2477, -6), (key2541, -6), (key2477, -6)]

def rawRow11632 : Integer.Sparse Key := [(key2403, 6), (key2403, 6), (key2399, 6), (key2434, 6), (key2387, -6), (key2541, -6), (key2477, -6), (key2477, -6)]

def rawRow11633 : Integer.Sparse Key := [(key2399, 6), (key2403, 6), (key2434, 6), (key2403, 6), (key2477, -6), (key2387, -6), (key2477, -6), (key2541, -6)]

def rawRow11634 : Integer.Sparse Key := [(key2403, 6), (key2399, 6), (key2434, 6), (key2403, 6), (key2477, -6), (key2387, -6), (key2541, -6), (key2477, -6)]

def rawRow11635 : Integer.Sparse Key := [(key2399, 6), (key2434, 6), (key2403, 6), (key2403, 6), (key2477, -6), (key2477, -6), (key2387, -6), (key2541, -6)]

def rawRow11636 : Integer.Sparse Key := [(key2434, 6), (key2399, 6), (key2403, 6), (key2403, 6), (key2477, -6), (key2477, -6), (key2541, -6), (key2387, -6)]

def rawRow11637 : Integer.Sparse Key := [(key2403, 6), (key2434, 6), (key2399, 6), (key2403, 6), (key2477, -6), (key2541, -6), (key2387, -6), (key2477, -6)]

def rawRow11638 : Integer.Sparse Key := [(key2434, 6), (key2403, 6), (key2399, 6), (key2403, 6), (key2477, -6), (key2541, -6), (key2477, -6), (key2387, -6)]

def rawRow11639 : Integer.Sparse Key := [(key2403, 6), (key2403, 6), (key2434, 6), (key2399, 6), (key2541, -6), (key2387, -6), (key2477, -6), (key2477, -6)]

def rawRow11640 : Integer.Sparse Key := [(key2403, 6), (key2434, 6), (key2403, 6), (key2399, 6), (key2541, -6), (key2477, -6), (key2387, -6), (key2477, -6)]

def rawRow11641 : Integer.Sparse Key := [(key2434, 6), (key2403, 6), (key2403, 6), (key2399, 6), (key2541, -6), (key2477, -6), (key2477, -6), (key2387, -6)]

def rawRow11642 : Integer.Sparse Key := [(key2193, -6), (key2194, -6), (key2194, -6), (key2200, -6), (key2091, 2), (key2092, 2), (key2092, 2), (key2302, 2), (key2303, 2), (key2302, 2), (key2341, 2), (key2303, 2), (key2341, 2), (key2310, 2), (key2310, 2), (key2347, 2)]

def rawRow11643 : Integer.Sparse Key := [(key2194, -6), (key2193, -6), (key2194, -6), (key2200, -6), (key2092, 2), (key2091, 2), (key2092, 2), (key2303, 2), (key2302, 2), (key2341, 2), (key2302, 2), (key2341, 2), (key2303, 2), (key2310, 2), (key2347, 2), (key2310, 2)]

def rawRow11644 : Integer.Sparse Key := [(key2194, -6), (key2194, -6), (key2193, -6), (key2200, -6), (key2092, 2), (key2092, 2), (key2091, 2), (key2341, 2), (key2341, 2), (key2303, 2), (key2303, 2), (key2302, 2), (key2302, 2), (key2347, 2), (key2310, 2), (key2310, 2)]

def rawRow11645 : Integer.Sparse Key := [(key2193, -6), (key2194, -6), (key2200, -6), (key2194, -6), (key2302, 2), (key2303, 2), (key2310, 2), (key2091, 2), (key2092, 2), (key2302, 2), (key2341, 2), (key2310, 2), (key2347, 2), (key2092, 2), (key2303, 2), (key2341, 2)]

def rawRow11646 : Integer.Sparse Key := [(key2194, -6), (key2193, -6), (key2200, -6), (key2194, -6), (key2303, 2), (key2302, 2), (key2310, 2), (key2092, 2), (key2091, 2), (key2341, 2), (key2302, 2), (key2347, 2), (key2310, 2), (key2092, 2), (key2341, 2), (key2303, 2)]

def rawRow11647 : Integer.Sparse Key := [(key2193, -6), (key2200, -6), (key2194, -6), (key2194, -6), (key2302, 2), (key2310, 2), (key2303, 2), (key2302, 2), (key2310, 2), (key2091, 2), (key2347, 2), (key2092, 2), (key2341, 2), (key2303, 2), (key2092, 2), (key2341, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11648 : Integer.Sparse Key := [(key2200, -6), (key2193, -6), (key2194, -6), (key2194, -6), (key2310, 2), (key2302, 2), (key2303, 2), (key2310, 2), (key2302, 2), (key2347, 2), (key2091, 2), (key2341, 2), (key2092, 2), (key2303, 2), (key2341, 2), (key2092, 2)]

def rawRow11649 : Integer.Sparse Key := [(key2194, -6), (key2200, -6), (key2193, -6), (key2194, -6), (key2303, 2), (key2310, 2), (key2302, 2), (key2341, 2), (key2347, 2), (key2092, 2), (key2310, 2), (key2091, 2), (key2302, 2), (key2341, 2), (key2092, 2), (key2303, 2)]

def rawRow11650 : Integer.Sparse Key := [(key2200, -6), (key2194, -6), (key2193, -6), (key2194, -6), (key2310, 2), (key2303, 2), (key2302, 2), (key2347, 2), (key2341, 2), (key2310, 2), (key2092, 2), (key2302, 2), (key2091, 2), (key2341, 2), (key2303, 2), (key2092, 2)]

def rawRow11651 : Integer.Sparse Key := [(key2194, -6), (key2194, -6), (key2200, -6), (key2193, -6), (key2341, 2), (key2341, 2), (key2347, 2), (key2092, 2), (key2092, 2), (key2303, 2), (key2303, 2), (key2310, 2), (key2310, 2), (key2091, 2), (key2302, 2), (key2302, 2)]

def rawRow11652 : Integer.Sparse Key := [(key2194, -6), (key2200, -6), (key2194, -6), (key2193, -6), (key2341, 2), (key2347, 2), (key2341, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2302, 2), (key2091, 2), (key2302, 2)]

def rawRow11653 : Integer.Sparse Key := [(key2200, -6), (key2194, -6), (key2194, -6), (key2193, -6), (key2347, 2), (key2341, 2), (key2341, 2), (key2310, 2), (key2303, 2), (key2310, 2), (key2092, 2), (key2303, 2), (key2092, 2), (key2302, 2), (key2302, 2), (key2091, 2)]

def rawRow11654 : Integer.Sparse Key := [(key1029, 6), (key1034, 6), (key1034, 6), (key1069, 6), (key1013, -6), (key1121, -6), (key1121, -6), (key1197, -6)]

def rawRow11655 : Integer.Sparse Key := [(key1034, 6), (key1029, 6), (key1034, 6), (key1069, 6), (key1013, -6), (key1121, -6), (key1197, -6), (key1121, -6)]

def rawRow11656 : Integer.Sparse Key := [(key1034, 6), (key1034, 6), (key1029, 6), (key1069, 6), (key1013, -6), (key1197, -6), (key1121, -6), (key1121, -6)]

def rawRow11657 : Integer.Sparse Key := [(key1029, 6), (key1034, 6), (key1069, 6), (key1034, 6), (key1121, -6), (key1013, -6), (key1121, -6), (key1197, -6)]

def rawRow11658 : Integer.Sparse Key := [(key1034, 6), (key1029, 6), (key1069, 6), (key1034, 6), (key1121, -6), (key1013, -6), (key1197, -6), (key1121, -6)]

def rawRow11659 : Integer.Sparse Key := [(key1029, 6), (key1069, 6), (key1034, 6), (key1034, 6), (key1121, -6), (key1121, -6), (key1013, -6), (key1197, -6)]

def rawRow11660 : Integer.Sparse Key := [(key1069, 6), (key1029, 6), (key1034, 6), (key1034, 6), (key1121, -6), (key1121, -6), (key1197, -6), (key1013, -6)]

def rawRow11661 : Integer.Sparse Key := [(key1034, 6), (key1069, 6), (key1029, 6), (key1034, 6), (key1121, -6), (key1197, -6), (key1013, -6), (key1121, -6)]

def rawRow11662 : Integer.Sparse Key := [(key1069, 6), (key1034, 6), (key1029, 6), (key1034, 6), (key1121, -6), (key1197, -6), (key1121, -6), (key1013, -6)]

def rawRow11663 : Integer.Sparse Key := [(key1034, 6), (key1034, 6), (key1069, 6), (key1029, 6), (key1197, -6), (key1013, -6), (key1121, -6), (key1121, -6)]

def rawRow11664 : Integer.Sparse Key := [(key1034, 6), (key1069, 6), (key1034, 6), (key1029, 6), (key1197, -6), (key1121, -6), (key1013, -6), (key1121, -6)]

def rawRow11665 : Integer.Sparse Key := [(key1069, 6), (key1034, 6), (key1034, 6), (key1029, 6), (key1197, -6), (key1121, -6), (key1121, -6), (key1013, -6)]

def rawRow11666 : Integer.Sparse Key := [(key2398, -6), (key2401, -6), (key2401, -6), (key2433, -6), (key2583, 2), (key2586, 2), (key2586, 2), (key2839, 2), (key2842, 2), (key2839, 2), (key2874, 2), (key2842, 2), (key2874, 2), (key2965, 2), (key2965, 2), (key2987, 2)]

def rawRow11667 : Integer.Sparse Key := [(key2401, -6), (key2398, -6), (key2401, -6), (key2433, -6), (key2586, 2), (key2583, 2), (key2586, 2), (key2842, 2), (key2839, 2), (key2874, 2), (key2839, 2), (key2874, 2), (key2842, 2), (key2965, 2), (key2987, 2), (key2965, 2)]

def rawRow11668 : Integer.Sparse Key := [(key2401, -6), (key2401, -6), (key2398, -6), (key2433, -6), (key2586, 2), (key2586, 2), (key2583, 2), (key2874, 2), (key2874, 2), (key2842, 2), (key2842, 2), (key2839, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2965, 2)]

def rawRow11669 : Integer.Sparse Key := [(key2398, -6), (key2401, -6), (key2433, -6), (key2401, -6), (key2839, 2), (key2842, 2), (key2965, 2), (key2583, 2), (key2586, 2), (key2839, 2), (key2874, 2), (key2965, 2), (key2987, 2), (key2586, 2), (key2842, 2), (key2874, 2)]

def rawRow11670 : Integer.Sparse Key := [(key2401, -6), (key2398, -6), (key2433, -6), (key2401, -6), (key2842, 2), (key2839, 2), (key2965, 2), (key2586, 2), (key2583, 2), (key2874, 2), (key2839, 2), (key2987, 2), (key2965, 2), (key2586, 2), (key2874, 2), (key2842, 2)]

def rawRow11671 : Integer.Sparse Key := [(key2398, -6), (key2433, -6), (key2401, -6), (key2401, -6), (key2839, 2), (key2965, 2), (key2842, 2), (key2839, 2), (key2965, 2), (key2583, 2), (key2987, 2), (key2586, 2), (key2874, 2), (key2842, 2), (key2586, 2), (key2874, 2)]

def rawRow11672 : Integer.Sparse Key := [(key2433, -6), (key2398, -6), (key2401, -6), (key2401, -6), (key2965, 2), (key2839, 2), (key2842, 2), (key2965, 2), (key2839, 2), (key2987, 2), (key2583, 2), (key2874, 2), (key2586, 2), (key2842, 2), (key2874, 2), (key2586, 2)]

def rawRow11673 : Integer.Sparse Key := [(key2401, -6), (key2433, -6), (key2398, -6), (key2401, -6), (key2842, 2), (key2965, 2), (key2839, 2), (key2874, 2), (key2987, 2), (key2586, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2874, 2), (key2586, 2), (key2842, 2)]

def rawRow11674 : Integer.Sparse Key := [(key2433, -6), (key2401, -6), (key2398, -6), (key2401, -6), (key2965, 2), (key2842, 2), (key2839, 2), (key2987, 2), (key2874, 2), (key2965, 2), (key2586, 2), (key2839, 2), (key2583, 2), (key2874, 2), (key2842, 2), (key2586, 2)]

def rawRow11675 : Integer.Sparse Key := [(key2401, -6), (key2401, -6), (key2433, -6), (key2398, -6), (key2874, 2), (key2874, 2), (key2987, 2), (key2586, 2), (key2586, 2), (key2842, 2), (key2842, 2), (key2965, 2), (key2965, 2), (key2583, 2), (key2839, 2), (key2839, 2)]

def rawRow11676 : Integer.Sparse Key := [(key2401, -6), (key2433, -6), (key2401, -6), (key2398, -6), (key2874, 2), (key2987, 2), (key2874, 2), (key2842, 2), (key2965, 2), (key2586, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2839, 2), (key2583, 2), (key2839, 2)]

def rawRow11677 : Integer.Sparse Key := [(key2433, -6), (key2401, -6), (key2401, -6), (key2398, -6), (key2987, 2), (key2874, 2), (key2874, 2), (key2965, 2), (key2842, 2), (key2965, 2), (key2586, 2), (key2842, 2), (key2586, 2), (key2839, 2), (key2839, 2), (key2583, 2)]

def rawRow11678 : Integer.Sparse Key := [(key2662, -6), (key2777, -6), (key2777, -6), (key2788, -6), (key2607, 6), (key2800, 6), (key2800, 6), (key2823, 6)]

def rawRow11679 : Integer.Sparse Key := [(key2662, -6), (key2777, -6), (key2788, -6), (key2777, -6), (key2607, 6), (key2800, 6), (key2823, 6), (key2800, 6)]

def rawRow11680 : Integer.Sparse Key := [(key2662, -6), (key2788, -6), (key2777, -6), (key2777, -6), (key2607, 6), (key2823, 6), (key2800, 6), (key2800, 6)]

def rawRow11681 : Integer.Sparse Key := [(key2777, -6), (key2662, -6), (key2777, -6), (key2788, -6), (key2800, 6), (key2607, 6), (key2800, 6), (key2823, 6)]

def rawRow11682 : Integer.Sparse Key := [(key2777, -6), (key2662, -6), (key2788, -6), (key2777, -6), (key2800, 6), (key2607, 6), (key2823, 6), (key2800, 6)]

def rawRow11683 : Integer.Sparse Key := [(key2777, -6), (key2777, -6), (key2662, -6), (key2788, -6), (key2800, 6), (key2800, 6), (key2607, 6), (key2823, 6)]

def rawRow11684 : Integer.Sparse Key := [(key2777, -6), (key2777, -6), (key2788, -6), (key2662, -6), (key2800, 6), (key2800, 6), (key2823, 6), (key2607, 6)]

def rawRow11685 : Integer.Sparse Key := [(key2777, -6), (key2788, -6), (key2662, -6), (key2777, -6), (key2800, 6), (key2823, 6), (key2607, 6), (key2800, 6)]

def rawRow11686 : Integer.Sparse Key := [(key2777, -6), (key2788, -6), (key2777, -6), (key2662, -6), (key2800, 6), (key2823, 6), (key2800, 6), (key2607, 6)]

def rawRow11687 : Integer.Sparse Key := [(key2788, -6), (key2662, -6), (key2777, -6), (key2777, -6), (key2823, 6), (key2607, 6), (key2800, 6), (key2800, 6)]

def rawRow11688 : Integer.Sparse Key := [(key2788, -6), (key2777, -6), (key2662, -6), (key2777, -6), (key2823, 6), (key2800, 6), (key2607, 6), (key2800, 6)]

def rawRow11689 : Integer.Sparse Key := [(key2788, -6), (key2777, -6), (key2777, -6), (key2662, -6), (key2823, 6), (key2800, 6), (key2800, 6), (key2607, 6)]

def rawRow11690 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2809, -2), (key2809, -2), (key2951, -2), (key2829, -2), (key2832, -2), (key2829, -2), (key2961, -2), (key2832, -2), (key2961, -2), (key2632, 2), (key2632, 2), (key2649, 2), (key2786, 2), (key2786, 2), (key2939, 2), (key2870, 2), (key2905, 2), (key2870, 2), (key2984, 2), (key2905, 2), (key2984, 2)]

def rawRow11691 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2809, -2), (key2951, -2), (key2809, -2), (key2832, -2), (key2829, -2), (key2961, -2), (key2829, -2), (key2961, -2), (key2832, -2), (key2632, 2), (key2649, 2), (key2632, 2), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, 2), (key2870, 2), (key2984, 2), (key2870, 2), (key2984, 2), (key2905, 2)]

def rawRow11692 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2951, -2), (key2809, -2), (key2809, -2), (key2961, -2), (key2961, -2), (key2832, -2), (key2832, -2), (key2829, -2), (key2829, -2), (key2649, 2), (key2632, 2), (key2632, 2), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, 2), (key2984, 2), (key2905, 2), (key2905, 2), (key2870, 2), (key2870, 2)]

def rawRow11693 : Integer.Sparse Key := [(key2809, -2), (key2829, -2), (key2832, -2), (key2616, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2619, -2), (key2809, -2), (key2951, -2), (key2832, -2), (key2961, -2), (key2786, 2), (key2870, 2), (key2905, 2), (key2632, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2649, 2), (key2786, 2), (key2939, 2), (key2905, 2), (key2984, 2)]

def rawRow11694 : Integer.Sparse Key := [(key2809, -2), (key2832, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2829, -2), (key2619, -2), (key2616, -2), (key2951, -2), (key2809, -2), (key2961, -2), (key2832, -2), (key2786, 2), (key2905, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2870, 2), (key2649, 2), (key2632, 2), (key2939, 2), (key2786, 2), (key2984, 2), (key2905, 2)]

def rawRow11695 : Integer.Sparse Key := [(key2829, -2), (key2809, -2), (key2832, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2809, -2), (key2832, -2), (key2616, -2), (key2961, -2), (key2619, -2), (key2951, -2), (key2870, 2), (key2786, 2), (key2905, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2786, 2), (key2905, 2), (key2632, 2), (key2984, 2), (key2649, 2), (key2939, 2)]

def rawRow11696 : Integer.Sparse Key := [(key2829, -2), (key2832, -2), (key2809, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2832, -2), (key2809, -2), (key2961, -2), (key2616, -2), (key2951, -2), (key2619, -2), (key2870, 2), (key2905, 2), (key2786, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2905, 2), (key2786, 2), (key2984, 2), (key2632, 2), (key2939, 2), (key2649, 2)]

def rawRow11697 : Integer.Sparse Key := [(key2832, -2), (key2809, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2829, -2), (key2951, -2), (key2961, -2), (key2619, -2), (key2832, -2), (key2616, -2), (key2809, -2), (key2905, 2), (key2786, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2870, 2), (key2939, 2), (key2984, 2), (key2649, 2), (key2905, 2), (key2632, 2), (key2786, 2)]

def rawRow11698 : Integer.Sparse Key := [(key2832, -2), (key2829, -2), (key2809, -2), (key2961, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2951, -2), (key2832, -2), (key2619, -2), (key2809, -2), (key2616, -2), (key2905, 2), (key2870, 2), (key2786, 2), (key2984, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2939, 2), (key2905, 2), (key2649, 2), (key2786, 2), (key2632, 2)]

def rawRow11699 : Integer.Sparse Key := [(key2951, -2), (key2961, -2), (key2961, -2), (key2619, -2), (key2832, -2), (key2832, -2), (key2616, -2), (key2616, -2), (key2809, -2), (key2809, -2), (key2829, -2), (key2829, -2), (key2939, 2), (key2984, 2), (key2984, 2), (key2649, 2), (key2905, 2), (key2905, 2), (key2632, 2), (key2632, 2), (key2786, 2), (key2786, 2), (key2870, 2), (key2870, 2)]

def rawRow11700 : Integer.Sparse Key := [(key2961, -2), (key2951, -2), (key2961, -2), (key2832, -2), (key2619, -2), (key2832, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2984, 2), (key2939, 2), (key2984, 2), (key2905, 2), (key2649, 2), (key2905, 2), (key2786, 2), (key2870, 2), (key2632, 2), (key2870, 2), (key2632, 2), (key2786, 2)]

def rawRow11701 : Integer.Sparse Key := [(key2961, -2), (key2961, -2), (key2951, -2), (key2832, -2), (key2832, -2), (key2619, -2), (key2829, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2616, -2), (key2984, 2), (key2984, 2), (key2939, 2), (key2905, 2), (key2905, 2), (key2649, 2), (key2870, 2), (key2786, 2), (key2870, 2), (key2632, 2), (key2786, 2), (key2632, 2)]

def rawRow11702 : Integer.Sparse Key := [(key1003, 2), (key1003, 2), (key1007, 2), (key1116, 2), (key1116, 2), (key1194, 2), (key1152, 2), (key1156, 2), (key1152, 2), (key1213, 2), (key1156, 2), (key1213, 2), (key1017, -2), (key1020, -2), (key1020, -2), (key1125, -2), (key1128, -2), (key1125, -2), (key1200, -2), (key1128, -2), (key1200, -2), (key1172, -2), (key1172, -2), (key1223, -2)]

def rawRow11703 : Integer.Sparse Key := [(key1003, 2), (key1007, 2), (key1003, 2), (key1116, 2), (key1194, 2), (key1116, 2), (key1156, 2), (key1152, 2), (key1213, 2), (key1152, 2), (key1213, 2), (key1156, 2), (key1020, -2), (key1017, -2), (key1020, -2), (key1128, -2), (key1125, -2), (key1200, -2), (key1125, -2), (key1200, -2), (key1128, -2), (key1172, -2), (key1223, -2), (key1172, -2)]

def rawRow11704 : Integer.Sparse Key := [(key1007, 2), (key1003, 2), (key1003, 2), (key1194, 2), (key1116, 2), (key1116, 2), (key1213, 2), (key1213, 2), (key1156, 2), (key1156, 2), (key1152, 2), (key1152, 2), (key1020, -2), (key1020, -2), (key1017, -2), (key1200, -2), (key1200, -2), (key1128, -2), (key1128, -2), (key1125, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1172, -2)]

def rawRow11705 : Integer.Sparse Key := [(key1116, 2), (key1152, 2), (key1156, 2), (key1003, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1007, 2), (key1116, 2), (key1194, 2), (key1156, 2), (key1213, 2), (key1125, -2), (key1128, -2), (key1172, -2), (key1017, -2), (key1020, -2), (key1125, -2), (key1200, -2), (key1172, -2), (key1223, -2), (key1020, -2), (key1128, -2), (key1200, -2)]

def rawRow11706 : Integer.Sparse Key := [(key1116, 2), (key1156, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1152, 2), (key1007, 2), (key1003, 2), (key1194, 2), (key1116, 2), (key1213, 2), (key1156, 2), (key1128, -2), (key1125, -2), (key1172, -2), (key1020, -2), (key1017, -2), (key1200, -2), (key1125, -2), (key1223, -2), (key1172, -2), (key1020, -2), (key1200, -2), (key1128, -2)]

def rawRow11707 : Integer.Sparse Key := [(key1152, 2), (key1116, 2), (key1156, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1116, 2), (key1156, 2), (key1003, 2), (key1213, 2), (key1007, 2), (key1194, 2), (key1125, -2), (key1172, -2), (key1128, -2), (key1125, -2), (key1172, -2), (key1017, -2), (key1223, -2), (key1020, -2), (key1200, -2), (key1128, -2), (key1020, -2), (key1200, -2)]

def rawRow11708 : Integer.Sparse Key := [(key1152, 2), (key1156, 2), (key1116, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1156, 2), (key1116, 2), (key1213, 2), (key1003, 2), (key1194, 2), (key1007, 2), (key1172, -2), (key1125, -2), (key1128, -2), (key1172, -2), (key1125, -2), (key1223, -2), (key1017, -2), (key1200, -2), (key1020, -2), (key1128, -2), (key1200, -2), (key1020, -2)]

def rawRow11709 : Integer.Sparse Key := [(key1156, 2), (key1116, 2), (key1152, 2), (key1213, 2), (key1003, 2), (key1152, 2), (key1194, 2), (key1213, 2), (key1007, 2), (key1156, 2), (key1003, 2), (key1116, 2), (key1128, -2), (key1172, -2), (key1125, -2), (key1200, -2), (key1223, -2), (key1020, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1200, -2), (key1020, -2), (key1128, -2)]

def rawRow11710 : Integer.Sparse Key := [(key1156, 2), (key1152, 2), (key1116, 2), (key1213, 2), (key1152, 2), (key1003, 2), (key1213, 2), (key1194, 2), (key1156, 2), (key1007, 2), (key1116, 2), (key1003, 2), (key1172, -2), (key1128, -2), (key1125, -2), (key1223, -2), (key1200, -2), (key1172, -2), (key1020, -2), (key1125, -2), (key1017, -2), (key1200, -2), (key1128, -2), (key1020, -2)]

def rawRow11711 : Integer.Sparse Key := [(key1194, 2), (key1213, 2), (key1213, 2), (key1007, 2), (key1156, 2), (key1156, 2), (key1003, 2), (key1003, 2), (key1116, 2), (key1116, 2), (key1152, 2), (key1152, 2), (key1200, -2), (key1200, -2), (key1223, -2), (key1020, -2), (key1020, -2), (key1128, -2), (key1128, -2), (key1172, -2), (key1172, -2), (key1017, -2), (key1125, -2), (key1125, -2)]

def rawRow11712 : Integer.Sparse Key := [(key1213, 2), (key1194, 2), (key1213, 2), (key1156, 2), (key1007, 2), (key1156, 2), (key1116, 2), (key1152, 2), (key1003, 2), (key1152, 2), (key1003, 2), (key1116, 2), (key1200, -2), (key1223, -2), (key1200, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1125, -2), (key1017, -2), (key1125, -2)]

def rawRow11713 : Integer.Sparse Key := [(key1213, 2), (key1213, 2), (key1194, 2), (key1156, 2), (key1156, 2), (key1007, 2), (key1152, 2), (key1116, 2), (key1152, 2), (key1003, 2), (key1116, 2), (key1003, 2), (key1223, -2), (key1200, -2), (key1200, -2), (key1172, -2), (key1128, -2), (key1172, -2), (key1020, -2), (key1128, -2), (key1020, -2), (key1125, -2), (key1125, -2), (key1017, -2)]

def rawRow11714 : Integer.Sparse Key := [(key2678, -4), (key2678, -4), (key2687, -4), (key2812, -4), (key2816, -4), (key2816, -4), (key2709, 6), (key2713, 6), (key2713, 6), (key2862, 6)]

def rawRow11715 : Integer.Sparse Key := [(key2678, -4), (key2687, -4), (key2678, -4), (key2816, -4), (key2812, -4), (key2816, -4), (key2713, 6), (key2709, 6), (key2713, 6), (key2862, 6)]

def rawRow11716 : Integer.Sparse Key := [(key2687, -4), (key2678, -4), (key2678, -4), (key2816, -4), (key2816, -4), (key2812, -4), (key2713, 6), (key2713, 6), (key2709, 6), (key2862, 6)]

def rawRow11717 : Integer.Sparse Key := [(key2678, -4), (key2812, -4), (key2816, -4), (key2678, -4), (key2687, -4), (key2816, -4), (key2709, 6), (key2713, 6), (key2862, 6), (key2713, 6)]

def rawRow11718 : Integer.Sparse Key := [(key2678, -4), (key2816, -4), (key2812, -4), (key2687, -4), (key2678, -4), (key2816, -4), (key2713, 6), (key2709, 6), (key2862, 6), (key2713, 6)]

def rawRow11719 : Integer.Sparse Key := [(key2812, -4), (key2678, -4), (key2816, -4), (key2678, -4), (key2816, -4), (key2687, -4), (key2709, 6), (key2862, 6), (key2713, 6), (key2713, 6)]

def rawRow11720 : Integer.Sparse Key := [(key2812, -4), (key2816, -4), (key2678, -4), (key2816, -4), (key2678, -4), (key2687, -4), (key2862, 6), (key2709, 6), (key2713, 6), (key2713, 6)]

def rawRow11721 : Integer.Sparse Key := [(key2816, -4), (key2678, -4), (key2812, -4), (key2687, -4), (key2816, -4), (key2678, -4), (key2713, 6), (key2862, 6), (key2709, 6), (key2713, 6)]

def rawRow11722 : Integer.Sparse Key := [(key2816, -4), (key2812, -4), (key2678, -4), (key2816, -4), (key2687, -4), (key2678, -4), (key2862, 6), (key2713, 6), (key2709, 6), (key2713, 6)]

def rawRow11723 : Integer.Sparse Key := [(key2687, -4), (key2816, -4), (key2816, -4), (key2678, -4), (key2678, -4), (key2812, -4), (key2713, 6), (key2713, 6), (key2862, 6), (key2709, 6)]

def rawRow11724 : Integer.Sparse Key := [(key2816, -4), (key2687, -4), (key2816, -4), (key2678, -4), (key2812, -4), (key2678, -4), (key2713, 6), (key2862, 6), (key2713, 6), (key2709, 6)]

def rawRow11725 : Integer.Sparse Key := [(key2816, -4), (key2816, -4), (key2687, -4), (key2812, -4), (key2678, -4), (key2678, -4), (key2862, 6), (key2713, 6), (key2713, 6), (key2709, 6)]

def rawRow11726 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1937, 6), (key1949, 6), (key1940, -24)]

def rawRow11727 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1937, 6), (key1949, 6), (key1940, -24)]

def rawRow11728 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1936, 6), (key1949, 6), (key1940, -24)]

def rawRow11729 : Integer.Sparse Key := [(key1936, 6), (key1937, 6), (key1949, 6), (key1937, 6), (key1940, -24)]

def rawRow11730 : Integer.Sparse Key := [(key1937, 6), (key1936, 6), (key1949, 6), (key1937, 6), (key1940, -24)]

def rawRow11731 : Integer.Sparse Key := [(key1936, 6), (key1949, 6), (key1937, 6), (key1937, 6), (key1940, -24)]

def rawRow11732 : Integer.Sparse Key := [(key1949, 6), (key1936, 6), (key1937, 6), (key1937, 6), (key1940, -24)]

def rawRow11733 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1936, 6), (key1937, 6), (key1940, -24)]

def rawRow11734 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1936, 6), (key1937, 6), (key1940, -24)]

def rawRow11735 : Integer.Sparse Key := [(key1937, 6), (key1937, 6), (key1949, 6), (key1936, 6), (key1940, -24)]

def rawRow11736 : Integer.Sparse Key := [(key1937, 6), (key1949, 6), (key1937, 6), (key1936, 6), (key1940, -24)]

def rawRow11737 : Integer.Sparse Key := [(key1949, 6), (key1937, 6), (key1937, 6), (key1936, 6), (key1940, -24)]

def rawRow11738 : Integer.Sparse Key := [(key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1), (key2851, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2866, 1), (key2971, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2981, 1), (key2645, -2), (key2645, -2), (key2651, -2), (key2734, -2), (key2734, -2), (key2745, -2), (key2892, -2), (key2895, -2), (key2892, -2), (key2902, -2), (key2895, -2), (key2902, -2)]

def rawRow11739 : Integer.Sparse Key := [(key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2645, -2), (key2651, -2), (key2645, -2), (key2734, -2), (key2745, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2902, -2), (key2892, -2), (key2902, -2), (key2895, -2)]

def rawRow11740 : Integer.Sparse Key := [(key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2866, 1), (key2866, 1), (key2856, 1), (key2856, 1), (key2851, 1), (key2851, 1), (key2981, 1), (key2981, 1), (key2974, 1), (key2974, 1), (key2971, 1), (key2971, 1), (key2651, -2), (key2645, -2), (key2645, -2), (key2745, -2), (key2734, -2), (key2734, -2), (key2902, -2), (key2902, -2), (key2895, -2), (key2895, -2), (key2892, -2), (key2892, -2)]

def rawRow11741 : Integer.Sparse Key := [(key2698, 1), (key2701, 1), (key2851, 1), (key2856, 1), (key2971, 1), (key2974, 1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1), (key2734, -2), (key2892, -2), (key2895, -2), (key2645, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2651, -2), (key2734, -2), (key2745, -2), (key2895, -2), (key2902, -2)]

def rawRow11742 : Integer.Sparse Key := [(key2701, 1), (key2698, 1), (key2856, 1), (key2851, 1), (key2974, 1), (key2971, 1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2892, -2), (key2651, -2), (key2645, -2), (key2745, -2), (key2734, -2), (key2902, -2), (key2895, -2)]

def rawRow11743 : Integer.Sparse Key := [(key2851, 1), (key2971, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2892, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2734, -2), (key2895, -2), (key2645, -2), (key2902, -2), (key2651, -2), (key2745, -2)]

def rawRow11744 : Integer.Sparse Key := [(key2971, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1), (key2892, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2895, -2), (key2734, -2), (key2902, -2), (key2645, -2), (key2745, -2), (key2651, -2)]

def rawRow11745 : Integer.Sparse Key := [(key2856, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2698, 1), (key2851, 1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2892, -2), (key2745, -2), (key2902, -2), (key2651, -2), (key2895, -2), (key2645, -2), (key2734, -2)]

def rawRow11746 : Integer.Sparse Key := [(key2974, 1), (key2856, 1), (key2971, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2895, -2), (key2892, -2), (key2734, -2), (key2902, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2745, -2), (key2895, -2), (key2651, -2), (key2734, -2), (key2645, -2)]

def rawRow11747 : Integer.Sparse Key := [(key2722, 1), (key2722, 1), (key2866, 1), (key2866, 1), (key2981, 1), (key2981, 1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2627, 1), (key2627, 1), (key2701, 1), (key2701, 1), (key2971, 1), (key2971, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1), (key2745, -2), (key2902, -2), (key2902, -2), (key2651, -2), (key2895, -2), (key2895, -2), (key2645, -2), (key2645, -2), (key2734, -2), (key2734, -2), (key2892, -2), (key2892, -2)]

def rawRow11748 : Integer.Sparse Key := [(key2866, 1), (key2981, 1), (key2722, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2902, -2), (key2745, -2), (key2902, -2), (key2895, -2), (key2651, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2645, -2), (key2892, -2), (key2645, -2), (key2734, -2)]

def rawRow11749 : Integer.Sparse Key := [(key2981, 1), (key2866, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2971, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2627, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1), (key2902, -2), (key2902, -2), (key2745, -2), (key2895, -2), (key2895, -2), (key2651, -2), (key2892, -2), (key2734, -2), (key2892, -2), (key2645, -2), (key2734, -2), (key2645, -2)]

def rawRow11750 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2801, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2804, -2), (key2825, -2), (key2947, -2), (key2947, -2), (key2958, -2), (key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1), (key2851, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2866, 1), (key2971, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2981, 1)]

def rawRow11751 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2801, -2), (key2825, -2), (key2804, -2), (key2947, -2), (key2958, -2), (key2947, -2), (key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2971, 1), (key2981, 1), (key2974, 1)]

def rawRow11752 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2825, -2), (key2825, -2), (key2804, -2), (key2804, -2), (key2801, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2947, -2), (key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2866, 1), (key2866, 1), (key2856, 1), (key2856, 1), (key2851, 1), (key2851, 1), (key2981, 1), (key2981, 1), (key2974, 1), (key2974, 1), (key2971, 1), (key2971, 1)]

def rawRow11753 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2608, -2), (key2611, -2), (key2801, -2), (key2825, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2698, 1), (key2701, 1), (key2851, 1), (key2856, 1), (key2971, 1), (key2974, 1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1)]

def rawRow11754 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2611, -2), (key2608, -2), (key2825, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2701, 1), (key2698, 1), (key2856, 1), (key2851, 1), (key2974, 1), (key2971, 1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1)]

def rawRow11755 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2608, -2), (key2958, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2825, -2), (key2851, 1), (key2971, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1)]

def rawRow11756 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2825, -2), (key2801, -2), (key2958, -2), (key2608, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2971, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1)]

def rawRow11757 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2825, -2), (key2608, -2), (key2801, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2856, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2698, 1), (key2851, 1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1)]

def rawRow11758 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2825, -2), (key2611, -2), (key2801, -2), (key2608, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2974, 1), (key2856, 1), (key2971, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

def rawRow11759 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2611, -2), (key2804, -2), (key2804, -2), (key2825, -2), (key2825, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2722, 1), (key2722, 1), (key2866, 1), (key2866, 1), (key2981, 1), (key2981, 1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2627, 1), (key2627, 1), (key2701, 1), (key2701, 1), (key2971, 1), (key2971, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

def rawRow11760 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2866, 1), (key2981, 1), (key2722, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

def rawRow11761 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2825, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2611, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2981, 1), (key2866, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2971, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2627, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

def rawRow11762 : Integer.Sparse Key := [(key2624, -2), (key2627, -2), (key2636, -2), (key2698, -2), (key2701, -2), (key2851, -2), (key2971, -2), (key2856, -2), (key2974, -2), (key2722, -2), (key2866, -2), (key2981, -2), (key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def rawRow11763 : Integer.Sparse Key := [(key2627, -2), (key2624, -2), (key2636, -2), (key2701, -2), (key2698, -2), (key2971, -2), (key2851, -2), (key2974, -2), (key2856, -2), (key2722, -2), (key2981, -2), (key2866, -2), (key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2790, 1), (key2778, 1), (key2825, 1), (key2801, 1), (key2902, 1), (key2895, 1), (key2941, 1), (key2935, 1), (key2958, 1), (key2947, 1), (key2981, 1), (key2974, 1)]

def rawRow11764 : Integer.Sparse Key := [(key2624, -2), (key2636, -2), (key2627, -2), (key2851, -2), (key2856, -2), (key2698, -2), (key2974, -2), (key2701, -2), (key2971, -2), (key2866, -2), (key2722, -2), (key2981, -2), (key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2801, 1), (key2895, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2947, 1), (key2974, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2958, 1)]

def rawRow11765 : Integer.Sparse Key := [(key2636, -2), (key2624, -2), (key2627, -2), (key2856, -2), (key2851, -2), (key2974, -2), (key2698, -2), (key2971, -2), (key2701, -2), (key2866, -2), (key2981, -2), (key2722, -2), (key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2825, 1), (key2790, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2958, 1), (key2941, 1)]

def rawRow11766 : Integer.Sparse Key := [(key2627, -2), (key2636, -2), (key2624, -2), (key2971, -2), (key2974, -2), (key2701, -2), (key2856, -2), (key2698, -2), (key2851, -2), (key2981, -2), (key2722, -2), (key2866, -2), (key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2825, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2778, 1), (key2801, 1), (key2958, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2935, 1), (key2947, 1)]

def rawRow11767 : Integer.Sparse Key := [(key2636, -2), (key2627, -2), (key2624, -2), (key2974, -2), (key2971, -2), (key2856, -2), (key2701, -2), (key2851, -2), (key2698, -2), (key2981, -2), (key2866, -2), (key2722, -2), (key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2902, 1), (key2825, 1), (key2895, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2958, 1), (key2974, 1), (key2941, 1), (key2947, 1), (key2935, 1)]

def rawRow11768 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2624, -2), (key2627, -2), (key2851, -2), (key2971, -2), (key2866, -2), (key2981, -2), (key2636, -2), (key2856, -2), (key2974, -2), (key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1)]

def rawRow11769 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2627, -2), (key2624, -2), (key2971, -2), (key2851, -2), (key2981, -2), (key2866, -2), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1)]

def rawRow11770 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2851, -2), (key2866, -2), (key2624, -2), (key2981, -2), (key2627, -2), (key2971, -2), (key2856, -2), (key2636, -2), (key2974, -2), (key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1)]

def rawRow11771 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2866, -2), (key2851, -2), (key2981, -2), (key2624, -2), (key2971, -2), (key2627, -2), (key2856, -2), (key2974, -2), (key2636, -2), (key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1)]

def rawRow11772 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2971, -2), (key2981, -2), (key2627, -2), (key2866, -2), (key2624, -2), (key2851, -2), (key2974, -2), (key2636, -2), (key2856, -2), (key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1)]

def rawRow11773 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2981, -2), (key2971, -2), (key2866, -2), (key2627, -2), (key2851, -2), (key2624, -2), (key2974, -2), (key2856, -2), (key2636, -2), (key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

def rawRow11774 : Integer.Sparse Key := [(key2851, -2), (key2856, -2), (key2866, -2), (key2624, -2), (key2636, -2), (key2698, -2), (key2974, -2), (key2722, -2), (key2981, -2), (key2627, -2), (key2701, -2), (key2971, -2), (key2778, 1), (key2790, 1), (key2801, 1), (key2895, 1), (key2825, 1), (key2902, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2974, 1), (key2722, 1), (key2981, 1), (key2608, 1), (key2651, 1), (key2663, 1), (key2745, 1), (key2941, 1), (key2958, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2722, 1), (key2790, 1), (key2825, 1)]

def rawRow11775 : Integer.Sparse Key := [(key2856, -2), (key2851, -2), (key2866, -2), (key2636, -2), (key2624, -2), (key2974, -2), (key2698, -2), (key2981, -2), (key2722, -2), (key2627, -2), (key2971, -2), (key2701, -2), (key2790, 1), (key2778, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2825, 1), (key2636, 1), (key2624, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2722, 1), (key2651, 1), (key2608, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2941, 1), (key2636, 1), (key2611, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2790, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11776 : Integer.Sparse Key := [(key2851, -2), (key2866, -2), (key2856, -2), (key2698, -2), (key2722, -2), (key2624, -2), (key2981, -2), (key2636, -2), (key2974, -2), (key2701, -2), (key2627, -2), (key2971, -2), (key2801, 1), (key2825, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2698, 1), (key2722, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2663, 1), (key2745, 1), (key2608, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2666, 1), (key2790, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2722, 1)]

def rawRow11777 : Integer.Sparse Key := [(key2866, -2), (key2851, -2), (key2856, -2), (key2722, -2), (key2698, -2), (key2981, -2), (key2624, -2), (key2974, -2), (key2636, -2), (key2701, -2), (key2971, -2), (key2627, -2), (key2825, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2895, 1), (key2790, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2974, 1), (key2636, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2608, 1), (key2745, 1), (key2651, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2722, 1), (key2636, 1)]

def rawRow11778 : Integer.Sparse Key := [(key2856, -2), (key2866, -2), (key2851, -2), (key2974, -2), (key2981, -2), (key2636, -2), (key2722, -2), (key2624, -2), (key2698, -2), (key2971, -2), (key2627, -2), (key2701, -2), (key2895, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2778, 1), (key2801, 1), (key2974, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2624, 1), (key2698, 1), (key2941, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2608, 1), (key2663, 1), (key2722, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2611, 1), (key2666, 1)]

def rawRow11779 : Integer.Sparse Key := [(key2866, -2), (key2856, -2), (key2851, -2), (key2981, -2), (key2974, -2), (key2722, -2), (key2636, -2), (key2698, -2), (key2624, -2), (key2971, -2), (key2701, -2), (key2627, -2), (key2902, 1), (key2895, 1), (key2825, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2974, 1), (key2722, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2958, 1), (key2941, 1), (key2745, 1), (key2651, 1), (key2663, 1), (key2608, 1), (key2825, 1), (key2722, 1), (key2790, 1), (key2636, 1), (key2666, 1), (key2611, 1)]

def rawRow11780 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2627, -2), (key2636, -2), (key2701, -2), (key2856, -2), (key2722, -2), (key2866, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

def rawRow11781 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2636, -2), (key2627, -2), (key2856, -2), (key2701, -2), (key2866, -2), (key2722, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

def rawRow11782 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2701, -2), (key2722, -2), (key2627, -2), (key2866, -2), (key2636, -2), (key2856, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

def rawRow11783 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2722, -2), (key2701, -2), (key2866, -2), (key2627, -2), (key2856, -2), (key2636, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

def rawRow11784 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2856, -2), (key2866, -2), (key2636, -2), (key2722, -2), (key2627, -2), (key2701, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

def rawRow11785 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2866, -2), (key2856, -2), (key2722, -2), (key2636, -2), (key2701, -2), (key2627, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

def rawRow11786 : Integer.Sparse Key := [(key2457, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2525, 2), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2564, -2)]

def rawRow11787 : Integer.Sparse Key := [(key2460, 2), (key2457, 2), (key2460, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2564, -2), (key2533, -2), (key2564, -2)]

def rawRow11788 : Integer.Sparse Key := [(key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2525, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2460, 2), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, -2), (key2564, -2), (key2533, -2)]

def rawRow11789 : Integer.Sparse Key := [(key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2525, 2), (key2457, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2521, 2), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2532, -2), (key2532, -2), (key2562, -2)]

def rawRow11790 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2532, -2), (key2562, -2), (key2532, -2)]

def rawRow11791 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2457, 2), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2532, -2)]

def rawRow11792 : Integer.Sparse Key := [(key974, -24), (key1088, 6), (key1088, 6), (key1178, 6), (key1178, 6)]

def rawRow11793 : Integer.Sparse Key := [(key974, -24), (key1088, 6), (key1178, 6), (key1088, 6), (key1178, 6)]

def rawRow11794 : Integer.Sparse Key := [(key974, -24), (key1088, 6), (key1178, 6), (key1178, 6), (key1088, 6)]

def rawRow11795 : Integer.Sparse Key := [(key974, -24), (key1178, 6), (key1088, 6), (key1088, 6), (key1178, 6)]

def rawRow11796 : Integer.Sparse Key := [(key974, -24), (key1178, 6), (key1088, 6), (key1178, 6), (key1088, 6)]

def rawRow11797 : Integer.Sparse Key := [(key974, -24), (key1178, 6), (key1178, 6), (key1088, 6), (key1088, 6)]

def rawRow11798 : Integer.Sparse Key := [(key1088, -24), (key974, 6), (key1088, 6), (key1178, 6), (key1178, 6)]

def rawRow11799 : Integer.Sparse Key := [(key1088, -24), (key974, 6), (key1178, 6), (key1088, 6), (key1178, 6)]

def rawRow11800 : Integer.Sparse Key := [(key1088, -24), (key974, 6), (key1178, 6), (key1178, 6), (key1088, 6)]

def rawRow11801 : Integer.Sparse Key := [(key1088, -24), (key1088, 6), (key974, 6), (key1178, 6), (key1178, 6)]

def rawRow11802 : Integer.Sparse Key := [(key1088, -24), (key1088, 6), (key1178, 6), (key974, 6), (key1178, 6)]

def rawRow11803 : Integer.Sparse Key := [(key1088, -24), (key1088, 6), (key1178, 6), (key1178, 6), (key974, 6)]

def rawRow11804 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key974, 6), (key1088, 6), (key1178, 6)]

def rawRow11805 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key974, 6), (key1178, 6), (key1088, 6)]

def rawRow11806 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1088, 6), (key974, 6), (key1178, 6)]

def rawRow11807 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1088, 6), (key1178, 6), (key974, 6)]

def rawRow11808 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1178, 6), (key974, 6), (key1088, 6)]

def rawRow11809 : Integer.Sparse Key := [(key1088, -24), (key1178, 6), (key1178, 6), (key1088, 6), (key974, 6)]

def rawRow11810 : Integer.Sparse Key := [(key976, -6), (key976, -6), (key984, -6), (key984, -6), (key1090, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1183, 2)]

def rawRow11811 : Integer.Sparse Key := [(key976, -6), (key984, -6), (key976, -6), (key984, -6), (key1090, 2), (key1098, 2), (key1090, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1183, 2), (key1098, 2), (key1183, 2)]

def rawRow11812 : Integer.Sparse Key := [(key984, -6), (key976, -6), (key976, -6), (key984, -6), (key1098, 2), (key1090, 2), (key1090, 2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1183, 2), (key1183, 2), (key1098, 2)]

def rawRow11813 : Integer.Sparse Key := [(key976, -6), (key984, -6), (key984, -6), (key976, -6), (key1180, 2), (key1183, 2), (key1183, 2), (key1090, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1183, 2), (key1090, 2), (key1090, 2), (key1180, 2)]

def rawRow11814 : Integer.Sparse Key := [(key984, -6), (key976, -6), (key984, -6), (key976, -6), (key1183, 2), (key1180, 2), (key1183, 2), (key1098, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1098, 2), (key1090, 2), (key1180, 2), (key1090, 2)]

def rawRow11815 : Integer.Sparse Key := [(key984, -6), (key984, -6), (key976, -6), (key976, -6), (key1183, 2), (key1183, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1098, 2), (key1098, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1090, 2)]

def rawRow11816 : Integer.Sparse Key := [(key1090, -6), (key1090, -6), (key1098, -6), (key1169, -6), (key976, 2), (key976, 2), (key984, 2), (key1090, 2), (key1090, 2), (key1180, 2), (key1180, 2), (key1183, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key1220, 2)]

def rawRow11817 : Integer.Sparse Key := [(key1090, -6), (key1098, -6), (key1090, -6), (key1169, -6), (key976, 2), (key984, 2), (key976, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key1169, 2), (key1220, 2)]

def rawRow11818 : Integer.Sparse Key := [(key1098, -6), (key1090, -6), (key1090, -6), (key1169, -6), (key984, 2), (key976, 2), (key976, 2), (key1183, 2), (key1180, 2), (key1183, 2), (key1090, 2), (key1180, 2), (key1090, 2), (key1220, 2), (key1220, 2), (key1169, 2)]

def rawRow11819 : Integer.Sparse Key := [(key1090, -6), (key1090, -6), (key1169, -6), (key1098, -6), (key1090, 2), (key1090, 2), (key1169, 2), (key976, 2), (key976, 2), (key1180, 2), (key1180, 2), (key1220, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1183, 2)]

def rawRow11820 : Integer.Sparse Key := [(key1090, -6), (key1169, -6), (key1090, -6), (key1098, -6), (key1090, 2), (key1169, 2), (key1090, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1220, 2), (key976, 2), (key1180, 2), (key1183, 2), (key984, 2), (key1183, 2)]

def rawRow11821 : Integer.Sparse Key := [(key1169, -6), (key1090, -6), (key1090, -6), (key1098, -6), (key1169, 2), (key1090, 2), (key1090, 2), (key1220, 2), (key1180, 2), (key1220, 2), (key976, 2), (key1180, 2), (key976, 2), (key1183, 2), (key1183, 2), (key984, 2)]

def rawRow11822 : Integer.Sparse Key := [(key1090, -6), (key1098, -6), (key1169, -6), (key1090, -6), (key1180, 2), (key1183, 2), (key1220, 2), (key976, 2), (key984, 2), (key1090, 2), (key1183, 2), (key1169, 2), (key1220, 2), (key976, 2), (key1090, 2), (key1180, 2)]

def rawRow11823 : Integer.Sparse Key := [(key1098, -6), (key1090, -6), (key1169, -6), (key1090, -6), (key1183, 2), (key1180, 2), (key1220, 2), (key984, 2), (key976, 2), (key1183, 2), (key1090, 2), (key1220, 2), (key1169, 2), (key976, 2), (key1180, 2), (key1090, 2)]

def rawRow11824 : Integer.Sparse Key := [(key1090, -6), (key1169, -6), (key1098, -6), (key1090, -6), (key1180, 2), (key1220, 2), (key1183, 2), (key1090, 2), (key1169, 2), (key976, 2), (key1220, 2), (key984, 2), (key1183, 2), (key1090, 2), (key976, 2), (key1180, 2)]

def rawRow11825 : Integer.Sparse Key := [(key1169, -6), (key1090, -6), (key1098, -6), (key1090, -6), (key1220, 2), (key1180, 2), (key1183, 2), (key1169, 2), (key1090, 2), (key1220, 2), (key976, 2), (key1183, 2), (key984, 2), (key1090, 2), (key1180, 2), (key976, 2)]

def rawRow11826 : Integer.Sparse Key := [(key1098, -6), (key1169, -6), (key1090, -6), (key1090, -6), (key1183, 2), (key1220, 2), (key1180, 2), (key1183, 2), (key1220, 2), (key984, 2), (key1169, 2), (key976, 2), (key1090, 2), (key1180, 2), (key976, 2), (key1090, 2)]

def rawRow11827 : Integer.Sparse Key := [(key1169, -6), (key1098, -6), (key1090, -6), (key1090, -6), (key1220, 2), (key1183, 2), (key1180, 2), (key1220, 2), (key1183, 2), (key1169, 2), (key984, 2), (key1090, 2), (key976, 2), (key1180, 2), (key1090, 2), (key976, 2)]

def rawRow11828 : Integer.Sparse Key := [(key2405, -6), (key2405, -6), (key2436, -6), (key2436, -6), (key2471, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

def rawRow11829 : Integer.Sparse Key := [(key2405, -6), (key2436, -6), (key2405, -6), (key2436, -6), (key2479, 2), (key2471, 2), (key2479, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

def rawRow11830 : Integer.Sparse Key := [(key2405, -6), (key2436, -6), (key2436, -6), (key2405, -6), (key2479, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2502, 2), (key2471, 2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

def rawRow11831 : Integer.Sparse Key := [(key2436, -6), (key2405, -6), (key2405, -6), (key2436, -6), (key2502, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2479, 2), (key2518, 2), (key2471, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2479, 2), (key2502, 2)]

def rawRow11832 : Integer.Sparse Key := [(key2436, -6), (key2405, -6), (key2436, -6), (key2405, -6), (key2502, 2), (key2518, 2), (key2502, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2502, 2), (key2471, 2), (key2502, 2), (key2479, 2)]

def rawRow11833 : Integer.Sparse Key := [(key2436, -6), (key2436, -6), (key2405, -6), (key2405, -6), (key2518, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2479, 2), (key2479, 2), (key2471, 2), (key2471, 2)]

def rawRow11834 : Integer.Sparse Key := [(key2377, -6), (key2471, -6), (key2502, -6), (key2502, -6), (key2377, 2), (key2389, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2436, 2), (key2479, 2), (key2479, 2), (key2502, 2), (key2502, 2), (key2518, 2), (key2518, 2)]

def rawRow11835 : Integer.Sparse Key := [(key2377, -6), (key2502, -6), (key2471, -6), (key2502, -6), (key2389, 2), (key2377, 2), (key2389, 2), (key2436, 2), (key2405, 2), (key2436, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2518, 2), (key2479, 2), (key2502, 2)]

def rawRow11836 : Integer.Sparse Key := [(key2377, -6), (key2502, -6), (key2502, -6), (key2471, -6), (key2389, 2), (key2389, 2), (key2377, 2), (key2436, 2), (key2436, 2), (key2405, 2), (key2518, 2), (key2502, 2), (key2518, 2), (key2479, 2), (key2502, 2), (key2479, 2)]

def rawRow11837 : Integer.Sparse Key := [(key2471, -6), (key2377, -6), (key2502, -6), (key2502, -6), (key2405, 2), (key2479, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2502, 2), (key2389, 2), (key2389, 2), (key2436, 2), (key2436, 2), (key2518, 2), (key2518, 2)]

def rawRow11838 : Integer.Sparse Key := [(key2471, -6), (key2502, -6), (key2377, -6), (key2502, -6), (key2479, 2), (key2405, 2), (key2479, 2), (key2502, 2), (key2377, 2), (key2502, 2), (key2436, 2), (key2518, 2), (key2389, 2), (key2518, 2), (key2389, 2), (key2436, 2)]

def rawRow11839 : Integer.Sparse Key := [(key2471, -6), (key2502, -6), (key2502, -6), (key2377, -6), (key2479, 2), (key2479, 2), (key2405, 2), (key2502, 2), (key2502, 2), (key2377, 2), (key2518, 2), (key2436, 2), (key2518, 2), (key2389, 2), (key2436, 2), (key2389, 2)]

def rawRow11840 : Integer.Sparse Key := [(key2502, -6), (key2377, -6), (key2471, -6), (key2502, -6), (key2436, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2518, 2), (key2377, 2), (key2389, 2), (key2405, 2), (key2436, 2), (key2479, 2), (key2502, 2)]

def rawRow11841 : Integer.Sparse Key := [(key2502, -6), (key2377, -6), (key2502, -6), (key2471, -6), (key2436, 2), (key2518, 2), (key2502, 2), (key2389, 2), (key2518, 2), (key2479, 2), (key2389, 2), (key2377, 2), (key2436, 2), (key2405, 2), (key2502, 2), (key2479, 2)]

def rawRow11842 : Integer.Sparse Key := [(key2502, -6), (key2471, -6), (key2377, -6), (key2502, -6), (key2502, 2), (key2436, 2), (key2518, 2), (key2479, 2), (key2389, 2), (key2518, 2), (key2405, 2), (key2479, 2), (key2377, 2), (key2502, 2), (key2389, 2), (key2436, 2)]

def rawRow11843 : Integer.Sparse Key := [(key2502, -6), (key2471, -6), (key2502, -6), (key2377, -6), (key2502, 2), (key2518, 2), (key2436, 2), (key2479, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2405, 2), (key2502, 2), (key2377, 2), (key2436, 2), (key2389, 2)]

def rawRow11844 : Integer.Sparse Key := [(key2502, -6), (key2502, -6), (key2377, -6), (key2471, -6), (key2518, 2), (key2436, 2), (key2502, 2), (key2518, 2), (key2389, 2), (key2479, 2), (key2436, 2), (key2502, 2), (key2389, 2), (key2479, 2), (key2377, 2), (key2405, 2)]

def rawRow11845 : Integer.Sparse Key := [(key2502, -6), (key2502, -6), (key2471, -6), (key2377, -6), (key2518, 2), (key2502, 2), (key2436, 2), (key2518, 2), (key2479, 2), (key2389, 2), (key2502, 2), (key2436, 2), (key2479, 2), (key2389, 2), (key2405, 2), (key2377, 2)]

def rawRow11846 : Integer.Sparse Key := [(key2357, -6), (key2361, -6), (key2366, -6), (key2366, -6), (key2456, 2), (key2456, 2), (key2461, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2)]

def rawRow11847 : Integer.Sparse Key := [(key2357, -6), (key2363, -6), (key2361, -6), (key2366, -6), (key2456, 2), (key2461, 2), (key2456, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2523, 2), (key2461, 2), (key2523, 2)]

def rawRow11848 : Integer.Sparse Key := [(key2363, -6), (key2357, -6), (key2361, -6), (key2366, -6), (key2461, 2), (key2456, 2), (key2456, 2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2523, 2), (key2523, 2), (key2461, 2)]

def rawRow11849 : Integer.Sparse Key := [(key2357, -6), (key2363, -6), (key2363, -6), (key2361, -6), (key2517, 2), (key2523, 2), (key2523, 2), (key2456, 2), (key2461, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2456, 2), (key2456, 2), (key2517, 2)]

def rawRow11850 : Integer.Sparse Key := [(key2363, -6), (key2357, -6), (key2363, -6), (key2361, -6), (key2523, 2), (key2517, 2), (key2523, 2), (key2461, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2461, 2), (key2456, 2), (key2517, 2), (key2456, 2)]

def rawRow11851 : Integer.Sparse Key := [(key2363, -6), (key2363, -6), (key2357, -6), (key2361, -6), (key2523, 2), (key2523, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2461, 2), (key2461, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2456, 2)]

def rawRow11852 : Integer.Sparse Key := [(key2452, -6), (key2452, -6), (key2458, -6), (key2519, -6), (key2357, 2), (key2361, 2), (key2366, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2523, 2), (key2523, 2), (key2567, 2), (key2579, 2), (key2579, 2)]

def rawRow11853 : Integer.Sparse Key := [(key2452, -6), (key2458, -6), (key2452, -6), (key2519, -6), (key2357, 2), (key2363, 2), (key2361, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2579, 2), (key2567, 2), (key2579, 2)]

def rawRow11854 : Integer.Sparse Key := [(key2458, -6), (key2452, -6), (key2452, -6), (key2519, -6), (key2363, 2), (key2357, 2), (key2361, 2), (key2523, 2), (key2517, 2), (key2523, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2579, 2), (key2579, 2), (key2567, 2)]

def rawRow11855 : Integer.Sparse Key := [(key2452, -6), (key2452, -6), (key2519, -6), (key2458, -6), (key2452, 2), (key2452, 2), (key2519, 2), (key2357, 2), (key2361, 2), (key2517, 2), (key2517, 2), (key2579, 2), (key2579, 2), (key2366, 2), (key2523, 2), (key2523, 2)]

def rawRow11856 : Integer.Sparse Key := [(key2452, -6), (key2519, -6), (key2452, -6), (key2458, -6), (key2452, 2), (key2519, 2), (key2452, 2), (key2528, 2), (key2560, 2), (key2357, 2), (key2560, 2), (key2361, 2), (key2517, 2), (key2523, 2), (key2366, 2), (key2523, 2)]

def rawRow11857 : Integer.Sparse Key := [(key2519, -6), (key2452, -6), (key2452, -6), (key2458, -6), (key2519, 2), (key2452, 2), (key2452, 2), (key2560, 2), (key2528, 2), (key2560, 2), (key2357, 2), (key2517, 2), (key2361, 2), (key2523, 2), (key2523, 2), (key2366, 2)]

def rawRow11858 : Integer.Sparse Key := [(key2452, -6), (key2458, -6), (key2519, -6), (key2452, -6), (key2528, 2), (key2530, 2), (key2560, 2), (key2357, 2), (key2363, 2), (key2452, 2), (key2530, 2), (key2519, 2), (key2560, 2), (key2361, 2), (key2456, 2), (key2517, 2)]

def rawRow11859 : Integer.Sparse Key := [(key2458, -6), (key2452, -6), (key2519, -6), (key2452, -6), (key2530, 2), (key2528, 2), (key2560, 2), (key2363, 2), (key2357, 2), (key2530, 2), (key2452, 2), (key2560, 2), (key2519, 2), (key2361, 2), (key2517, 2), (key2456, 2)]

def rawRow11860 : Integer.Sparse Key := [(key2452, -6), (key2519, -6), (key2458, -6), (key2452, -6), (key2528, 2), (key2560, 2), (key2530, 2), (key2452, 2), (key2519, 2), (key2357, 2), (key2560, 2), (key2363, 2), (key2530, 2), (key2456, 2), (key2361, 2), (key2517, 2)]

def rawRow11861 : Integer.Sparse Key := [(key2519, -6), (key2452, -6), (key2458, -6), (key2452, -6), (key2560, 2), (key2528, 2), (key2530, 2), (key2519, 2), (key2452, 2), (key2560, 2), (key2357, 2), (key2530, 2), (key2363, 2), (key2456, 2), (key2517, 2), (key2361, 2)]

def rawRow11862 : Integer.Sparse Key := [(key2458, -6), (key2519, -6), (key2452, -6), (key2452, -6), (key2530, 2), (key2560, 2), (key2528, 2), (key2530, 2), (key2560, 2), (key2363, 2), (key2519, 2), (key2357, 2), (key2452, 2), (key2517, 2), (key2361, 2), (key2456, 2)]

def rawRow11863 : Integer.Sparse Key := [(key2519, -6), (key2458, -6), (key2452, -6), (key2452, -6), (key2560, 2), (key2530, 2), (key2528, 2), (key2560, 2), (key2530, 2), (key2519, 2), (key2363, 2), (key2452, 2), (key2357, 2), (key2517, 2), (key2456, 2), (key2361, 2)]

def rawRow11864 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2411, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2437, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2443, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2509, 1), (key2509, 1), (key2524, 1), (key2524, 1)]

def rawRow11865 : Integer.Sparse Key := [(key2406, -2), (key2411, -2), (key2406, -2), (key2437, -2), (key2443, -2), (key2406, -2), (key2443, -2), (key2406, -2), (key2437, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2480, 1), (key2484, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2484, 1), (key2509, 1)]

def rawRow11866 : Integer.Sparse Key := [(key2411, -2), (key2406, -2), (key2406, -2), (key2443, -2), (key2437, -2), (key2443, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2484, 1), (key2480, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2484, 1)]

def rawRow11867 : Integer.Sparse Key := [(key2437, -2), (key2443, -2), (key2443, -2), (key2406, -2), (key2411, -2), (key2406, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2503, 1), (key2509, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1)]

def rawRow11868 : Integer.Sparse Key := [(key2443, -2), (key2437, -2), (key2443, -2), (key2411, -2), (key2406, -2), (key2443, -2), (key2406, -2), (key2443, -2), (key2411, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2509, 1), (key2503, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1)]

def rawRow11869 : Integer.Sparse Key := [(key2443, -2), (key2443, -2), (key2437, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2411, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2406, -2), (key2524, 1), (key2524, 1), (key2509, 1), (key2509, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1), (key2509, 1), (key2509, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1)]

def rawRow11870 : Integer.Sparse Key := [(key2587, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2843, -2), (key2966, -2), (key2966, -2), (key2968, -2), (key2968, -2), (key2880, -2), (key2989, -2), (key2989, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2571, 1), (key2571, 1), (key2576, 1), (key2576, 1), (key2580, 1), (key2580, 1)]

def rawRow11871 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2587, -2), (key2966, -2), (key2968, -2), (key2843, -2), (key2968, -2), (key2843, -2), (key2966, -2), (key2989, -2), (key2880, -2), (key2989, -2), (key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2580, 1), (key2571, 1), (key2576, 1)]

def rawRow11872 : Integer.Sparse Key := [(key2593, -2), (key2587, -2), (key2587, -2), (key2968, -2), (key2966, -2), (key2968, -2), (key2843, -2), (key2966, -2), (key2843, -2), (key2989, -2), (key2989, -2), (key2880, -2), (key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2580, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2571, 1)]

def rawRow11873 : Integer.Sparse Key := [(key2843, -2), (key2843, -2), (key2880, -2), (key2587, -2), (key2587, -2), (key2966, -2), (key2966, -2), (key2989, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2968, -2), (key2766, 1), (key2766, 1), (key2887, 1), (key2887, 1), (key2910, 1), (key2910, 1), (key2587, 1), (key2587, 1), (key2966, 1), (key2966, 1), (key2989, 1), (key2989, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2580, 1), (key2580, 1), (key2394, 1), (key2394, 1), (key2443, 1), (key2443, 1), (key2524, 1), (key2524, 1)]

def rawRow11874 : Integer.Sparse Key := [(key2843, -2), (key2880, -2), (key2843, -2), (key2966, -2), (key2989, -2), (key2587, -2), (key2989, -2), (key2587, -2), (key2966, -2), (key2968, -2), (key2593, -2), (key2968, -2), (key2887, 1), (key2910, 1), (key2766, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key3002, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2524, 1), (key2394, 1), (key2443, 1)]

def rawRow11875 : Integer.Sparse Key := [(key2880, -2), (key2843, -2), (key2843, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2587, -2), (key2966, -2), (key2587, -2), (key2968, -2), (key2968, -2), (key2593, -2), (key2910, 1), (key2887, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2766, 1), (key2989, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2587, 1), (key3002, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key2437, 1), (key2390, 1), (key2524, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2394, 1)]

def rawRow11876 : Integer.Sparse Key := [(key2966, -2), (key2968, -2), (key2989, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2968, -2), (key2880, -2), (key2989, -2), (key2587, -2), (key2843, -2), (key2966, -2), (key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1), (key2587, 1), (key2600, 1), (key2766, 1), (key2931, 1), (key2910, 1), (key2989, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1)]

def rawRow11877 : Integer.Sparse Key := [(key2968, -2), (key2966, -2), (key2989, -2), (key2593, -2), (key2587, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2880, -2), (key2587, -2), (key2966, -2), (key2843, -2), (key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1), (key2600, 1), (key2587, 1), (key2931, 1), (key2766, 1), (key2989, 1), (key2910, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1)]

def rawRow11878 : Integer.Sparse Key := [(key2966, -2), (key2989, -2), (key2968, -2), (key2843, -2), (key2880, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2843, -2), (key2587, -2), (key2966, -2), (key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2766, 1), (key2910, 1), (key2587, 1), (key2989, 1), (key2600, 1), (key2931, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1)]

def rawRow11879 : Integer.Sparse Key := [(key2989, -2), (key2966, -2), (key2968, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1), (key2910, 1), (key2766, 1), (key2989, 1), (key2587, 1), (key2931, 1), (key2600, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1)]

def rawRow11880 : Integer.Sparse Key := [(key2968, -2), (key2989, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2587, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1), (key2931, 1), (key2989, 1), (key2600, 1), (key2910, 1), (key2587, 1), (key2766, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1)]

def rawRow11881 : Integer.Sparse Key := [(key2989, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2880, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2966, -2), (key2843, -2), (key2587, -2), (key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1), (key2989, 1), (key2931, 1), (key2910, 1), (key2600, 1), (key2766, 1), (key2587, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

def rawRow11882 : Integer.Sparse Key := [(key2360, -24), (key2455, 6), (key2455, 6), (key2516, 6), (key2516, 6)]

def rawRow11883 : Integer.Sparse Key := [(key2360, -24), (key2455, 6), (key2516, 6), (key2455, 6), (key2516, 6)]

def rawRow11884 : Integer.Sparse Key := [(key2360, -24), (key2455, 6), (key2516, 6), (key2516, 6), (key2455, 6)]

def rawRow11885 : Integer.Sparse Key := [(key2360, -24), (key2516, 6), (key2455, 6), (key2455, 6), (key2516, 6)]

def rawRow11886 : Integer.Sparse Key := [(key2360, -24), (key2516, 6), (key2455, 6), (key2516, 6), (key2455, 6)]

def rawRow11887 : Integer.Sparse Key := [(key2360, -24), (key2516, 6), (key2516, 6), (key2455, 6), (key2455, 6)]

def rawRow11888 : Integer.Sparse Key := [(key2455, -24), (key2360, 6), (key2455, 6), (key2516, 6), (key2516, 6)]

def rawRow11889 : Integer.Sparse Key := [(key2455, -24), (key2360, 6), (key2516, 6), (key2455, 6), (key2516, 6)]

def rawRow11890 : Integer.Sparse Key := [(key2455, -24), (key2360, 6), (key2516, 6), (key2516, 6), (key2455, 6)]

def rawRow11891 : Integer.Sparse Key := [(key2455, -24), (key2455, 6), (key2360, 6), (key2516, 6), (key2516, 6)]

def rawRow11892 : Integer.Sparse Key := [(key2455, -24), (key2455, 6), (key2516, 6), (key2360, 6), (key2516, 6)]

def rawRow11893 : Integer.Sparse Key := [(key2455, -24), (key2455, 6), (key2516, 6), (key2516, 6), (key2360, 6)]

def rawRow11894 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2360, 6), (key2455, 6), (key2516, 6)]

def rawRow11895 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2360, 6), (key2516, 6), (key2455, 6)]

def rawRow11896 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2455, 6), (key2360, 6), (key2516, 6)]

def rawRow11897 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2455, 6), (key2516, 6), (key2360, 6)]

def rawRow11898 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2516, 6), (key2360, 6), (key2455, 6)]

def rawRow11899 : Integer.Sparse Key := [(key2455, -24), (key2516, 6), (key2516, 6), (key2455, 6), (key2360, 6)]

def rawRow11900 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2383, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2390, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2394, -2), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2443, 2)]

def rawRow11901 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2378, -2), (key2390, -2), (key2394, -2), (key2378, -2), (key2394, -2), (key2378, -2), (key2390, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2443, 2)]

def rawRow11902 : Integer.Sparse Key := [(key2383, -2), (key2378, -2), (key2378, -2), (key2394, -2), (key2390, -2), (key2394, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2443, 2), (key2411, 2)]

def rawRow11903 : Integer.Sparse Key := [(key2390, -2), (key2394, -2), (key2394, -2), (key2378, -2), (key2383, -2), (key2378, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2406, 2), (key2406, 2), (key2437, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11904 : Integer.Sparse Key := [(key2394, -2), (key2390, -2), (key2394, -2), (key2383, -2), (key2378, -2), (key2394, -2), (key2378, -2), (key2394, -2), (key2383, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2406, 2)]

def rawRow11905 : Integer.Sparse Key := [(key2394, -2), (key2394, -2), (key2390, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2383, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2378, -2), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2406, 2)]

def rawRow11906 : Integer.Sparse Key := [(key2766, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2843, -2), (key2887, -2), (key2887, -2), (key2889, -2), (key2889, -2), (key2880, -2), (key2910, -2), (key2910, -2), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2843, 2), (key2966, 2), (key2966, 2), (key2968, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2989, 2)]

def rawRow11907 : Integer.Sparse Key := [(key2766, -2), (key2772, -2), (key2766, -2), (key2887, -2), (key2889, -2), (key2843, -2), (key2889, -2), (key2843, -2), (key2887, -2), (key2910, -2), (key2880, -2), (key2910, -2), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2880, 2), (key2989, 2)]

def rawRow11908 : Integer.Sparse Key := [(key2772, -2), (key2766, -2), (key2766, -2), (key2889, -2), (key2887, -2), (key2889, -2), (key2843, -2), (key2887, -2), (key2843, -2), (key2910, -2), (key2910, -2), (key2880, -2), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2880, 2)]

def rawRow11909 : Integer.Sparse Key := [(key2843, -2), (key2843, -2), (key2880, -2), (key2766, -2), (key2766, -2), (key2887, -2), (key2887, -2), (key2910, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2889, -2), (key2843, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2968, 2)]

def rawRow11910 : Integer.Sparse Key := [(key2843, -2), (key2880, -2), (key2843, -2), (key2887, -2), (key2910, -2), (key2766, -2), (key2910, -2), (key2766, -2), (key2887, -2), (key2889, -2), (key2772, -2), (key2889, -2), (key2843, 2), (key2880, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2593, 2), (key2968, 2)]

def rawRow11911 : Integer.Sparse Key := [(key2880, -2), (key2843, -2), (key2843, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2766, -2), (key2887, -2), (key2766, -2), (key2889, -2), (key2889, -2), (key2772, -2), (key2880, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key2968, 2), (key2968, 2), (key2593, 2)]

def rawRow11912 : Integer.Sparse Key := [(key2887, -2), (key2889, -2), (key2910, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2889, -2), (key2880, -2), (key2910, -2), (key2766, -2), (key2843, -2), (key2887, -2), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2587, 2), (key2843, 2), (key2966, 2)]

def rawRow11913 : Integer.Sparse Key := [(key2889, -2), (key2887, -2), (key2910, -2), (key2772, -2), (key2766, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2880, -2), (key2766, -2), (key2887, -2), (key2843, -2), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2880, 2), (key2587, 2), (key2966, 2), (key2843, 2)]

def rawRow11914 : Integer.Sparse Key := [(key2887, -2), (key2910, -2), (key2889, -2), (key2843, -2), (key2880, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2843, -2), (key2766, -2), (key2887, -2), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2843, 2), (key2587, 2), (key2966, 2)]

def rawRow11915 : Integer.Sparse Key := [(key2910, -2), (key2887, -2), (key2889, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2593, 2), (key2843, 2), (key2966, 2), (key2587, 2)]

def rawRow11916 : Integer.Sparse Key := [(key2889, -2), (key2910, -2), (key2887, -2), (key2889, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2766, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2587, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2843, 2)]

def rawRow11917 : Integer.Sparse Key := [(key2910, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2880, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2887, -2), (key2843, -2), (key2766, -2), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2880, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2966, 2), (key2843, 2), (key2587, 2)]

def rawRow11918 : Integer.Sparse Key := [(key1531, -2), (key1531, -2), (key1536, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1765, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1768, -2), (key1609, 1), (key1609, 1), (key1648, 1), (key1648, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1), (key1648, 1), (key1648, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1809, 1), (key1809, 1), (key1837, 1), (key1837, 1)]

def rawRow11919 : Integer.Sparse Key := [(key1531, -2), (key1536, -2), (key1531, -2), (key1765, -2), (key1768, -2), (key1531, -2), (key1768, -2), (key1531, -2), (key1765, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1648, 1), (key1651, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1651, 1), (key1809, 1)]

def rawRow11920 : Integer.Sparse Key := [(key1536, -2), (key1531, -2), (key1531, -2), (key1768, -2), (key1765, -2), (key1768, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1651, 1), (key1648, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1648, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1809, 1), (key1651, 1)]

def rawRow11921 : Integer.Sparse Key := [(key1765, -2), (key1768, -2), (key1768, -2), (key1531, -2), (key1536, -2), (key1531, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1806, 1), (key1809, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1809, 1), (key1651, 1), (key1809, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1648, 1), (key1806, 1)]

def rawRow11922 : Integer.Sparse Key := [(key1768, -2), (key1765, -2), (key1768, -2), (key1536, -2), (key1531, -2), (key1768, -2), (key1531, -2), (key1768, -2), (key1536, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1809, 1), (key1806, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1651, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1806, 1), (key1648, 1)]

def rawRow11923 : Integer.Sparse Key := [(key1768, -2), (key1768, -2), (key1765, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1536, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1531, -2), (key1837, 1), (key1837, 1), (key1809, 1), (key1809, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1), (key1809, 1), (key1809, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1648, 1), (key1648, 1), (key1609, 1), (key1609, 1)]

def rawRow11924 : Integer.Sparse Key := [(key1256, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1609, -2), (key1806, -2), (key1806, -2), (key1809, -2), (key1809, -2), (key1642, -2), (key1832, -2), (key1832, -2), (key1256, 1), (key1256, 1), (key1265, 1), (key1265, 1), (key1268, 1), (key1268, 1), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1), (key1648, 1), (key1648, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1674, 1), (key1674, 1), (key1832, 1), (key1832, 1), (key1848, 1), (key1848, 1)]

def rawRow11925 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1256, -2), (key1806, -2), (key1809, -2), (key1609, -2), (key1809, -2), (key1609, -2), (key1806, -2), (key1832, -2), (key1642, -2), (key1832, -2), (key1265, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1848, 1), (key1674, 1), (key1832, 1)]

def rawRow11926 : Integer.Sparse Key := [(key1261, -2), (key1256, -2), (key1256, -2), (key1809, -2), (key1806, -2), (key1809, -2), (key1609, -2), (key1806, -2), (key1609, -2), (key1832, -2), (key1832, -2), (key1642, -2), (key1268, 1), (key1265, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1256, 1), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1648, 1), (key1848, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1832, 1), (key1674, 1)]

def rawRow11927 : Integer.Sparse Key := [(key1609, -2), (key1609, -2), (key1642, -2), (key1256, -2), (key1256, -2), (key1806, -2), (key1806, -2), (key1832, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1809, -2), (key1531, 1), (key1531, 1), (key1648, 1), (key1648, 1), (key1674, 1), (key1674, 1), (key1256, 1), (key1256, 1), (key1806, 1), (key1806, 1), (key1832, 1), (key1832, 1), (key1265, 1), (key1265, 1), (key1765, 1), (key1765, 1), (key1848, 1), (key1848, 1), (key1268, 1), (key1268, 1), (key1768, 1), (key1768, 1), (key1837, 1), (key1837, 1)]

def rawRow11928 : Integer.Sparse Key := [(key1609, -2), (key1642, -2), (key1609, -2), (key1806, -2), (key1832, -2), (key1256, -2), (key1832, -2), (key1256, -2), (key1806, -2), (key1809, -2), (key1261, -2), (key1809, -2), (key1648, 1), (key1674, 1), (key1531, 1), (key1674, 1), (key1531, 1), (key1648, 1), (key1806, 1), (key1832, 1), (key1256, 1), (key1832, 1), (key1256, 1), (key1806, 1), (key1765, 1), (key1848, 1), (key1265, 1), (key1848, 1), (key1265, 1), (key1765, 1), (key1768, 1), (key1837, 1), (key1268, 1), (key1837, 1), (key1268, 1), (key1768, 1)]

def rawRow11929 : Integer.Sparse Key := [(key1642, -2), (key1609, -2), (key1609, -2), (key1832, -2), (key1806, -2), (key1832, -2), (key1256, -2), (key1806, -2), (key1256, -2), (key1809, -2), (key1809, -2), (key1261, -2), (key1674, 1), (key1648, 1), (key1674, 1), (key1531, 1), (key1648, 1), (key1531, 1), (key1832, 1), (key1806, 1), (key1832, 1), (key1256, 1), (key1806, 1), (key1256, 1), (key1848, 1), (key1765, 1), (key1848, 1), (key1265, 1), (key1765, 1), (key1265, 1), (key1837, 1), (key1768, 1), (key1837, 1), (key1268, 1), (key1768, 1), (key1268, 1)]

def rawRow11930 : Integer.Sparse Key := [(key1806, -2), (key1809, -2), (key1832, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1809, -2), (key1642, -2), (key1832, -2), (key1256, -2), (key1609, -2), (key1806, -2), (key1765, 1), (key1768, 1), (key1806, 1), (key1837, 1), (key1832, 1), (key1848, 1), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1), (key1256, 1), (key1268, 1), (key1531, 1), (key1768, 1), (key1674, 1), (key1832, 1), (key1256, 1), (key1265, 1), (key1531, 1), (key1765, 1), (key1648, 1), (key1806, 1)]

def rawRow11931 : Integer.Sparse Key := [(key1809, -2), (key1806, -2), (key1832, -2), (key1261, -2), (key1256, -2), (key1809, -2), (key1609, -2), (key1832, -2), (key1642, -2), (key1256, -2), (key1806, -2), (key1609, -2), (key1768, 1), (key1765, 1), (key1837, 1), (key1806, 1), (key1848, 1), (key1832, 1), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1), (key1268, 1), (key1256, 1), (key1768, 1), (key1531, 1), (key1832, 1), (key1674, 1), (key1265, 1), (key1256, 1), (key1765, 1), (key1531, 1), (key1806, 1), (key1648, 1)]

def rawRow11932 : Integer.Sparse Key := [(key1806, -2), (key1832, -2), (key1809, -2), (key1609, -2), (key1642, -2), (key1256, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1609, -2), (key1256, -2), (key1806, -2), (key1806, 1), (key1832, 1), (key1765, 1), (key1848, 1), (key1768, 1), (key1837, 1), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1), (key1531, 1), (key1674, 1), (key1256, 1), (key1832, 1), (key1268, 1), (key1768, 1), (key1531, 1), (key1648, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1765, 1)]

def rawRow11933 : Integer.Sparse Key := [(key1832, -2), (key1806, -2), (key1809, -2), (key1642, -2), (key1609, -2), (key1832, -2), (key1256, -2), (key1809, -2), (key1261, -2), (key1609, -2), (key1806, -2), (key1256, -2), (key1832, 1), (key1806, 1), (key1848, 1), (key1765, 1), (key1837, 1), (key1768, 1), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1), (key1674, 1), (key1531, 1), (key1832, 1), (key1256, 1), (key1768, 1), (key1268, 1), (key1648, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1765, 1), (key1265, 1)]

def rawRow11934 : Integer.Sparse Key := [(key1809, -2), (key1832, -2), (key1806, -2), (key1809, -2), (key1832, -2), (key1261, -2), (key1642, -2), (key1256, -2), (key1609, -2), (key1806, -2), (key1256, -2), (key1609, -2), (key1837, 1), (key1848, 1), (key1768, 1), (key1832, 1), (key1765, 1), (key1806, 1), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1), (key1768, 1), (key1832, 1), (key1268, 1), (key1674, 1), (key1256, 1), (key1531, 1), (key1765, 1), (key1806, 1), (key1265, 1), (key1648, 1), (key1256, 1), (key1531, 1)]

def rawRow11935 : Integer.Sparse Key := [(key1832, -2), (key1809, -2), (key1806, -2), (key1832, -2), (key1809, -2), (key1642, -2), (key1261, -2), (key1609, -2), (key1256, -2), (key1806, -2), (key1609, -2), (key1256, -2), (key1848, 1), (key1837, 1), (key1832, 1), (key1768, 1), (key1806, 1), (key1765, 1), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1), (key1832, 1), (key1768, 1), (key1674, 1), (key1268, 1), (key1531, 1), (key1256, 1), (key1806, 1), (key1765, 1), (key1648, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

def rawRow11936 : Integer.Sparse Key := [(key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2509, 1), (key2509, 1), (key2524, 1), (key2524, 1), (key2569, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2571, -2), (key2571, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2580, -2)]

def rawRow11937 : Integer.Sparse Key := [(key2480, 1), (key2484, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2571, -2), (key2569, -2), (key2571, -2), (key2576, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2580, -2), (key2571, -2), (key2576, -2)]

def rawRow11938 : Integer.Sparse Key := [(key2484, 1), (key2480, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2484, 1), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2569, -2), (key2580, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2576, -2), (key2571, -2)]

def rawRow11939 : Integer.Sparse Key := [(key2503, 1), (key2509, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2580, -2), (key2569, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2571, -2), (key2576, -2)]

def rawRow11940 : Integer.Sparse Key := [(key2509, 1), (key2503, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2576, -2), (key2580, -2), (key2576, -2), (key2571, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2569, -2), (key2576, -2), (key2571, -2)]

def rawRow11941 : Integer.Sparse Key := [(key2524, 1), (key2524, 1), (key2509, 1), (key2509, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1), (key2509, 1), (key2509, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1), (key2580, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2576, -2), (key2576, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2569, -2)]

def rawRow11942 : Integer.Sparse Key := [(key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2571, 1), (key2571, 1), (key2576, 1), (key2576, 1), (key2580, 1), (key2580, 1), (key2383, -2), (key2394, -2), (key2394, -2), (key2411, -2), (key2443, -2), (key2443, -2), (key2484, -2), (key2484, -2), (key2509, -2), (key2509, -2), (key2524, -2), (key2524, -2)]

def rawRow11943 : Integer.Sparse Key := [(key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2394, -2), (key2383, -2), (key2394, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2509, -2), (key2524, -2), (key2484, -2), (key2524, -2), (key2484, -2), (key2509, -2)]

def rawRow11944 : Integer.Sparse Key := [(key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2580, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2571, 1), (key2394, -2), (key2394, -2), (key2383, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2524, -2), (key2509, -2), (key2524, -2), (key2484, -2), (key2509, -2), (key2484, -2)]

def rawRow11945 : Integer.Sparse Key := [(key2766, 1), (key2766, 1), (key2887, 1), (key2887, 1), (key2910, 1), (key2910, 1), (key2587, 1), (key2587, 1), (key2966, 1), (key2966, 1), (key2989, 1), (key2989, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2580, 1), (key2580, 1), (key2394, 1), (key2394, 1), (key2443, 1), (key2443, 1), (key2524, 1), (key2524, 1), (key2411, -2), (key2484, -2), (key2484, -2), (key2383, -2), (key2509, -2), (key2509, -2), (key2394, -2), (key2394, -2), (key2443, -2), (key2443, -2), (key2524, -2), (key2524, -2)]

def rawRow11946 : Integer.Sparse Key := [(key2887, 1), (key2910, 1), (key2766, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key3002, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2484, -2), (key2411, -2), (key2484, -2), (key2509, -2), (key2383, -2), (key2509, -2), (key2443, -2), (key2524, -2), (key2394, -2), (key2524, -2), (key2394, -2), (key2443, -2)]

def rawRow11947 : Integer.Sparse Key := [(key2910, 1), (key2887, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2766, 1), (key2989, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2587, 1), (key3002, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key2437, 1), (key2390, 1), (key2524, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2394, 1), (key2484, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2509, -2), (key2383, -2), (key2524, -2), (key2443, -2), (key2524, -2), (key2394, -2), (key2443, -2), (key2394, -2)]

def rawRow11948 : Integer.Sparse Key := [(key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1), (key2587, 1), (key2600, 1), (key2766, 1), (key2931, 1), (key2910, 1), (key2989, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2443, -2), (key2509, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2524, -2), (key2383, -2), (key2394, -2), (key2411, -2), (key2443, -2), (key2484, -2), (key2509, -2)]

def rawRow11949 : Integer.Sparse Key := [(key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1), (key2600, 1), (key2587, 1), (key2931, 1), (key2766, 1), (key2989, 1), (key2910, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1), (key2443, -2), (key2524, -2), (key2509, -2), (key2394, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2383, -2), (key2443, -2), (key2411, -2), (key2509, -2), (key2484, -2)]

def rawRow11950 : Integer.Sparse Key := [(key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2766, 1), (key2910, 1), (key2587, 1), (key2989, 1), (key2600, 1), (key2931, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2509, -2), (key2443, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2524, -2), (key2411, -2), (key2484, -2), (key2383, -2), (key2509, -2), (key2394, -2), (key2443, -2)]

def rawRow11951 : Integer.Sparse Key := [(key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1), (key2910, 1), (key2766, 1), (key2989, 1), (key2587, 1), (key2931, 1), (key2600, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1), (key2509, -2), (key2524, -2), (key2443, -2), (key2484, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2383, -2), (key2443, -2), (key2394, -2)]

def rawRow11952 : Integer.Sparse Key := [(key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1), (key2931, 1), (key2989, 1), (key2600, 1), (key2910, 1), (key2587, 1), (key2766, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1), (key2524, -2), (key2443, -2), (key2509, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2443, -2), (key2509, -2), (key2394, -2), (key2484, -2), (key2383, -2), (key2411, -2)]

def rawRow11953 : Integer.Sparse Key := [(key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1), (key2989, 1), (key2931, 1), (key2910, 1), (key2600, 1), (key2766, 1), (key2587, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1), (key2524, -2), (key2509, -2), (key2443, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2509, -2), (key2443, -2), (key2484, -2), (key2394, -2), (key2411, -2), (key2383, -2)]

def rawRow11954 : Integer.Sparse Key := [(key1529, -6), (key1529, -6), (key1763, -6), (key1763, -6), (key1607, 2), (key1646, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1646, 2), (key1646, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1835, 2)]

def rawRow11955 : Integer.Sparse Key := [(key1529, -6), (key1763, -6), (key1529, -6), (key1763, -6), (key1646, 2), (key1607, 2), (key1646, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1835, 2), (key1646, 2), (key1804, 2)]

def rawRow11956 : Integer.Sparse Key := [(key1529, -6), (key1763, -6), (key1763, -6), (key1529, -6), (key1646, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1804, 2), (key1607, 2), (key1835, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1804, 2), (key1646, 2)]

def rawRow11957 : Integer.Sparse Key := [(key1763, -6), (key1529, -6), (key1529, -6), (key1763, -6), (key1804, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1646, 2), (key1835, 2), (key1607, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1646, 2), (key1804, 2)]

def rawRow11958 : Integer.Sparse Key := [(key1763, -6), (key1529, -6), (key1763, -6), (key1529, -6), (key1804, 2), (key1835, 2), (key1804, 2), (key1646, 2), (key1835, 2), (key1646, 2), (key1646, 2), (key1607, 2), (key1804, 2), (key1607, 2), (key1804, 2), (key1646, 2)]

def rawRow11959 : Integer.Sparse Key := [(key1763, -6), (key1763, -6), (key1529, -6), (key1529, -6), (key1835, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1646, 2), (key1804, 2), (key1804, 2), (key1646, 2), (key1646, 2), (key1607, 2), (key1607, 2)]

def rawRow11960 : Integer.Sparse Key := [(key1254, -6), (key1607, -6), (key1804, -6), (key1804, -6), (key1254, 2), (key1263, 2), (key1263, 2), (key1529, 2), (key1763, 2), (key1763, 2), (key1646, 2), (key1646, 2), (key1804, 2), (key1804, 2), (key1835, 2), (key1835, 2)]

def rawRow11961 : Integer.Sparse Key := [(key1254, -6), (key1804, -6), (key1607, -6), (key1804, -6), (key1263, 2), (key1254, 2), (key1263, 2), (key1763, 2), (key1529, 2), (key1763, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1835, 2), (key1646, 2), (key1804, 2)]

def rawRow11962 : Integer.Sparse Key := [(key1254, -6), (key1804, -6), (key1804, -6), (key1607, -6), (key1263, 2), (key1263, 2), (key1254, 2), (key1763, 2), (key1763, 2), (key1529, 2), (key1835, 2), (key1804, 2), (key1835, 2), (key1646, 2), (key1804, 2), (key1646, 2)]

def rawRow11963 : Integer.Sparse Key := [(key1607, -6), (key1254, -6), (key1804, -6), (key1804, -6), (key1529, 2), (key1646, 2), (key1646, 2), (key1254, 2), (key1804, 2), (key1804, 2), (key1263, 2), (key1263, 2), (key1763, 2), (key1763, 2), (key1835, 2), (key1835, 2)]

def rawRow11964 : Integer.Sparse Key := [(key1607, -6), (key1804, -6), (key1254, -6), (key1804, -6), (key1646, 2), (key1529, 2), (key1646, 2), (key1804, 2), (key1254, 2), (key1804, 2), (key1763, 2), (key1835, 2), (key1263, 2), (key1835, 2), (key1263, 2), (key1763, 2)]

def rawRow11965 : Integer.Sparse Key := [(key1607, -6), (key1804, -6), (key1804, -6), (key1254, -6), (key1646, 2), (key1646, 2), (key1529, 2), (key1804, 2), (key1804, 2), (key1254, 2), (key1835, 2), (key1763, 2), (key1835, 2), (key1263, 2), (key1763, 2), (key1263, 2)]

def rawRow11966 : Integer.Sparse Key := [(key1804, -6), (key1254, -6), (key1607, -6), (key1804, -6), (key1763, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1835, 2), (key1254, 2), (key1263, 2), (key1529, 2), (key1763, 2), (key1646, 2), (key1804, 2)]

def rawRow11967 : Integer.Sparse Key := [(key1804, -6), (key1254, -6), (key1804, -6), (key1607, -6), (key1763, 2), (key1835, 2), (key1804, 2), (key1263, 2), (key1835, 2), (key1646, 2), (key1263, 2), (key1254, 2), (key1763, 2), (key1529, 2), (key1804, 2), (key1646, 2)]

def rawRow11968 : Integer.Sparse Key := [(key1804, -6), (key1607, -6), (key1254, -6), (key1804, -6), (key1804, 2), (key1763, 2), (key1835, 2), (key1646, 2), (key1263, 2), (key1835, 2), (key1529, 2), (key1646, 2), (key1254, 2), (key1804, 2), (key1263, 2), (key1763, 2)]

def rawRow11969 : Integer.Sparse Key := [(key1804, -6), (key1607, -6), (key1804, -6), (key1254, -6), (key1804, 2), (key1835, 2), (key1763, 2), (key1646, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1529, 2), (key1804, 2), (key1254, 2), (key1763, 2), (key1263, 2)]

def rawRow11970 : Integer.Sparse Key := [(key1804, -6), (key1804, -6), (key1254, -6), (key1607, -6), (key1835, 2), (key1763, 2), (key1804, 2), (key1835, 2), (key1263, 2), (key1646, 2), (key1763, 2), (key1804, 2), (key1263, 2), (key1646, 2), (key1254, 2), (key1529, 2)]

def rawRow11971 : Integer.Sparse Key := [(key1804, -6), (key1804, -6), (key1607, -6), (key1254, -6), (key1835, 2), (key1804, 2), (key1763, 2), (key1835, 2), (key1646, 2), (key1263, 2), (key1804, 2), (key1763, 2), (key1646, 2), (key1263, 2), (key1529, 2), (key1254, 2)]

def rawRow11972 : Integer.Sparse Key := [(key2361, 6), (key2361, 6), (key2364, 6), (key2364, 6), (key2531, -6), (key2531, -6), (key2561, -6), (key2561, -6)]

def rawRow11973 : Integer.Sparse Key := [(key2361, 6), (key2364, 6), (key2361, 6), (key2364, 6), (key2531, -6), (key2561, -6), (key2531, -6), (key2561, -6)]

def rawRow11974 : Integer.Sparse Key := [(key2364, 6), (key2361, 6), (key2361, 6), (key2364, 6), (key2531, -6), (key2561, -6), (key2561, -6), (key2531, -6)]

def rawRow11975 : Integer.Sparse Key := [(key2361, 6), (key2364, 6), (key2364, 6), (key2361, 6), (key2561, -6), (key2531, -6), (key2531, -6), (key2561, -6)]

def rawRow11976 : Integer.Sparse Key := [(key2364, 6), (key2361, 6), (key2364, 6), (key2361, 6), (key2561, -6), (key2531, -6), (key2561, -6), (key2531, -6)]

def rawRow11977 : Integer.Sparse Key := [(key2364, 6), (key2364, 6), (key2361, 6), (key2361, 6), (key2561, -6), (key2561, -6), (key2531, -6), (key2531, -6)]

def rawRow11978 : Integer.Sparse Key := [(key2456, 6), (key2456, 6), (key2459, 6), (key2531, 6), (key2364, -6), (key2459, -6), (key2520, -6), (key2520, -6)]

def rawRow11979 : Integer.Sparse Key := [(key2456, 6), (key2459, 6), (key2456, 6), (key2531, 6), (key2364, -6), (key2520, -6), (key2459, -6), (key2520, -6)]

def rawRow11980 : Integer.Sparse Key := [(key2459, 6), (key2456, 6), (key2456, 6), (key2531, 6), (key2364, -6), (key2520, -6), (key2520, -6), (key2459, -6)]

def rawRow11981 : Integer.Sparse Key := [(key2456, 6), (key2456, 6), (key2531, 6), (key2459, 6), (key2459, -6), (key2364, -6), (key2520, -6), (key2520, -6)]

def rawRow11982 : Integer.Sparse Key := [(key2456, 6), (key2531, 6), (key2456, 6), (key2459, 6), (key2459, -6), (key2520, -6), (key2364, -6), (key2520, -6)]

def rawRow11983 : Integer.Sparse Key := [(key2531, 6), (key2456, 6), (key2456, 6), (key2459, 6), (key2459, -6), (key2520, -6), (key2520, -6), (key2364, -6)]

def rawRow11984 : Integer.Sparse Key := [(key2456, 6), (key2459, 6), (key2531, 6), (key2456, 6), (key2520, -6), (key2364, -6), (key2459, -6), (key2520, -6)]

def rawRow11985 : Integer.Sparse Key := [(key2459, 6), (key2456, 6), (key2531, 6), (key2456, 6), (key2520, -6), (key2364, -6), (key2520, -6), (key2459, -6)]

def rawRow11986 : Integer.Sparse Key := [(key2456, 6), (key2531, 6), (key2459, 6), (key2456, 6), (key2520, -6), (key2459, -6), (key2364, -6), (key2520, -6)]

def rawRow11987 : Integer.Sparse Key := [(key2531, 6), (key2456, 6), (key2459, 6), (key2456, 6), (key2520, -6), (key2459, -6), (key2520, -6), (key2364, -6)]

def rawRow11988 : Integer.Sparse Key := [(key2459, 6), (key2531, 6), (key2456, 6), (key2456, 6), (key2520, -6), (key2520, -6), (key2364, -6), (key2459, -6)]

def rawRow11989 : Integer.Sparse Key := [(key2531, 6), (key2459, 6), (key2456, 6), (key2456, 6), (key2520, -6), (key2520, -6), (key2459, -6), (key2364, -6)]

def rawRow11990 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 6), (key2366, 6), (key2567, -6), (key2567, -6), (key2579, -6), (key2579, -6)]

def rawRow11991 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2361, 6), (key2366, 6), (key2567, -6), (key2579, -6), (key2567, -6), (key2579, -6)]

def rawRow11992 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2567, -6), (key2579, -6), (key2579, -6), (key2567, -6)]

def rawRow11993 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2363, 6), (key2361, 6), (key2579, -6), (key2567, -6), (key2567, -6), (key2579, -6)]

def rawRow11994 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2579, -6), (key2567, -6), (key2579, -6), (key2567, -6)]

def rawRow11995 : Integer.Sparse Key := [(key2363, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2579, -6), (key2579, -6), (key2567, -6), (key2567, -6)]

def rawRow11996 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2366, -6), (key2461, -6), (key2523, -6), (key2523, -6)]

def rawRow11997 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2366, -6), (key2523, -6), (key2461, -6), (key2523, -6)]

def rawRow11998 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2366, -6), (key2523, -6), (key2523, -6), (key2461, -6)]

def rawRow11999 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2461, -6), (key2366, -6), (key2523, -6), (key2523, -6)]

def rawRow12000 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2461, -6), (key2523, -6), (key2366, -6), (key2523, -6)]

def rawRow12001 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2452, 6), (key2458, 6), (key2461, -6), (key2523, -6), (key2523, -6), (key2366, -6)]

def rawRow12002 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2523, -6), (key2366, -6), (key2461, -6), (key2523, -6)]

def rawRow12003 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2523, -6), (key2366, -6), (key2523, -6), (key2461, -6)]

def rawRow12004 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2523, -6), (key2461, -6), (key2366, -6), (key2523, -6)]

def rawRow12005 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2523, -6), (key2461, -6), (key2523, -6), (key2366, -6)]

def rawRow12006 : Integer.Sparse Key := [(key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2523, -6), (key2523, -6), (key2366, -6), (key2461, -6)]

def rawRow12007 : Integer.Sparse Key := [(key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2523, -6), (key2523, -6), (key2461, -6), (key2366, -6)]

def rawRow12008 : Integer.Sparse Key := [(key1999, -6), (key1999, -6), (key2003, -6), (key2003, -6), (key2268, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2323, 2), (key2324, 2), (key2324, 2), (key2272, 2), (key2324, 2), (key2324, 2)]

def rawRow12009 : Integer.Sparse Key := [(key1999, -6), (key2003, -6), (key1999, -6), (key2003, -6), (key2268, 2), (key2272, 2), (key2268, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2324, 2), (key2272, 2), (key2324, 2)]

def rawRow12010 : Integer.Sparse Key := [(key2003, -6), (key1999, -6), (key1999, -6), (key2003, -6), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2268, 2), (key2324, 2), (key2324, 2), (key2272, 2)]

def rawRow12011 : Integer.Sparse Key := [(key1999, -6), (key2003, -6), (key2003, -6), (key1999, -6), (key2323, 2), (key2324, 2), (key2324, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2324, 2), (key2272, 2), (key2324, 2), (key2268, 2), (key2268, 2), (key2323, 2)]

def rawRow12012 : Integer.Sparse Key := [(key2003, -6), (key1999, -6), (key2003, -6), (key1999, -6), (key2324, 2), (key2323, 2), (key2324, 2), (key2272, 2), (key2268, 2), (key2324, 2), (key2268, 2), (key2324, 2), (key2272, 2), (key2268, 2), (key2323, 2), (key2268, 2)]

def rawRow12013 : Integer.Sparse Key := [(key2003, -6), (key2003, -6), (key1999, -6), (key1999, -6), (key2324, 2), (key2324, 2), (key2323, 2), (key2324, 2), (key2324, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2268, 2), (key2268, 2)]

def rawRow12014 : Integer.Sparse Key := [(key2268, -6), (key2268, -6), (key2272, -6), (key2294, -6), (key1999, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2323, 2), (key2324, 2), (key2324, 2), (key2294, 2), (key2336, 2), (key2336, 2)]

def rawRow12015 : Integer.Sparse Key := [(key2268, -6), (key2272, -6), (key2268, -6), (key2294, -6), (key1999, 2), (key2003, 2), (key1999, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key2294, 2), (key2336, 2)]

def rawRow12016 : Integer.Sparse Key := [(key2272, -6), (key2268, -6), (key2268, -6), (key2294, -6), (key2003, 2), (key1999, 2), (key1999, 2), (key2324, 2), (key2323, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2268, 2), (key2336, 2), (key2336, 2), (key2294, 2)]

def rawRow12017 : Integer.Sparse Key := [(key2268, -6), (key2268, -6), (key2294, -6), (key2272, -6), (key2268, 2), (key2268, 2), (key2294, 2), (key1999, 2), (key1999, 2), (key2323, 2), (key2323, 2), (key2336, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key2324, 2)]

def rawRow12018 : Integer.Sparse Key := [(key2268, -6), (key2294, -6), (key2268, -6), (key2272, -6), (key2268, 2), (key2294, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2336, 2), (key1999, 2), (key2323, 2), (key2324, 2), (key2003, 2), (key2324, 2)]

def rawRow12019 : Integer.Sparse Key := [(key2294, -6), (key2268, -6), (key2268, -6), (key2272, -6), (key2294, 2), (key2268, 2), (key2268, 2), (key2336, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2323, 2), (key1999, 2), (key2324, 2), (key2324, 2), (key2003, 2)]

def rawRow12020 : Integer.Sparse Key := [(key2268, -6), (key2272, -6), (key2294, -6), (key2268, -6), (key2323, 2), (key2324, 2), (key2336, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2324, 2), (key2294, 2), (key2336, 2), (key1999, 2), (key2268, 2), (key2323, 2)]

def rawRow12021 : Integer.Sparse Key := [(key2272, -6), (key2268, -6), (key2294, -6), (key2268, -6), (key2324, 2), (key2323, 2), (key2336, 2), (key2003, 2), (key1999, 2), (key2324, 2), (key2268, 2), (key2336, 2), (key2294, 2), (key1999, 2), (key2323, 2), (key2268, 2)]

def rawRow12022 : Integer.Sparse Key := [(key2268, -6), (key2294, -6), (key2272, -6), (key2268, -6), (key2323, 2), (key2336, 2), (key2324, 2), (key2268, 2), (key2294, 2), (key1999, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key2268, 2), (key1999, 2), (key2323, 2)]

def rawRow12023 : Integer.Sparse Key := [(key2294, -6), (key2268, -6), (key2272, -6), (key2268, -6), (key2336, 2), (key2323, 2), (key2324, 2), (key2294, 2), (key2268, 2), (key2336, 2), (key1999, 2), (key2324, 2), (key2003, 2), (key2268, 2), (key2323, 2), (key1999, 2)]

def rawRow12024 : Integer.Sparse Key := [(key2272, -6), (key2294, -6), (key2268, -6), (key2268, -6), (key2324, 2), (key2336, 2), (key2323, 2), (key2324, 2), (key2336, 2), (key2003, 2), (key2294, 2), (key1999, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2268, 2)]

def rawRow12025 : Integer.Sparse Key := [(key2294, -6), (key2272, -6), (key2268, -6), (key2268, -6), (key2336, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2294, 2), (key2003, 2), (key2268, 2), (key1999, 2), (key2323, 2), (key2268, 2), (key1999, 2)]

def rawRow12026 : Integer.Sparse Key := [(key976, 6), (key976, 6), (key984, 6), (key984, 6), (key1169, -6), (key1169, -6), (key1220, -6), (key1220, -6)]

def rawRow12027 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key976, 6), (key984, 6), (key1169, -6), (key1220, -6), (key1169, -6), (key1220, -6)]

def rawRow12028 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key976, 6), (key984, 6), (key1169, -6), (key1220, -6), (key1220, -6), (key1169, -6)]

def rawRow12029 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key984, 6), (key976, 6), (key1220, -6), (key1169, -6), (key1169, -6), (key1220, -6)]

def rawRow12030 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key984, 6), (key976, 6), (key1220, -6), (key1169, -6), (key1220, -6), (key1169, -6)]

def rawRow12031 : Integer.Sparse Key := [(key984, 6), (key984, 6), (key976, 6), (key976, 6), (key1220, -6), (key1220, -6), (key1169, -6), (key1169, -6)]

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

def rawRow12032 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key984, -6), (key1098, -6), (key1183, -6), (key1183, -6)]

def rawRow12033 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key984, -6), (key1183, -6), (key1098, -6), (key1183, -6)]

def rawRow12034 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key984, -6), (key1183, -6), (key1183, -6), (key1098, -6)]

def rawRow12035 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1098, -6), (key984, -6), (key1183, -6), (key1183, -6)]

def rawRow12036 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1098, -6), (key1183, -6), (key984, -6), (key1183, -6)]

def rawRow12037 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1098, -6), (key1183, -6), (key1183, -6), (key984, -6)]

def rawRow12038 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1183, -6), (key984, -6), (key1098, -6), (key1183, -6)]

def rawRow12039 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1183, -6), (key984, -6), (key1183, -6), (key1098, -6)]

def rawRow12040 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1183, -6), (key1098, -6), (key984, -6), (key1183, -6)]

def rawRow12041 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, -6), (key1098, -6), (key1183, -6), (key984, -6)]

def rawRow12042 : Integer.Sparse Key := [(key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1183, -6), (key1183, -6), (key984, -6), (key1098, -6)]

def rawRow12043 : Integer.Sparse Key := [(key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1183, -6), (key1183, -6), (key1098, -6), (key984, -6)]

def rawRow12044 : Integer.Sparse Key := [(key2361, -6), (key2361, -6), (key2364, -6), (key2364, -6), (key2456, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2)]

def rawRow12045 : Integer.Sparse Key := [(key2361, -6), (key2364, -6), (key2361, -6), (key2364, -6), (key2456, 2), (key2459, 2), (key2456, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2520, 2), (key2459, 2), (key2520, 2)]

def rawRow12046 : Integer.Sparse Key := [(key2364, -6), (key2361, -6), (key2361, -6), (key2364, -6), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2520, 2), (key2520, 2), (key2459, 2)]

def rawRow12047 : Integer.Sparse Key := [(key2361, -6), (key2364, -6), (key2364, -6), (key2361, -6), (key2517, 2), (key2520, 2), (key2520, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2456, 2), (key2456, 2), (key2517, 2)]

def rawRow12048 : Integer.Sparse Key := [(key2364, -6), (key2361, -6), (key2364, -6), (key2361, -6), (key2520, 2), (key2517, 2), (key2520, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2456, 2), (key2517, 2), (key2456, 2)]

def rawRow12049 : Integer.Sparse Key := [(key2364, -6), (key2364, -6), (key2361, -6), (key2361, -6), (key2520, 2), (key2520, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2456, 2)]

def rawRow12050 : Integer.Sparse Key := [(key2456, -6), (key2456, -6), (key2459, -6), (key2531, -6), (key2361, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2561, 2)]

def rawRow12051 : Integer.Sparse Key := [(key2456, -6), (key2459, -6), (key2456, -6), (key2531, -6), (key2361, 2), (key2364, 2), (key2361, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2531, 2), (key2561, 2)]

def rawRow12052 : Integer.Sparse Key := [(key2459, -6), (key2456, -6), (key2456, -6), (key2531, -6), (key2364, 2), (key2361, 2), (key2361, 2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2561, 2), (key2561, 2), (key2531, 2)]

def rawRow12053 : Integer.Sparse Key := [(key2456, -6), (key2456, -6), (key2531, -6), (key2459, -6), (key2456, 2), (key2456, 2), (key2531, 2), (key2361, 2), (key2361, 2), (key2517, 2), (key2517, 2), (key2561, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2520, 2)]

def rawRow12054 : Integer.Sparse Key := [(key2456, -6), (key2531, -6), (key2456, -6), (key2459, -6), (key2456, 2), (key2531, 2), (key2456, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2561, 2), (key2361, 2), (key2517, 2), (key2520, 2), (key2364, 2), (key2520, 2)]

def rawRow12055 : Integer.Sparse Key := [(key2531, -6), (key2456, -6), (key2456, -6), (key2459, -6), (key2531, 2), (key2456, 2), (key2456, 2), (key2561, 2), (key2517, 2), (key2561, 2), (key2361, 2), (key2517, 2), (key2361, 2), (key2520, 2), (key2520, 2), (key2364, 2)]

def rawRow12056 : Integer.Sparse Key := [(key2456, -6), (key2459, -6), (key2531, -6), (key2456, -6), (key2517, 2), (key2520, 2), (key2561, 2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2361, 2), (key2456, 2), (key2517, 2)]

def rawRow12057 : Integer.Sparse Key := [(key2459, -6), (key2456, -6), (key2531, -6), (key2456, -6), (key2520, 2), (key2517, 2), (key2561, 2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2361, 2), (key2517, 2), (key2456, 2)]

def rawRow12058 : Integer.Sparse Key := [(key2456, -6), (key2531, -6), (key2459, -6), (key2456, -6), (key2517, 2), (key2561, 2), (key2520, 2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2456, 2), (key2361, 2), (key2517, 2)]

def rawRow12059 : Integer.Sparse Key := [(key2531, -6), (key2456, -6), (key2459, -6), (key2456, -6), (key2561, 2), (key2517, 2), (key2520, 2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2456, 2), (key2517, 2), (key2361, 2)]

def rawRow12060 : Integer.Sparse Key := [(key2459, -6), (key2531, -6), (key2456, -6), (key2456, -6), (key2520, 2), (key2561, 2), (key2517, 2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2517, 2), (key2361, 2), (key2456, 2)]

def rawRow12061 : Integer.Sparse Key := [(key2531, -6), (key2459, -6), (key2456, -6), (key2456, -6), (key2561, 2), (key2520, 2), (key2517, 2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2517, 2), (key2456, 2), (key2361, 2)]

def rawRow12062 : Integer.Sparse Key := [(key2377, -6), (key2377, -6), (key2389, -6), (key2389, -6), (key2405, 6), (key2405, 6), (key2436, 6), (key2436, 6)]

def rawRow12063 : Integer.Sparse Key := [(key2377, -6), (key2389, -6), (key2377, -6), (key2389, -6), (key2405, 6), (key2436, 6), (key2405, 6), (key2436, 6)]

def rawRow12064 : Integer.Sparse Key := [(key2377, -6), (key2389, -6), (key2389, -6), (key2377, -6), (key2405, 6), (key2436, 6), (key2436, 6), (key2405, 6)]

def rawRow12065 : Integer.Sparse Key := [(key2389, -6), (key2377, -6), (key2377, -6), (key2389, -6), (key2436, 6), (key2405, 6), (key2405, 6), (key2436, 6)]

def rawRow12066 : Integer.Sparse Key := [(key2389, -6), (key2377, -6), (key2389, -6), (key2377, -6), (key2436, 6), (key2405, 6), (key2436, 6), (key2405, 6)]

def rawRow12067 : Integer.Sparse Key := [(key2389, -6), (key2389, -6), (key2377, -6), (key2377, -6), (key2436, 6), (key2436, 6), (key2405, 6), (key2405, 6)]

def rawRow12068 : Integer.Sparse Key := [(key2405, -6), (key2471, -6), (key2479, -6), (key2479, -6), (key2377, 6), (key2471, 6), (key2502, 6), (key2502, 6)]

def rawRow12069 : Integer.Sparse Key := [(key2405, -6), (key2479, -6), (key2471, -6), (key2479, -6), (key2377, 6), (key2502, 6), (key2471, 6), (key2502, 6)]

def rawRow12070 : Integer.Sparse Key := [(key2405, -6), (key2479, -6), (key2479, -6), (key2471, -6), (key2377, 6), (key2502, 6), (key2502, 6), (key2471, 6)]

def rawRow12071 : Integer.Sparse Key := [(key2471, -6), (key2405, -6), (key2479, -6), (key2479, -6), (key2471, 6), (key2377, 6), (key2502, 6), (key2502, 6)]

def rawRow12072 : Integer.Sparse Key := [(key2471, -6), (key2479, -6), (key2405, -6), (key2479, -6), (key2471, 6), (key2502, 6), (key2377, 6), (key2502, 6)]

def rawRow12073 : Integer.Sparse Key := [(key2471, -6), (key2479, -6), (key2479, -6), (key2405, -6), (key2471, 6), (key2502, 6), (key2502, 6), (key2377, 6)]

def rawRow12074 : Integer.Sparse Key := [(key2479, -6), (key2405, -6), (key2471, -6), (key2479, -6), (key2502, 6), (key2377, 6), (key2471, 6), (key2502, 6)]

def rawRow12075 : Integer.Sparse Key := [(key2479, -6), (key2405, -6), (key2479, -6), (key2471, -6), (key2502, 6), (key2377, 6), (key2502, 6), (key2471, 6)]

def rawRow12076 : Integer.Sparse Key := [(key2479, -6), (key2471, -6), (key2405, -6), (key2479, -6), (key2502, 6), (key2471, 6), (key2377, 6), (key2502, 6)]

def rawRow12077 : Integer.Sparse Key := [(key2479, -6), (key2471, -6), (key2479, -6), (key2405, -6), (key2502, 6), (key2471, 6), (key2502, 6), (key2377, 6)]

def rawRow12078 : Integer.Sparse Key := [(key2479, -6), (key2479, -6), (key2405, -6), (key2471, -6), (key2502, 6), (key2502, 6), (key2377, 6), (key2471, 6)]

def rawRow12079 : Integer.Sparse Key := [(key2479, -6), (key2479, -6), (key2471, -6), (key2405, -6), (key2502, 6), (key2502, 6), (key2471, 6), (key2377, 6)]

def rawRow12080 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2410, -2), (key2410, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2445, -2), (key2473, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2483, 2), (key2483, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2526, 2)]

def rawRow12081 : Integer.Sparse Key := [(key2410, -2), (key2407, -2), (key2410, -2), (key2441, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2445, -2), (key2410, -2), (key2441, -2), (key2483, 2), (key2473, 2), (key2483, 2), (key2507, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2526, 2), (key2483, 2), (key2507, 2)]

def rawRow12082 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2407, -2), (key2445, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2441, -2), (key2410, -2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2473, 2), (key2526, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2507, 2), (key2483, 2)]

def rawRow12083 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2445, -2), (key2407, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2410, -2), (key2441, -2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2526, 2), (key2473, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2483, 2), (key2507, 2)]

def rawRow12084 : Integer.Sparse Key := [(key2441, -2), (key2445, -2), (key2441, -2), (key2410, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2407, -2), (key2441, -2), (key2410, -2), (key2507, 2), (key2526, 2), (key2507, 2), (key2483, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2473, 2), (key2507, 2), (key2483, 2)]

def rawRow12085 : Integer.Sparse Key := [(key2445, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2441, -2), (key2441, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2407, -2), (key2526, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2507, 2), (key2507, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2473, 2)]

def rawRow12086 : Integer.Sparse Key := [(key2592, -2), (key2595, -2), (key2595, -2), (key2848, -2), (key2970, -2), (key2970, -2), (key2882, -2), (key2882, -2), (key2991, -2), (key2991, -2), (key2993, -2), (key2993, -2), (key2379, 2), (key2393, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2441, 2), (key2544, 2), (key2544, 2), (key2555, 2), (key2555, 2), (key2565, 2), (key2565, 2)]

def rawRow12087 : Integer.Sparse Key := [(key2595, -2), (key2592, -2), (key2595, -2), (key2970, -2), (key2848, -2), (key2970, -2), (key2991, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2882, -2), (key2991, -2), (key2393, 2), (key2379, 2), (key2393, 2), (key2441, 2), (key2407, 2), (key2441, 2), (key2555, 2), (key2565, 2), (key2544, 2), (key2565, 2), (key2544, 2), (key2555, 2)]

def rawRow12088 : Integer.Sparse Key := [(key2595, -2), (key2595, -2), (key2592, -2), (key2970, -2), (key2970, -2), (key2848, -2), (key2993, -2), (key2991, -2), (key2993, -2), (key2882, -2), (key2991, -2), (key2882, -2), (key2393, 2), (key2393, 2), (key2379, 2), (key2441, 2), (key2441, 2), (key2407, 2), (key2565, 2), (key2555, 2), (key2565, 2), (key2544, 2), (key2555, 2), (key2544, 2)]

def rawRow12089 : Integer.Sparse Key := [(key2848, -2), (key2882, -2), (key2882, -2), (key2592, -2), (key2991, -2), (key2991, -2), (key2595, -2), (key2595, -2), (key2970, -2), (key2970, -2), (key2993, -2), (key2993, -2), (key2771, 2), (key2912, 2), (key2912, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2393, 2), (key2393, 2), (key2441, 2), (key2441, 2), (key2565, 2), (key2565, 2)]

def rawRow12090 : Integer.Sparse Key := [(key2882, -2), (key2848, -2), (key2882, -2), (key2991, -2), (key2592, -2), (key2991, -2), (key2970, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2970, -2), (key2912, 2), (key2771, 2), (key2912, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2565, 2), (key2393, 2), (key2441, 2)]

def rawRow12091 : Integer.Sparse Key := [(key2882, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2991, -2), (key2592, -2), (key2993, -2), (key2970, -2), (key2993, -2), (key2595, -2), (key2970, -2), (key2595, -2), (key2912, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key2565, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2393, 2)]

def rawRow12092 : Integer.Sparse Key := [(key2970, -2), (key2991, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2993, -2), (key2592, -2), (key2595, -2), (key2848, -2), (key2970, -2), (key2882, -2), (key2991, -2), (key2933, 2), (key2991, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key3003, 2), (key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2)]

def rawRow12093 : Integer.Sparse Key := [(key2970, -2), (key2993, -2), (key2991, -2), (key2595, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2592, -2), (key2970, -2), (key2848, -2), (key2991, -2), (key2882, -2), (key2933, 2), (key3003, 2), (key2991, 2), (key2602, 2), (key3003, 2), (key2912, 2), (key2393, 2), (key2379, 2), (key2441, 2), (key2407, 2), (key2555, 2), (key2544, 2)]

def rawRow12094 : Integer.Sparse Key := [(key2991, -2), (key2970, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2993, -2), (key2848, -2), (key2882, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2991, 2), (key2933, 2), (key3003, 2), (key2912, 2), (key2602, 2), (key3003, 2), (key2771, 2), (key2912, 2), (key2592, 2), (key2991, 2), (key2393, 2), (key2441, 2)]

def rawRow12095 : Integer.Sparse Key := [(key2991, -2), (key2993, -2), (key2970, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2970, -2), (key2595, -2), (key2991, 2), (key3003, 2), (key2933, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2592, 2), (key2441, 2), (key2393, 2)]

def rawRow12096 : Integer.Sparse Key := [(key2993, -2), (key2970, -2), (key2991, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2592, -2), (key2848, -2), (key3003, 2), (key2933, 2), (key2991, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2933, 2), (key2991, 2), (key2602, 2), (key2912, 2), (key2379, 2), (key2407, 2)]

def rawRow12097 : Integer.Sparse Key := [(key2993, -2), (key2991, -2), (key2970, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2991, -2), (key2970, -2), (key2882, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key3003, 2), (key2991, 2), (key2933, 2), (key3003, 2), (key2912, 2), (key2602, 2), (key2991, 2), (key2933, 2), (key2912, 2), (key2602, 2), (key2771, 2), (key2592, 2)]

def rawRow12098 : Integer.Sparse Key := [(key1096, 2), (key1100, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1100, 2), (key1100, 2), (key1185, 2), (key1185, 2), (key1186, 2), (key1186, 2), (key1171, -2), (key1171, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1222, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1224, -2)]

def rawRow12099 : Integer.Sparse Key := [(key1100, 2), (key1096, 2), (key1100, 2), (key1185, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key1171, -2), (key1175, -2), (key1171, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1224, -2), (key1175, -2), (key1224, -2)]

def rawRow12100 : Integer.Sparse Key := [(key1100, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1096, 2), (key1186, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1185, 2), (key1100, 2), (key1175, -2), (key1171, -2), (key1171, -2), (key1224, -2), (key1222, -2), (key1224, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1224, -2), (key1224, -2), (key1175, -2)]

def rawRow12101 : Integer.Sparse Key := [(key1185, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1100, 2), (key1186, 2), (key1096, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1100, 2), (key1185, 2), (key1222, -2), (key1224, -2), (key1224, -2), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1171, -2), (key1171, -2), (key1222, -2)]

def rawRow12102 : Integer.Sparse Key := [(key1185, 2), (key1186, 2), (key1185, 2), (key1100, 2), (key1186, 2), (key1100, 2), (key1100, 2), (key1096, 2), (key1185, 2), (key1096, 2), (key1185, 2), (key1100, 2), (key1224, -2), (key1222, -2), (key1224, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1171, -2), (key1222, -2), (key1171, -2)]

def rawRow12103 : Integer.Sparse Key := [(key1186, 2), (key1185, 2), (key1185, 2), (key1186, 2), (key1100, 2), (key1100, 2), (key1185, 2), (key1185, 2), (key1100, 2), (key1100, 2), (key1096, 2), (key1096, 2), (key1224, -2), (key1224, -2), (key1222, -2), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1222, -2), (key1171, -2), (key1171, -2)]

def rawRow12104 : Integer.Sparse Key := [(key982, 2), (key986, 2), (key986, 2), (key1096, 2), (key1185, 2), (key1185, 2), (key1171, 2), (key1171, 2), (key1222, 2), (key1222, 2), (key1224, 2), (key1224, 2), (key986, -2), (key986, -2), (key988, -2), (key1100, -2), (key1100, -2), (key1185, -2), (key1185, -2), (key1186, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key1224, -2)]

def rawRow12105 : Integer.Sparse Key := [(key986, 2), (key982, 2), (key986, 2), (key1185, 2), (key1096, 2), (key1185, 2), (key1222, 2), (key1224, 2), (key1171, 2), (key1224, 2), (key1171, 2), (key1222, 2), (key986, -2), (key988, -2), (key986, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1224, -2), (key1175, -2), (key1224, -2)]

def rawRow12106 : Integer.Sparse Key := [(key986, 2), (key986, 2), (key982, 2), (key1185, 2), (key1185, 2), (key1096, 2), (key1224, 2), (key1222, 2), (key1224, 2), (key1171, 2), (key1222, 2), (key1171, 2), (key988, -2), (key986, -2), (key986, -2), (key1186, -2), (key1185, -2), (key1186, -2), (key1100, -2), (key1185, -2), (key1100, -2), (key1224, -2), (key1224, -2), (key1175, -2)]

def rawRow12107 : Integer.Sparse Key := [(key1096, 2), (key1171, 2), (key1171, 2), (key982, 2), (key1222, 2), (key1222, 2), (key986, 2), (key986, 2), (key1185, 2), (key1185, 2), (key1224, 2), (key1224, 2), (key1100, -2), (key1100, -2), (key1175, -2), (key986, -2), (key986, -2), (key1185, -2), (key1185, -2), (key1224, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1186, -2)]

def rawRow12108 : Integer.Sparse Key := [(key1171, 2), (key1096, 2), (key1171, 2), (key1222, 2), (key982, 2), (key1222, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1224, 2), (key986, 2), (key1185, 2), (key1100, -2), (key1175, -2), (key1100, -2), (key1185, -2), (key1224, -2), (key986, -2), (key1224, -2), (key986, -2), (key1185, -2), (key1186, -2), (key988, -2), (key1186, -2)]

def rawRow12109 : Integer.Sparse Key := [(key1171, 2), (key1171, 2), (key1096, 2), (key1222, 2), (key1222, 2), (key982, 2), (key1224, 2), (key1185, 2), (key1224, 2), (key986, 2), (key1185, 2), (key986, 2), (key1175, -2), (key1100, -2), (key1100, -2), (key1224, -2), (key1185, -2), (key1224, -2), (key986, -2), (key1185, -2), (key986, -2), (key1186, -2), (key1186, -2), (key988, -2)]

def rawRow12110 : Integer.Sparse Key := [(key1185, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1224, 2), (key982, 2), (key986, 2), (key1096, 2), (key1185, 2), (key1171, 2), (key1222, 2), (key1185, -2), (key1186, -2), (key1224, -2), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key986, -2), (key1100, -2), (key1185, -2)]

def rawRow12111 : Integer.Sparse Key := [(key1185, 2), (key1224, 2), (key1222, 2), (key986, 2), (key1224, 2), (key1171, 2), (key986, 2), (key982, 2), (key1185, 2), (key1096, 2), (key1222, 2), (key1171, 2), (key1186, -2), (key1185, -2), (key1224, -2), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, -2), (key1185, -2), (key1100, -2)]

def rawRow12112 : Integer.Sparse Key := [(key1222, 2), (key1185, 2), (key1224, 2), (key1171, 2), (key986, 2), (key1224, 2), (key1096, 2), (key1171, 2), (key982, 2), (key1222, 2), (key986, 2), (key1185, 2), (key1185, -2), (key1224, -2), (key1186, -2), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1100, -2), (key986, -2), (key1185, -2)]

def rawRow12113 : Integer.Sparse Key := [(key1222, 2), (key1224, 2), (key1185, 2), (key1171, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1096, 2), (key1222, 2), (key982, 2), (key1185, 2), (key986, 2), (key1224, -2), (key1185, -2), (key1186, -2), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1100, -2), (key1185, -2), (key986, -2)]

def rawRow12114 : Integer.Sparse Key := [(key1224, 2), (key1185, 2), (key1222, 2), (key1224, 2), (key986, 2), (key1171, 2), (key1185, 2), (key1222, 2), (key986, 2), (key1171, 2), (key982, 2), (key1096, 2), (key1186, -2), (key1224, -2), (key1185, -2), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, -2), (key986, -2), (key1100, -2)]

def rawRow12115 : Integer.Sparse Key := [(key1224, 2), (key1222, 2), (key1185, 2), (key1224, 2), (key1171, 2), (key986, 2), (key1222, 2), (key1185, 2), (key1171, 2), (key986, 2), (key1096, 2), (key982, 2), (key1224, -2), (key1186, -2), (key1185, -2), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1185, -2), (key1100, -2), (key986, -2)]

def rawRow12116 : Integer.Sparse Key := [(key2420, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2438, -4), (key2495, 6), (key2495, 6), (key2504, 6), (key2504, 6)]

def rawRow12117 : Integer.Sparse Key := [(key2427, -4), (key2420, -4), (key2427, -4), (key2427, -4), (key2438, -4), (key2427, -4), (key2495, 6), (key2504, 6), (key2495, 6), (key2504, 6)]

def rawRow12118 : Integer.Sparse Key := [(key2427, -4), (key2427, -4), (key2420, -4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, 6), (key2495, 6), (key2495, 6), (key2504, 6)]

def rawRow12119 : Integer.Sparse Key := [(key2427, -4), (key2427, -4), (key2438, -4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, 6), (key2504, 6), (key2504, 6), (key2495, 6)]

def rawRow12120 : Integer.Sparse Key := [(key2427, -4), (key2438, -4), (key2427, -4), (key2427, -4), (key2420, -4), (key2427, -4), (key2504, 6), (key2495, 6), (key2504, 6), (key2495, 6)]

def rawRow12121 : Integer.Sparse Key := [(key2438, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2427, -4), (key2420, -4), (key2504, 6), (key2504, 6), (key2495, 6), (key2495, 6)]

def rawRow12122 : Integer.Sparse Key := [(key2420, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2495, -4), (key2504, -4), (key2427, 6), (key2427, 6), (key2438, 6), (key2504, 6)]

def rawRow12123 : Integer.Sparse Key := [(key2427, -4), (key2420, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2495, -4), (key2427, 6), (key2438, 6), (key2427, 6), (key2504, 6)]

def rawRow12124 : Integer.Sparse Key := [(key2427, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2495, -4), (key2495, -4), (key2438, 6), (key2427, 6), (key2427, 6), (key2504, 6)]

def rawRow12125 : Integer.Sparse Key := [(key2420, -4), (key2495, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2427, 6), (key2427, 6), (key2504, 6), (key2438, 6)]

def rawRow12126 : Integer.Sparse Key := [(key2495, -4), (key2420, -4), (key2495, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2427, 6), (key2504, 6), (key2427, 6), (key2438, 6)]

def rawRow12127 : Integer.Sparse Key := [(key2495, -4), (key2495, -4), (key2420, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2504, 6), (key2427, 6), (key2427, 6), (key2438, 6)]

def rawRow12128 : Integer.Sparse Key := [(key2427, -4), (key2495, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, 6), (key2438, 6), (key2504, 6), (key2427, 6)]

def rawRow12129 : Integer.Sparse Key := [(key2427, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2420, -4), (key2495, -4), (key2438, 6), (key2427, 6), (key2504, 6), (key2427, 6)]

def rawRow12130 : Integer.Sparse Key := [(key2495, -4), (key2427, -4), (key2504, -4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, 6), (key2504, 6), (key2438, 6), (key2427, 6)]

def rawRow12131 : Integer.Sparse Key := [(key2495, -4), (key2504, -4), (key2427, -4), (key2495, -4), (key2420, -4), (key2427, -4), (key2504, 6), (key2427, 6), (key2438, 6), (key2427, 6)]

def rawRow12132 : Integer.Sparse Key := [(key2504, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2495, -4), (key2420, -4), (key2438, 6), (key2504, 6), (key2427, 6), (key2427, 6)]

def rawRow12133 : Integer.Sparse Key := [(key2504, -4), (key2495, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, -4), (key2504, 6), (key2438, 6), (key2427, 6), (key2427, 6)]

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

def rawRow12152 : Integer.Sparse Key := [(key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1), (key2538, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2543, -2), (key2543, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2563, -2)]

def rawRow12153 : Integer.Sparse Key := [(key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2543, -2), (key2538, -2), (key2543, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2563, -2), (key2543, -2), (key2554, -2)]

def rawRow12154 : Integer.Sparse Key := [(key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2482, 1), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2538, -2), (key2563, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2554, -2), (key2543, -2)]

def rawRow12155 : Integer.Sparse Key := [(key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2563, -2), (key2538, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2543, -2), (key2554, -2)]

def rawRow12156 : Integer.Sparse Key := [(key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2554, -2), (key2563, -2), (key2554, -2), (key2543, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2543, -2)]

def rawRow12157 : Integer.Sparse Key := [(key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1), (key2506, 1), (key2506, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1), (key2563, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2554, -2), (key2554, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2538, -2)]

def rawRow12158 : Integer.Sparse Key := [(key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2543, 1), (key2543, 1), (key2554, 1), (key2554, 1), (key2563, 1), (key2563, 1), (key2381, -2), (key2392, -2), (key2392, -2), (key2409, -2), (key2440, -2), (key2440, -2), (key2482, -2), (key2482, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2)]

def rawRow12159 : Integer.Sparse Key := [(key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2392, -2), (key2381, -2), (key2392, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2506, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2482, -2), (key2506, -2)]

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

def rawRow12160 : Integer.Sparse Key := [(key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2563, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2543, 1), (key2392, -2), (key2392, -2), (key2381, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2522, -2), (key2506, -2), (key2522, -2), (key2482, -2), (key2506, -2), (key2482, -2)]

def rawRow12161 : Integer.Sparse Key := [(key2406, 1), (key2406, 1), (key2480, 1), (key2480, 1), (key2543, 1), (key2543, 1), (key2378, 1), (key2378, 1), (key2503, 1), (key2503, 1), (key2554, 1), (key2554, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2563, 1), (key2563, 1), (key2392, 1), (key2392, 1), (key2440, 1), (key2440, 1), (key2522, 1), (key2522, 1), (key2409, -2), (key2482, -2), (key2482, -2), (key2381, -2), (key2506, -2), (key2506, -2), (key2392, -2), (key2392, -2), (key2440, -2), (key2440, -2), (key2522, -2), (key2522, -2)]

def rawRow12162 : Integer.Sparse Key := [(key2480, 1), (key2543, 1), (key2406, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2482, -2), (key2409, -2), (key2482, -2), (key2506, -2), (key2381, -2), (key2506, -2), (key2440, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2440, -2)]

def rawRow12163 : Integer.Sparse Key := [(key2543, 1), (key2480, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2563, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2390, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2392, 1), (key2482, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2506, -2), (key2381, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2392, -2), (key2440, -2), (key2392, -2)]

def rawRow12164 : Integer.Sparse Key := [(key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1), (key2378, 1), (key2392, 1), (key2406, 1), (key2440, 1), (key2543, 1), (key2554, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2440, -2), (key2506, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2522, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2440, -2), (key2482, -2), (key2506, -2)]

def rawRow12165 : Integer.Sparse Key := [(key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1), (key2392, 1), (key2378, 1), (key2440, 1), (key2406, 1), (key2554, 1), (key2543, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1), (key2440, -2), (key2522, -2), (key2506, -2), (key2392, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2381, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2482, -2)]

def rawRow12166 : Integer.Sparse Key := [(key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2406, 1), (key2543, 1), (key2378, 1), (key2554, 1), (key2392, 1), (key2440, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2506, -2), (key2440, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2522, -2), (key2409, -2), (key2482, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2440, -2)]

def rawRow12167 : Integer.Sparse Key := [(key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1), (key2543, 1), (key2406, 1), (key2554, 1), (key2378, 1), (key2440, 1), (key2392, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1), (key2506, -2), (key2522, -2), (key2440, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2440, -2), (key2392, -2)]

def rawRow12168 : Integer.Sparse Key := [(key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1), (key2440, 1), (key2554, 1), (key2392, 1), (key2543, 1), (key2378, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1), (key2522, -2), (key2440, -2), (key2506, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2381, -2), (key2409, -2)]

def rawRow12169 : Integer.Sparse Key := [(key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1), (key2554, 1), (key2440, 1), (key2543, 1), (key2392, 1), (key2406, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1), (key2522, -2), (key2506, -2), (key2440, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2506, -2), (key2440, -2), (key2482, -2), (key2392, -2), (key2409, -2), (key2381, -2)]

def rawRow12170 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2437, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2440, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1)]

def rawRow12171 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2437, -2), (key2440, -2), (key2406, -2), (key2440, -2), (key2406, -2), (key2437, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2482, 1), (key2506, 1)]

def rawRow12172 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2440, -2), (key2437, -2), (key2440, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2482, 1)]

def rawRow12173 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2440, -2), (key2406, -2), (key2409, -2), (key2406, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1)]

def rawRow12174 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2440, -2), (key2409, -2), (key2406, -2), (key2440, -2), (key2406, -2), (key2440, -2), (key2409, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1)]

def rawRow12175 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2437, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2409, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2406, -2), (key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1), (key2506, 1), (key2506, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1)]

def rawRow12176 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2506, -2), (key2506, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2543, 1), (key2543, 1), (key2554, 1), (key2554, 1), (key2563, 1), (key2563, 1)]

def rawRow12177 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2503, -2), (key2506, -2), (key2472, -2), (key2506, -2), (key2472, -2), (key2503, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2563, 1), (key2543, 1), (key2554, 1)]

def rawRow12178 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2506, -2), (key2503, -2), (key2506, -2), (key2472, -2), (key2503, -2), (key2472, -2), (key2554, -2), (key2554, -2), (key2538, -2), (key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2563, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2543, 1)]

def rawRow12179 : Integer.Sparse Key := [(key2472, -2), (key2472, -2), (key2538, -2), (key2378, -2), (key2378, -2), (key2503, -2), (key2503, -2), (key2554, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2506, -2), (key2406, 1), (key2406, 1), (key2480, 1), (key2480, 1), (key2543, 1), (key2543, 1), (key2378, 1), (key2378, 1), (key2503, 1), (key2503, 1), (key2554, 1), (key2554, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2563, 1), (key2563, 1), (key2392, 1), (key2392, 1), (key2440, 1), (key2440, 1), (key2522, 1), (key2522, 1)]

def rawRow12180 : Integer.Sparse Key := [(key2472, -2), (key2538, -2), (key2472, -2), (key2503, -2), (key2554, -2), (key2378, -2), (key2554, -2), (key2378, -2), (key2503, -2), (key2506, -2), (key2381, -2), (key2506, -2), (key2480, 1), (key2543, 1), (key2406, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2440, 1)]

def rawRow12181 : Integer.Sparse Key := [(key2538, -2), (key2472, -2), (key2472, -2), (key2554, -2), (key2503, -2), (key2554, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2506, -2), (key2506, -2), (key2381, -2), (key2543, 1), (key2480, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2563, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2390, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2392, 1)]

def rawRow12182 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2554, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2506, -2), (key2538, -2), (key2554, -2), (key2378, -2), (key2472, -2), (key2503, -2), (key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1), (key2378, 1), (key2392, 1), (key2406, 1), (key2440, 1), (key2543, 1), (key2554, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1)]

def rawRow12183 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2554, -2), (key2381, -2), (key2378, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2538, -2), (key2378, -2), (key2503, -2), (key2472, -2), (key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1), (key2392, 1), (key2378, 1), (key2440, 1), (key2406, 1), (key2554, 1), (key2543, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1)]

def rawRow12184 : Integer.Sparse Key := [(key2503, -2), (key2554, -2), (key2506, -2), (key2472, -2), (key2538, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2472, -2), (key2378, -2), (key2503, -2), (key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2406, 1), (key2543, 1), (key2378, 1), (key2554, 1), (key2392, 1), (key2440, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1)]

def rawRow12185 : Integer.Sparse Key := [(key2554, -2), (key2503, -2), (key2506, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1), (key2543, 1), (key2406, 1), (key2554, 1), (key2378, 1), (key2440, 1), (key2392, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1)]

def rawRow12186 : Integer.Sparse Key := [(key2506, -2), (key2554, -2), (key2503, -2), (key2506, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2378, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1), (key2440, 1), (key2554, 1), (key2392, 1), (key2543, 1), (key2378, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1)]

def rawRow12187 : Integer.Sparse Key := [(key2554, -2), (key2506, -2), (key2503, -2), (key2554, -2), (key2506, -2), (key2538, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2503, -2), (key2472, -2), (key2378, -2), (key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1), (key2554, 1), (key2440, 1), (key2543, 1), (key2392, 1), (key2406, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

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

def rawRow12861 : Integer.Sparse Key := [(key868, -6), (key882, -6), (key866, -6), (key866, -6), (key901, 2), (key913, 2), (key900, 2), (key901, 2), (key913, 2), (key734, 2), (key882, 2), (key732, 2), (key866, 2), (key900, 2), (key732, 2), (key866, 2)]

def rawRow12862 : Integer.Sparse Key := [(key882, -6), (key868, -6), (key866, -6), (key866, -6), (key913, 2), (key901, 2), (key900, 2), (key913, 2), (key901, 2), (key882, 2), (key734, 2), (key866, 2), (key732, 2), (key900, 2), (key866, 2), (key732, 2)]

def rawRow12863 : Integer.Sparse Key := [(key900, -6), (key901, -6), (key901, -6), (key913, -6), (key732, 2), (key734, 2), (key734, 2), (key866, 2), (key868, 2), (key866, 2), (key901, 2), (key868, 2), (key901, 2), (key882, 2), (key882, 2), (key913, 2)]

def rawRow12864 : Integer.Sparse Key := [(key901, -6), (key900, -6), (key901, -6), (key913, -6), (key734, 2), (key732, 2), (key734, 2), (key868, 2), (key866, 2), (key901, 2), (key866, 2), (key901, 2), (key868, 2), (key882, 2), (key913, 2), (key882, 2)]

def rawRow12865 : Integer.Sparse Key := [(key901, -6), (key901, -6), (key900, -6), (key913, -6), (key734, 2), (key734, 2), (key732, 2), (key901, 2), (key901, 2), (key868, 2), (key868, 2), (key866, 2), (key866, 2), (key913, 2), (key882, 2), (key882, 2)]

def rawRow12866 : Integer.Sparse Key := [(key900, -6), (key901, -6), (key913, -6), (key901, -6), (key866, 2), (key868, 2), (key882, 2), (key732, 2), (key734, 2), (key866, 2), (key901, 2), (key882, 2), (key913, 2), (key734, 2), (key868, 2), (key901, 2)]

def rawRow12867 : Integer.Sparse Key := [(key901, -6), (key900, -6), (key913, -6), (key901, -6), (key868, 2), (key866, 2), (key882, 2), (key734, 2), (key732, 2), (key901, 2), (key866, 2), (key913, 2), (key882, 2), (key734, 2), (key901, 2), (key868, 2)]

def rawRow12868 : Integer.Sparse Key := [(key900, -6), (key913, -6), (key901, -6), (key901, -6), (key866, 2), (key882, 2), (key868, 2), (key866, 2), (key882, 2), (key732, 2), (key913, 2), (key734, 2), (key901, 2), (key868, 2), (key734, 2), (key901, 2)]

def rawRow12869 : Integer.Sparse Key := [(key913, -6), (key900, -6), (key901, -6), (key901, -6), (key882, 2), (key866, 2), (key868, 2), (key882, 2), (key866, 2), (key913, 2), (key732, 2), (key901, 2), (key734, 2), (key868, 2), (key901, 2), (key734, 2)]

def rawRow12870 : Integer.Sparse Key := [(key901, -6), (key913, -6), (key900, -6), (key901, -6), (key868, 2), (key882, 2), (key866, 2), (key901, 2), (key913, 2), (key734, 2), (key882, 2), (key732, 2), (key866, 2), (key901, 2), (key734, 2), (key868, 2)]

def rawRow12871 : Integer.Sparse Key := [(key913, -6), (key901, -6), (key900, -6), (key901, -6), (key882, 2), (key868, 2), (key866, 2), (key913, 2), (key901, 2), (key882, 2), (key734, 2), (key866, 2), (key732, 2), (key901, 2), (key868, 2), (key734, 2)]

def rawRow12872 : Integer.Sparse Key := [(key901, -6), (key901, -6), (key913, -6), (key900, -6), (key901, 2), (key901, 2), (key913, 2), (key734, 2), (key734, 2), (key868, 2), (key868, 2), (key882, 2), (key882, 2), (key732, 2), (key866, 2), (key866, 2)]

def rawRow12873 : Integer.Sparse Key := [(key901, -6), (key913, -6), (key901, -6), (key900, -6), (key901, 2), (key913, 2), (key901, 2), (key868, 2), (key882, 2), (key734, 2), (key882, 2), (key734, 2), (key868, 2), (key866, 2), (key732, 2), (key866, 2)]

def rawRow12874 : Integer.Sparse Key := [(key913, -6), (key901, -6), (key901, -6), (key900, -6), (key913, 2), (key901, 2), (key901, 2), (key882, 2), (key868, 2), (key882, 2), (key734, 2), (key868, 2), (key734, 2), (key866, 2), (key866, 2), (key732, 2)]

def rawRow12875 : Integer.Sparse Key := [(key498, 6), (key498, 6), (key504, 6), (key666, 6), (key232, -6), (key504, -6), (key562, -6), (key562, -6)]

def rawRow12876 : Integer.Sparse Key := [(key498, 6), (key504, 6), (key498, 6), (key666, 6), (key232, -6), (key562, -6), (key504, -6), (key562, -6)]

def rawRow12877 : Integer.Sparse Key := [(key504, 6), (key498, 6), (key498, 6), (key666, 6), (key232, -6), (key562, -6), (key562, -6), (key504, -6)]

def rawRow12878 : Integer.Sparse Key := [(key498, 6), (key498, 6), (key666, 6), (key504, 6), (key504, -6), (key232, -6), (key562, -6), (key562, -6)]

def rawRow12879 : Integer.Sparse Key := [(key498, 6), (key666, 6), (key498, 6), (key504, 6), (key504, -6), (key562, -6), (key232, -6), (key562, -6)]

def rawRow12880 : Integer.Sparse Key := [(key666, 6), (key498, 6), (key498, 6), (key504, 6), (key504, -6), (key562, -6), (key562, -6), (key232, -6)]

def rawRow12881 : Integer.Sparse Key := [(key498, 6), (key504, 6), (key666, 6), (key498, 6), (key562, -6), (key232, -6), (key504, -6), (key562, -6)]

def rawRow12882 : Integer.Sparse Key := [(key504, 6), (key498, 6), (key666, 6), (key498, 6), (key562, -6), (key232, -6), (key562, -6), (key504, -6)]

def rawRow12883 : Integer.Sparse Key := [(key498, 6), (key666, 6), (key504, 6), (key498, 6), (key562, -6), (key504, -6), (key232, -6), (key562, -6)]

def rawRow12884 : Integer.Sparse Key := [(key666, 6), (key498, 6), (key504, 6), (key498, 6), (key562, -6), (key504, -6), (key562, -6), (key232, -6)]

def rawRow12885 : Integer.Sparse Key := [(key504, 6), (key666, 6), (key498, 6), (key498, 6), (key562, -6), (key562, -6), (key232, -6), (key504, -6)]

def rawRow12886 : Integer.Sparse Key := [(key666, 6), (key504, 6), (key498, 6), (key498, 6), (key562, -6), (key562, -6), (key504, -6), (key232, -6)]

def rawRow12887 : Integer.Sparse Key := [(key552, 6), (key562, 6), (key562, 6), (key683, 6), (key226, -6), (key498, -6), (key498, -6), (key552, -6)]

def rawRow12888 : Integer.Sparse Key := [(key562, 6), (key552, 6), (key562, 6), (key683, 6), (key226, -6), (key498, -6), (key552, -6), (key498, -6)]

def rawRow12889 : Integer.Sparse Key := [(key562, 6), (key562, 6), (key552, 6), (key683, 6), (key226, -6), (key552, -6), (key498, -6), (key498, -6)]

def rawRow12890 : Integer.Sparse Key := [(key552, 6), (key562, 6), (key683, 6), (key562, 6), (key498, -6), (key226, -6), (key498, -6), (key552, -6)]

def rawRow12891 : Integer.Sparse Key := [(key562, 6), (key552, 6), (key683, 6), (key562, 6), (key498, -6), (key226, -6), (key552, -6), (key498, -6)]

def rawRow12892 : Integer.Sparse Key := [(key552, 6), (key683, 6), (key562, 6), (key562, 6), (key498, -6), (key498, -6), (key226, -6), (key552, -6)]

def rawRow12893 : Integer.Sparse Key := [(key683, 6), (key552, 6), (key562, 6), (key562, 6), (key498, -6), (key498, -6), (key552, -6), (key226, -6)]

def rawRow12894 : Integer.Sparse Key := [(key562, 6), (key683, 6), (key552, 6), (key562, 6), (key498, -6), (key552, -6), (key226, -6), (key498, -6)]

def rawRow12895 : Integer.Sparse Key := [(key683, 6), (key562, 6), (key552, 6), (key562, 6), (key498, -6), (key552, -6), (key498, -6), (key226, -6)]

def rawRow12896 : Integer.Sparse Key := [(key562, 6), (key562, 6), (key683, 6), (key552, 6), (key552, -6), (key226, -6), (key498, -6), (key498, -6)]

def rawRow12897 : Integer.Sparse Key := [(key562, 6), (key683, 6), (key562, 6), (key552, 6), (key552, -6), (key498, -6), (key226, -6), (key498, -6)]

def rawRow12898 : Integer.Sparse Key := [(key683, 6), (key562, 6), (key562, 6), (key552, 6), (key552, -6), (key498, -6), (key498, -6), (key226, -6)]

def rawRow12899 : Integer.Sparse Key := [(key1704, -6), (key1704, -6), (key1708, -6), (key1857, -6), (key1281, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1704, 2), (key1753, 2), (key1753, 2), (key1758, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1888, 2)]

def rawRow12900 : Integer.Sparse Key := [(key1704, -6), (key1708, -6), (key1704, -6), (key1857, -6), (key1281, 2), (key1285, 2), (key1281, 2), (key1753, 2), (key1758, 2), (key1704, 2), (key1758, 2), (key1704, 2), (key1753, 2), (key1888, 2), (key1857, 2), (key1888, 2)]

def rawRow12901 : Integer.Sparse Key := [(key1708, -6), (key1704, -6), (key1704, -6), (key1857, -6), (key1285, 2), (key1281, 2), (key1281, 2), (key1758, 2), (key1753, 2), (key1758, 2), (key1704, 2), (key1753, 2), (key1704, 2), (key1888, 2), (key1888, 2), (key1857, 2)]

def rawRow12902 : Integer.Sparse Key := [(key1704, -6), (key1704, -6), (key1857, -6), (key1708, -6), (key1704, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1281, 2), (key1753, 2), (key1753, 2), (key1888, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1758, 2)]

def rawRow12903 : Integer.Sparse Key := [(key1704, -6), (key1857, -6), (key1704, -6), (key1708, -6), (key1704, 2), (key1857, 2), (key1704, 2), (key1753, 2), (key1888, 2), (key1281, 2), (key1888, 2), (key1281, 2), (key1753, 2), (key1758, 2), (key1285, 2), (key1758, 2)]

def rawRow12904 : Integer.Sparse Key := [(key1857, -6), (key1704, -6), (key1704, -6), (key1708, -6), (key1857, 2), (key1704, 2), (key1704, 2), (key1888, 2), (key1753, 2), (key1888, 2), (key1281, 2), (key1753, 2), (key1281, 2), (key1758, 2), (key1758, 2), (key1285, 2)]

def rawRow12905 : Integer.Sparse Key := [(key1704, -6), (key1708, -6), (key1857, -6), (key1704, -6), (key1753, 2), (key1758, 2), (key1888, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1281, 2), (key1704, 2), (key1753, 2)]

def rawRow12906 : Integer.Sparse Key := [(key1708, -6), (key1704, -6), (key1857, -6), (key1704, -6), (key1758, 2), (key1753, 2), (key1888, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1281, 2), (key1753, 2), (key1704, 2)]

def rawRow12907 : Integer.Sparse Key := [(key1704, -6), (key1857, -6), (key1708, -6), (key1704, -6), (key1753, 2), (key1888, 2), (key1758, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1704, 2), (key1281, 2), (key1753, 2)]

def rawRow12908 : Integer.Sparse Key := [(key1857, -6), (key1704, -6), (key1708, -6), (key1704, -6), (key1888, 2), (key1753, 2), (key1758, 2), (key1857, 2), (key1704, 2), (key1888, 2), (key1281, 2), (key1758, 2), (key1285, 2), (key1704, 2), (key1753, 2), (key1281, 2)]

def rawRow12909 : Integer.Sparse Key := [(key1708, -6), (key1857, -6), (key1704, -6), (key1704, -6), (key1758, 2), (key1888, 2), (key1753, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1753, 2), (key1281, 2), (key1704, 2)]

def rawRow12910 : Integer.Sparse Key := [(key1857, -6), (key1708, -6), (key1704, -6), (key1704, -6), (key1888, 2), (key1758, 2), (key1753, 2), (key1888, 2), (key1758, 2), (key1857, 2), (key1285, 2), (key1704, 2), (key1281, 2), (key1753, 2), (key1704, 2), (key1281, 2)]

def rawRow12911 : Integer.Sparse Key := [(key1753, -6), (key1758, -6), (key1758, -6), (key1888, -6), (key1281, 2), (key1285, 2), (key1285, 2), (key1704, 2), (key1708, 2), (key1704, 2), (key1758, 2), (key1708, 2), (key1758, 2), (key1857, 2), (key1857, 2), (key1888, 2)]

def rawRow12912 : Integer.Sparse Key := [(key1758, -6), (key1753, -6), (key1758, -6), (key1888, -6), (key1285, 2), (key1281, 2), (key1285, 2), (key1708, 2), (key1704, 2), (key1758, 2), (key1704, 2), (key1758, 2), (key1708, 2), (key1857, 2), (key1888, 2), (key1857, 2)]

def rawRow12913 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1753, -6), (key1888, -6), (key1285, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1758, 2), (key1708, 2), (key1708, 2), (key1704, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1857, 2)]

def rawRow12914 : Integer.Sparse Key := [(key1753, -6), (key1758, -6), (key1888, -6), (key1758, -6), (key1704, 2), (key1708, 2), (key1857, 2), (key1281, 2), (key1285, 2), (key1704, 2), (key1758, 2), (key1857, 2), (key1888, 2), (key1285, 2), (key1708, 2), (key1758, 2)]

def rawRow12915 : Integer.Sparse Key := [(key1758, -6), (key1753, -6), (key1888, -6), (key1758, -6), (key1708, 2), (key1704, 2), (key1857, 2), (key1285, 2), (key1281, 2), (key1758, 2), (key1704, 2), (key1888, 2), (key1857, 2), (key1285, 2), (key1758, 2), (key1708, 2)]

def rawRow12916 : Integer.Sparse Key := [(key1753, -6), (key1888, -6), (key1758, -6), (key1758, -6), (key1704, 2), (key1857, 2), (key1708, 2), (key1704, 2), (key1857, 2), (key1281, 2), (key1888, 2), (key1285, 2), (key1758, 2), (key1708, 2), (key1285, 2), (key1758, 2)]

def rawRow12917 : Integer.Sparse Key := [(key1888, -6), (key1753, -6), (key1758, -6), (key1758, -6), (key1857, 2), (key1704, 2), (key1708, 2), (key1857, 2), (key1704, 2), (key1888, 2), (key1281, 2), (key1758, 2), (key1285, 2), (key1708, 2), (key1758, 2), (key1285, 2)]

def rawRow12918 : Integer.Sparse Key := [(key1758, -6), (key1888, -6), (key1753, -6), (key1758, -6), (key1708, 2), (key1857, 2), (key1704, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1758, 2), (key1285, 2), (key1708, 2)]

def rawRow12919 : Integer.Sparse Key := [(key1888, -6), (key1758, -6), (key1753, -6), (key1758, -6), (key1857, 2), (key1708, 2), (key1704, 2), (key1888, 2), (key1758, 2), (key1857, 2), (key1285, 2), (key1704, 2), (key1281, 2), (key1758, 2), (key1708, 2), (key1285, 2)]

def rawRow12920 : Integer.Sparse Key := [(key1758, -6), (key1758, -6), (key1888, -6), (key1753, -6), (key1758, 2), (key1758, 2), (key1888, 2), (key1285, 2), (key1285, 2), (key1708, 2), (key1708, 2), (key1857, 2), (key1857, 2), (key1281, 2), (key1704, 2), (key1704, 2)]

def rawRow12921 : Integer.Sparse Key := [(key1758, -6), (key1888, -6), (key1758, -6), (key1753, -6), (key1758, 2), (key1888, 2), (key1758, 2), (key1708, 2), (key1857, 2), (key1285, 2), (key1857, 2), (key1285, 2), (key1708, 2), (key1704, 2), (key1281, 2), (key1704, 2)]

def rawRow12922 : Integer.Sparse Key := [(key1888, -6), (key1758, -6), (key1758, -6), (key1753, -6), (key1888, 2), (key1758, 2), (key1758, 2), (key1857, 2), (key1708, 2), (key1857, 2), (key1285, 2), (key1708, 2), (key1285, 2), (key1704, 2), (key1704, 2), (key1281, 2)]

def rawRow12923 : Integer.Sparse Key := [(key1494, -6), (key1720, -6), (key1726, -6), (key1726, -6), (key1368, 6), (key1720, 6), (key1744, 6), (key1744, 6)]

def rawRow12924 : Integer.Sparse Key := [(key1494, -6), (key1726, -6), (key1720, -6), (key1726, -6), (key1368, 6), (key1744, 6), (key1720, 6), (key1744, 6)]

def rawRow12925 : Integer.Sparse Key := [(key1494, -6), (key1726, -6), (key1726, -6), (key1720, -6), (key1368, 6), (key1744, 6), (key1744, 6), (key1720, 6)]

def rawRow12926 : Integer.Sparse Key := [(key1720, -6), (key1494, -6), (key1726, -6), (key1726, -6), (key1720, 6), (key1368, 6), (key1744, 6), (key1744, 6)]

def rawRow12927 : Integer.Sparse Key := [(key1720, -6), (key1726, -6), (key1494, -6), (key1726, -6), (key1720, 6), (key1744, 6), (key1368, 6), (key1744, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block125
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12928 : Integer.Sparse Key := [(key1720, -6), (key1726, -6), (key1726, -6), (key1494, -6), (key1720, 6), (key1744, 6), (key1744, 6), (key1368, 6)]

def rawRow12929 : Integer.Sparse Key := [(key1726, -6), (key1494, -6), (key1720, -6), (key1726, -6), (key1744, 6), (key1368, 6), (key1720, 6), (key1744, 6)]

def rawRow12930 : Integer.Sparse Key := [(key1726, -6), (key1494, -6), (key1726, -6), (key1720, -6), (key1744, 6), (key1368, 6), (key1744, 6), (key1720, 6)]

def rawRow12931 : Integer.Sparse Key := [(key1726, -6), (key1720, -6), (key1494, -6), (key1726, -6), (key1744, 6), (key1720, 6), (key1368, 6), (key1744, 6)]

def rawRow12932 : Integer.Sparse Key := [(key1726, -6), (key1720, -6), (key1726, -6), (key1494, -6), (key1744, 6), (key1720, 6), (key1744, 6), (key1368, 6)]

def rawRow12933 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1494, -6), (key1720, -6), (key1744, 6), (key1744, 6), (key1368, 6), (key1720, 6)]

def rawRow12934 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1720, -6), (key1494, -6), (key1744, 6), (key1744, 6), (key1720, 6), (key1368, 6)]

def rawRow12935 : Integer.Sparse Key := [(key1516, -6), (key1744, -6), (key1744, -6), (key1755, -6), (key1377, 6), (key1726, 6), (key1726, 6), (key1755, 6)]

def rawRow12936 : Integer.Sparse Key := [(key1516, -6), (key1744, -6), (key1755, -6), (key1744, -6), (key1377, 6), (key1726, 6), (key1755, 6), (key1726, 6)]

def rawRow12937 : Integer.Sparse Key := [(key1516, -6), (key1755, -6), (key1744, -6), (key1744, -6), (key1377, 6), (key1755, 6), (key1726, 6), (key1726, 6)]

def rawRow12938 : Integer.Sparse Key := [(key1744, -6), (key1516, -6), (key1744, -6), (key1755, -6), (key1726, 6), (key1377, 6), (key1726, 6), (key1755, 6)]

def rawRow12939 : Integer.Sparse Key := [(key1744, -6), (key1516, -6), (key1755, -6), (key1744, -6), (key1726, 6), (key1377, 6), (key1755, 6), (key1726, 6)]

def rawRow12940 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1516, -6), (key1755, -6), (key1726, 6), (key1726, 6), (key1377, 6), (key1755, 6)]

def rawRow12941 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1755, -6), (key1516, -6), (key1726, 6), (key1726, 6), (key1755, 6), (key1377, 6)]

def rawRow12942 : Integer.Sparse Key := [(key1744, -6), (key1755, -6), (key1516, -6), (key1744, -6), (key1726, 6), (key1755, 6), (key1377, 6), (key1726, 6)]

def rawRow12943 : Integer.Sparse Key := [(key1744, -6), (key1755, -6), (key1744, -6), (key1516, -6), (key1726, 6), (key1755, 6), (key1726, 6), (key1377, 6)]

def rawRow12944 : Integer.Sparse Key := [(key1755, -6), (key1516, -6), (key1744, -6), (key1744, -6), (key1755, 6), (key1377, 6), (key1726, 6), (key1726, 6)]

def rawRow12945 : Integer.Sparse Key := [(key1755, -6), (key1744, -6), (key1516, -6), (key1744, -6), (key1755, 6), (key1726, 6), (key1377, 6), (key1726, 6)]

def rawRow12946 : Integer.Sparse Key := [(key1755, -6), (key1744, -6), (key1744, -6), (key1516, -6), (key1755, 6), (key1726, 6), (key1726, 6), (key1377, 6)]

def rawRow12947 : Integer.Sparse Key := [(key1366, -2), (key1370, -2), (key1370, -2), (key1718, -2), (key1747, -2), (key1747, -2), (key1865, -2), (key1865, -2), (key1880, -2), (key1880, -2), (key1883, -2), (key1883, -2), (key1366, 2), (key1379, 2), (key1379, 2), (key1492, 2), (key1519, 2), (key1519, 2), (key1870, 2), (key1870, 2), (key1880, 2), (key1880, 2), (key1891, 2), (key1891, 2)]

def rawRow12948 : Integer.Sparse Key := [(key1370, -2), (key1366, -2), (key1370, -2), (key1747, -2), (key1718, -2), (key1747, -2), (key1880, -2), (key1883, -2), (key1865, -2), (key1883, -2), (key1865, -2), (key1880, -2), (key1379, 2), (key1366, 2), (key1379, 2), (key1519, 2), (key1492, 2), (key1519, 2), (key1880, 2), (key1891, 2), (key1870, 2), (key1891, 2), (key1870, 2), (key1880, 2)]

def rawRow12949 : Integer.Sparse Key := [(key1370, -2), (key1370, -2), (key1366, -2), (key1747, -2), (key1747, -2), (key1718, -2), (key1883, -2), (key1880, -2), (key1883, -2), (key1865, -2), (key1880, -2), (key1865, -2), (key1379, 2), (key1379, 2), (key1366, 2), (key1519, 2), (key1519, 2), (key1492, 2), (key1891, 2), (key1880, 2), (key1891, 2), (key1870, 2), (key1880, 2), (key1870, 2)]

def rawRow12950 : Integer.Sparse Key := [(key1718, -2), (key1865, -2), (key1865, -2), (key1366, -2), (key1880, -2), (key1880, -2), (key1370, -2), (key1370, -2), (key1747, -2), (key1747, -2), (key1883, -2), (key1883, -2), (key1492, 2), (key1870, 2), (key1870, 2), (key1366, 2), (key1880, 2), (key1880, 2), (key1379, 2), (key1379, 2), (key1519, 2), (key1519, 2), (key1891, 2), (key1891, 2)]

def rawRow12951 : Integer.Sparse Key := [(key1865, -2), (key1718, -2), (key1865, -2), (key1880, -2), (key1366, -2), (key1880, -2), (key1747, -2), (key1883, -2), (key1370, -2), (key1883, -2), (key1370, -2), (key1747, -2), (key1870, 2), (key1492, 2), (key1870, 2), (key1880, 2), (key1366, 2), (key1880, 2), (key1519, 2), (key1891, 2), (key1379, 2), (key1891, 2), (key1379, 2), (key1519, 2)]

def rawRow12952 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1718, -2), (key1880, -2), (key1880, -2), (key1366, -2), (key1883, -2), (key1747, -2), (key1883, -2), (key1370, -2), (key1747, -2), (key1370, -2), (key1870, 2), (key1870, 2), (key1492, 2), (key1880, 2), (key1880, 2), (key1366, 2), (key1891, 2), (key1519, 2), (key1891, 2), (key1379, 2), (key1519, 2), (key1379, 2)]

def rawRow12953 : Integer.Sparse Key := [(key1747, -2), (key1880, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1883, -2), (key1366, -2), (key1370, -2), (key1718, -2), (key1747, -2), (key1865, -2), (key1880, -2), (key1519, 2), (key1880, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1891, 2), (key1366, 2), (key1379, 2), (key1492, 2), (key1519, 2), (key1870, 2), (key1880, 2)]

def rawRow12954 : Integer.Sparse Key := [(key1747, -2), (key1883, -2), (key1880, -2), (key1370, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1366, -2), (key1747, -2), (key1718, -2), (key1880, -2), (key1865, -2), (key1519, 2), (key1891, 2), (key1880, 2), (key1379, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1366, 2), (key1519, 2), (key1492, 2), (key1880, 2), (key1870, 2)]

def rawRow12955 : Integer.Sparse Key := [(key1880, -2), (key1747, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1883, -2), (key1718, -2), (key1865, -2), (key1366, -2), (key1880, -2), (key1370, -2), (key1747, -2), (key1880, 2), (key1519, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1891, 2), (key1492, 2), (key1870, 2), (key1366, 2), (key1880, 2), (key1379, 2), (key1519, 2)]

def rawRow12956 : Integer.Sparse Key := [(key1880, -2), (key1883, -2), (key1747, -2), (key1865, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1718, -2), (key1880, -2), (key1366, -2), (key1747, -2), (key1370, -2), (key1880, 2), (key1891, 2), (key1519, 2), (key1870, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1492, 2), (key1880, 2), (key1366, 2), (key1519, 2), (key1379, 2)]

def rawRow12957 : Integer.Sparse Key := [(key1883, -2), (key1747, -2), (key1880, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1747, -2), (key1880, -2), (key1370, -2), (key1865, -2), (key1366, -2), (key1718, -2), (key1891, 2), (key1519, 2), (key1880, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1519, 2), (key1880, 2), (key1379, 2), (key1870, 2), (key1366, 2), (key1492, 2)]

def rawRow12958 : Integer.Sparse Key := [(key1883, -2), (key1880, -2), (key1747, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1880, -2), (key1747, -2), (key1865, -2), (key1370, -2), (key1718, -2), (key1366, -2), (key1891, 2), (key1880, 2), (key1519, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1880, 2), (key1519, 2), (key1870, 2), (key1379, 2), (key1492, 2), (key1366, 2)]

def rawRow12959 : Integer.Sparse Key := [(key1379, -2), (key1379, -2), (key1381, -2), (key1728, -2), (key1728, -2), (key1761, -2), (key1870, -2), (key1872, -2), (key1870, -2), (key1891, -2), (key1872, -2), (key1891, -2), (key1370, 2), (key1370, 2), (key1381, 2), (key1496, 2), (key1496, 2), (key1522, 2), (key1865, 2), (key1872, 2), (key1865, 2), (key1883, 2), (key1872, 2), (key1883, 2)]

def rawRow12960 : Integer.Sparse Key := [(key1379, -2), (key1381, -2), (key1379, -2), (key1728, -2), (key1761, -2), (key1728, -2), (key1872, -2), (key1870, -2), (key1891, -2), (key1870, -2), (key1891, -2), (key1872, -2), (key1370, 2), (key1381, 2), (key1370, 2), (key1496, 2), (key1522, 2), (key1496, 2), (key1872, 2), (key1865, 2), (key1883, 2), (key1865, 2), (key1883, 2), (key1872, 2)]

def rawRow12961 : Integer.Sparse Key := [(key1381, -2), (key1379, -2), (key1379, -2), (key1761, -2), (key1728, -2), (key1728, -2), (key1891, -2), (key1891, -2), (key1872, -2), (key1872, -2), (key1870, -2), (key1870, -2), (key1381, 2), (key1370, 2), (key1370, 2), (key1522, 2), (key1496, 2), (key1496, 2), (key1883, 2), (key1883, 2), (key1872, 2), (key1872, 2), (key1865, 2), (key1865, 2)]

def rawRow12962 : Integer.Sparse Key := [(key1728, -2), (key1870, -2), (key1872, -2), (key1379, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1381, -2), (key1728, -2), (key1761, -2), (key1872, -2), (key1891, -2), (key1496, 2), (key1865, 2), (key1872, 2), (key1370, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1381, 2), (key1496, 2), (key1522, 2), (key1872, 2), (key1883, 2)]

def rawRow12963 : Integer.Sparse Key := [(key1728, -2), (key1872, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1870, -2), (key1381, -2), (key1379, -2), (key1761, -2), (key1728, -2), (key1891, -2), (key1872, -2), (key1496, 2), (key1872, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1865, 2), (key1381, 2), (key1370, 2), (key1522, 2), (key1496, 2), (key1883, 2), (key1872, 2)]

def rawRow12964 : Integer.Sparse Key := [(key1870, -2), (key1728, -2), (key1872, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1728, -2), (key1872, -2), (key1379, -2), (key1891, -2), (key1381, -2), (key1761, -2), (key1865, 2), (key1496, 2), (key1872, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1496, 2), (key1872, 2), (key1370, 2), (key1883, 2), (key1381, 2), (key1522, 2)]

def rawRow12965 : Integer.Sparse Key := [(key1870, -2), (key1872, -2), (key1728, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1872, -2), (key1728, -2), (key1891, -2), (key1379, -2), (key1761, -2), (key1381, -2), (key1865, 2), (key1872, 2), (key1496, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1872, 2), (key1496, 2), (key1883, 2), (key1370, 2), (key1522, 2), (key1381, 2)]

def rawRow12966 : Integer.Sparse Key := [(key1872, -2), (key1728, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1870, -2), (key1761, -2), (key1891, -2), (key1381, -2), (key1872, -2), (key1379, -2), (key1728, -2), (key1872, 2), (key1496, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1865, 2), (key1522, 2), (key1883, 2), (key1381, 2), (key1872, 2), (key1370, 2), (key1496, 2)]

def rawRow12967 : Integer.Sparse Key := [(key1872, -2), (key1870, -2), (key1728, -2), (key1891, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1761, -2), (key1872, -2), (key1381, -2), (key1728, -2), (key1379, -2), (key1872, 2), (key1865, 2), (key1496, 2), (key1883, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1522, 2), (key1872, 2), (key1381, 2), (key1496, 2), (key1370, 2)]

def rawRow12968 : Integer.Sparse Key := [(key1761, -2), (key1891, -2), (key1891, -2), (key1381, -2), (key1872, -2), (key1872, -2), (key1379, -2), (key1379, -2), (key1728, -2), (key1728, -2), (key1870, -2), (key1870, -2), (key1522, 2), (key1883, 2), (key1883, 2), (key1381, 2), (key1872, 2), (key1872, 2), (key1370, 2), (key1370, 2), (key1496, 2), (key1496, 2), (key1865, 2), (key1865, 2)]

def rawRow12969 : Integer.Sparse Key := [(key1891, -2), (key1761, -2), (key1891, -2), (key1872, -2), (key1381, -2), (key1872, -2), (key1728, -2), (key1870, -2), (key1379, -2), (key1870, -2), (key1379, -2), (key1728, -2), (key1883, 2), (key1522, 2), (key1883, 2), (key1872, 2), (key1381, 2), (key1872, 2), (key1496, 2), (key1865, 2), (key1370, 2), (key1865, 2), (key1370, 2), (key1496, 2)]

def rawRow12970 : Integer.Sparse Key := [(key1891, -2), (key1891, -2), (key1761, -2), (key1872, -2), (key1872, -2), (key1381, -2), (key1870, -2), (key1728, -2), (key1870, -2), (key1379, -2), (key1728, -2), (key1379, -2), (key1883, 2), (key1883, 2), (key1522, 2), (key1872, 2), (key1872, 2), (key1381, 2), (key1865, 2), (key1496, 2), (key1865, 2), (key1370, 2), (key1496, 2), (key1370, 2)]

def rawRow12971 : Integer.Sparse Key := [(key227, 2), (key231, 2), (key231, 2), (key499, 2), (key560, 2), (key560, 2), (key623, 2), (key623, 2), (key649, 2), (key649, 2), (key653, 2), (key653, 2), (key231, -2), (key231, -2), (key233, -2), (key503, -2), (key503, -2), (key560, -2), (key560, -2), (key564, -2), (key564, -2), (key625, -2), (key653, -2), (key653, -2)]

def rawRow12972 : Integer.Sparse Key := [(key231, 2), (key227, 2), (key231, 2), (key560, 2), (key499, 2), (key560, 2), (key649, 2), (key653, 2), (key623, 2), (key653, 2), (key623, 2), (key649, 2), (key231, -2), (key233, -2), (key231, -2), (key560, -2), (key564, -2), (key503, -2), (key564, -2), (key503, -2), (key560, -2), (key653, -2), (key625, -2), (key653, -2)]

def rawRow12973 : Integer.Sparse Key := [(key231, 2), (key231, 2), (key227, 2), (key560, 2), (key560, 2), (key499, 2), (key653, 2), (key649, 2), (key653, 2), (key623, 2), (key649, 2), (key623, 2), (key233, -2), (key231, -2), (key231, -2), (key564, -2), (key560, -2), (key564, -2), (key503, -2), (key560, -2), (key503, -2), (key653, -2), (key653, -2), (key625, -2)]

def rawRow12974 : Integer.Sparse Key := [(key499, 2), (key623, 2), (key623, 2), (key227, 2), (key649, 2), (key649, 2), (key231, 2), (key231, 2), (key560, 2), (key560, 2), (key653, 2), (key653, 2), (key503, -2), (key503, -2), (key625, -2), (key231, -2), (key231, -2), (key560, -2), (key560, -2), (key653, -2), (key653, -2), (key233, -2), (key564, -2), (key564, -2)]

def rawRow12975 : Integer.Sparse Key := [(key623, 2), (key499, 2), (key623, 2), (key649, 2), (key227, 2), (key649, 2), (key560, 2), (key653, 2), (key231, 2), (key653, 2), (key231, 2), (key560, 2), (key503, -2), (key625, -2), (key503, -2), (key560, -2), (key653, -2), (key231, -2), (key653, -2), (key231, -2), (key560, -2), (key564, -2), (key233, -2), (key564, -2)]

def rawRow12976 : Integer.Sparse Key := [(key623, 2), (key623, 2), (key499, 2), (key649, 2), (key649, 2), (key227, 2), (key653, 2), (key560, 2), (key653, 2), (key231, 2), (key560, 2), (key231, 2), (key625, -2), (key503, -2), (key503, -2), (key653, -2), (key560, -2), (key653, -2), (key231, -2), (key560, -2), (key231, -2), (key564, -2), (key564, -2), (key233, -2)]

def rawRow12977 : Integer.Sparse Key := [(key560, 2), (key649, 2), (key653, 2), (key231, 2), (key623, 2), (key653, 2), (key227, 2), (key231, 2), (key499, 2), (key560, 2), (key623, 2), (key649, 2), (key560, -2), (key564, -2), (key653, -2), (key231, -2), (key233, -2), (key503, -2), (key564, -2), (key625, -2), (key653, -2), (key231, -2), (key503, -2), (key560, -2)]

def rawRow12978 : Integer.Sparse Key := [(key560, 2), (key653, 2), (key649, 2), (key231, 2), (key653, 2), (key623, 2), (key231, 2), (key227, 2), (key560, 2), (key499, 2), (key649, 2), (key623, 2), (key564, -2), (key560, -2), (key653, -2), (key233, -2), (key231, -2), (key564, -2), (key503, -2), (key653, -2), (key625, -2), (key231, -2), (key560, -2), (key503, -2)]

def rawRow12979 : Integer.Sparse Key := [(key649, 2), (key560, 2), (key653, 2), (key623, 2), (key231, 2), (key653, 2), (key499, 2), (key623, 2), (key227, 2), (key649, 2), (key231, 2), (key560, 2), (key560, -2), (key653, -2), (key564, -2), (key503, -2), (key625, -2), (key231, -2), (key653, -2), (key233, -2), (key564, -2), (key503, -2), (key231, -2), (key560, -2)]

def rawRow12980 : Integer.Sparse Key := [(key649, 2), (key653, 2), (key560, 2), (key623, 2), (key653, 2), (key231, 2), (key623, 2), (key499, 2), (key649, 2), (key227, 2), (key560, 2), (key231, 2), (key653, -2), (key560, -2), (key564, -2), (key625, -2), (key503, -2), (key653, -2), (key231, -2), (key564, -2), (key233, -2), (key503, -2), (key560, -2), (key231, -2)]

def rawRow12981 : Integer.Sparse Key := [(key653, 2), (key560, 2), (key649, 2), (key653, 2), (key231, 2), (key623, 2), (key560, 2), (key649, 2), (key231, 2), (key623, 2), (key227, 2), (key499, 2), (key564, -2), (key653, -2), (key560, -2), (key564, -2), (key653, -2), (key233, -2), (key625, -2), (key231, -2), (key503, -2), (key560, -2), (key231, -2), (key503, -2)]

def rawRow12982 : Integer.Sparse Key := [(key653, 2), (key649, 2), (key560, 2), (key653, 2), (key623, 2), (key231, 2), (key649, 2), (key560, 2), (key623, 2), (key231, 2), (key499, 2), (key227, 2), (key653, -2), (key564, -2), (key560, -2), (key653, -2), (key564, -2), (key625, -2), (key233, -2), (key503, -2), (key231, -2), (key560, -2), (key503, -2), (key231, -2)]

def rawRow12983 : Integer.Sparse Key := [(key231, 2), (key231, 2), (key233, 2), (key503, 2), (key503, 2), (key564, 2), (key623, 2), (key625, 2), (key623, 2), (key653, 2), (key625, 2), (key653, 2), (key227, -2), (key231, -2), (key231, -2), (key499, -2), (key503, -2), (key499, -2), (key560, -2), (key503, -2), (key560, -2), (key623, -2), (key623, -2), (key649, -2)]

def rawRow12984 : Integer.Sparse Key := [(key231, 2), (key233, 2), (key231, 2), (key503, 2), (key564, 2), (key503, 2), (key625, 2), (key623, 2), (key653, 2), (key623, 2), (key653, 2), (key625, 2), (key231, -2), (key227, -2), (key231, -2), (key503, -2), (key499, -2), (key560, -2), (key499, -2), (key560, -2), (key503, -2), (key623, -2), (key649, -2), (key623, -2)]

def rawRow12985 : Integer.Sparse Key := [(key233, 2), (key231, 2), (key231, 2), (key564, 2), (key503, 2), (key503, 2), (key653, 2), (key653, 2), (key625, 2), (key625, 2), (key623, 2), (key623, 2), (key231, -2), (key231, -2), (key227, -2), (key560, -2), (key560, -2), (key503, -2), (key503, -2), (key499, -2), (key499, -2), (key649, -2), (key623, -2), (key623, -2)]

def rawRow12986 : Integer.Sparse Key := [(key503, 2), (key623, 2), (key625, 2), (key231, 2), (key623, 2), (key653, 2), (key231, 2), (key233, 2), (key503, 2), (key564, 2), (key625, 2), (key653, 2), (key499, -2), (key503, -2), (key623, -2), (key227, -2), (key231, -2), (key499, -2), (key560, -2), (key623, -2), (key649, -2), (key231, -2), (key503, -2), (key560, -2)]

def rawRow12987 : Integer.Sparse Key := [(key503, 2), (key625, 2), (key623, 2), (key231, 2), (key653, 2), (key623, 2), (key233, 2), (key231, 2), (key564, 2), (key503, 2), (key653, 2), (key625, 2), (key503, -2), (key499, -2), (key623, -2), (key231, -2), (key227, -2), (key560, -2), (key499, -2), (key649, -2), (key623, -2), (key231, -2), (key560, -2), (key503, -2)]

def rawRow12988 : Integer.Sparse Key := [(key623, 2), (key503, 2), (key625, 2), (key623, 2), (key231, 2), (key653, 2), (key503, 2), (key625, 2), (key231, 2), (key653, 2), (key233, 2), (key564, 2), (key499, -2), (key623, -2), (key503, -2), (key499, -2), (key623, -2), (key227, -2), (key649, -2), (key231, -2), (key560, -2), (key503, -2), (key231, -2), (key560, -2)]

def rawRow12989 : Integer.Sparse Key := [(key623, 2), (key625, 2), (key503, 2), (key623, 2), (key653, 2), (key231, 2), (key625, 2), (key503, 2), (key653, 2), (key231, 2), (key564, 2), (key233, 2), (key623, -2), (key499, -2), (key503, -2), (key623, -2), (key499, -2), (key649, -2), (key227, -2), (key560, -2), (key231, -2), (key503, -2), (key560, -2), (key231, -2)]

def rawRow12990 : Integer.Sparse Key := [(key625, 2), (key503, 2), (key623, 2), (key653, 2), (key231, 2), (key623, 2), (key564, 2), (key653, 2), (key233, 2), (key625, 2), (key231, 2), (key503, 2), (key503, -2), (key623, -2), (key499, -2), (key560, -2), (key649, -2), (key231, -2), (key623, -2), (key227, -2), (key499, -2), (key560, -2), (key231, -2), (key503, -2)]

def rawRow12991 : Integer.Sparse Key := [(key625, 2), (key623, 2), (key503, 2), (key653, 2), (key623, 2), (key231, 2), (key653, 2), (key564, 2), (key625, 2), (key233, 2), (key503, 2), (key231, 2), (key623, -2), (key503, -2), (key499, -2), (key649, -2), (key560, -2), (key623, -2), (key231, -2), (key499, -2), (key227, -2), (key560, -2), (key503, -2), (key231, -2)]

def rawRow12992 : Integer.Sparse Key := [(key564, 2), (key653, 2), (key653, 2), (key233, 2), (key625, 2), (key625, 2), (key231, 2), (key231, 2), (key503, 2), (key503, 2), (key623, 2), (key623, 2), (key560, -2), (key560, -2), (key649, -2), (key231, -2), (key231, -2), (key503, -2), (key503, -2), (key623, -2), (key623, -2), (key227, -2), (key499, -2), (key499, -2)]

def rawRow12993 : Integer.Sparse Key := [(key653, 2), (key564, 2), (key653, 2), (key625, 2), (key233, 2), (key625, 2), (key503, 2), (key623, 2), (key231, 2), (key623, 2), (key231, 2), (key503, 2), (key560, -2), (key649, -2), (key560, -2), (key503, -2), (key623, -2), (key231, -2), (key623, -2), (key231, -2), (key503, -2), (key499, -2), (key227, -2), (key499, -2)]

def rawRow12994 : Integer.Sparse Key := [(key653, 2), (key653, 2), (key564, 2), (key625, 2), (key625, 2), (key233, 2), (key623, 2), (key503, 2), (key623, 2), (key231, 2), (key503, 2), (key231, 2), (key649, -2), (key560, -2), (key560, -2), (key623, -2), (key503, -2), (key623, -2), (key231, -2), (key503, -2), (key231, -2), (key499, -2), (key499, -2), (key227, -2)]

def rawRow12995 : Integer.Sparse Key := [(key1505, -4), (key1509, -4), (key1509, -4), (key1738, -4), (key1738, -4), (key1745, -4), (key1509, 6), (key1509, 6), (key1517, 6), (key1745, 6)]

def rawRow12996 : Integer.Sparse Key := [(key1509, -4), (key1505, -4), (key1509, -4), (key1738, -4), (key1745, -4), (key1738, -4), (key1509, 6), (key1517, 6), (key1509, 6), (key1745, 6)]

def rawRow12997 : Integer.Sparse Key := [(key1509, -4), (key1509, -4), (key1505, -4), (key1745, -4), (key1738, -4), (key1738, -4), (key1517, 6), (key1509, 6), (key1509, 6), (key1745, 6)]

def rawRow12998 : Integer.Sparse Key := [(key1505, -4), (key1738, -4), (key1738, -4), (key1509, -4), (key1509, -4), (key1745, -4), (key1509, 6), (key1509, 6), (key1745, 6), (key1517, 6)]

def rawRow12999 : Integer.Sparse Key := [(key1738, -4), (key1505, -4), (key1738, -4), (key1509, -4), (key1745, -4), (key1509, -4), (key1509, 6), (key1745, 6), (key1509, 6), (key1517, 6)]

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

def rawRow18456 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key0, 24), (key83, 24), (key83, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1107 : Integer.Sparse Key := [(key1686, -6), (key1581, 2), (key1581, 2), (key1581, 2), (key1923, 6), (key1432, -2), (key1432, -2), (key1432, -2), (key1906, -2), (key1906, -2), (key1906, -2), (key1475, 2), (key1475, 2), (key1475, 2)]

def rawRow1108 : Integer.Sparse Key := [(key1906, -6), (key1906, 2), (key1906, 2), (key1923, 2), (key1475, 6), (key1475, -2), (key1475, -2), (key1686, -2), (key1404, -2), (key1404, -2), (key1432, -2), (key1404, 2), (key1404, 2), (key1581, 2)]

def rawRow1109 : Integer.Sparse Key := [(key1906, -6), (key1906, 2), (key1923, 2), (key1906, 2), (key1475, 6), (key1475, -2), (key1686, -2), (key1475, -2), (key1404, -2), (key1432, -2), (key1404, -2), (key1404, 2), (key1581, 2), (key1404, 2)]

def rawRow1110 : Integer.Sparse Key := [(key1906, -6), (key1923, 2), (key1906, 2), (key1906, 2), (key1475, 6), (key1686, -2), (key1475, -2), (key1475, -2), (key1432, -2), (key1404, -2), (key1404, -2), (key1581, 2), (key1404, 2), (key1404, 2)]

def rawRow1111 : Integer.Sparse Key := [(key1923, -6), (key1906, 2), (key1906, 2), (key1906, 2), (key1686, 6), (key1475, -2), (key1475, -2), (key1475, -2), (key1581, -2), (key1581, -2), (key1581, -2), (key1432, 2), (key1432, 2), (key1432, 2)]

def rawRow1112 : Integer.Sparse Key := [(key2710, -2), (key2717, -2), (key2717, -2), (key2679, 1), (key2691, 1), (key2679, 1), (key2755, 1), (key2691, 1), (key2755, 1), (key2813, 2), (key2820, 2), (key2820, 2), (key2679, -1), (key2691, -1), (key3047, -1), (key3115, -1), (key3058, -1), (key3115, -1), (key3096, -1), (key3113, -1), (key3096, -1), (key3142, -1), (key3113, -1), (key3142, -1), (key3061, 1), (key3075, 1), (key3061, 1), (key3143, 1), (key3075, 1), (key3143, 1)]

def rawRow1113 : Integer.Sparse Key := [(key2717, -2), (key2710, -2), (key2717, -2), (key2691, 1), (key2679, 1), (key2755, 1), (key2679, 1), (key2755, 1), (key2691, 1), (key2820, 2), (key2813, 2), (key2820, 2), (key2691, -1), (key2679, -1), (key3115, -1), (key3047, -1), (key3115, -1), (key3058, -1), (key3113, -1), (key3096, -1), (key3142, -1), (key3096, -1), (key3142, -1), (key3113, -1), (key3075, 1), (key3061, 1), (key3143, 1), (key3061, 1), (key3143, 1), (key3075, 1)]

def rawRow1114 : Integer.Sparse Key := [(key2717, -2), (key2717, -2), (key2710, -2), (key2755, 1), (key2755, 1), (key2691, 1), (key2691, 1), (key2679, 1), (key2679, 1), (key2820, 2), (key2820, 2), (key2813, 2), (key3014, -1), (key3014, -1), (key2691, -1), (key2691, -1), (key2679, -1), (key3047, -1), (key3142, -1), (key3142, -1), (key3113, -1), (key3113, -1), (key3096, -1), (key3096, -1), (key3143, 1), (key3143, 1), (key3075, 1), (key3075, 1), (key3061, 1), (key3061, 1)]

def rawRow1115 : Integer.Sparse Key := [(key2754, -2), (key2755, -2), (key2755, -2), (key2684, 1), (key2691, 1), (key2684, 1), (key2717, 1), (key2691, 1), (key2717, 1), (key3013, 2), (key3014, 2), (key3014, 2), (key2684, -1), (key2691, -1), (key2684, -1), (key2820, -1), (key2691, -1), (key2820, -1), (key3105, -1), (key3115, -1), (key3105, -1), (key3143, -1), (key3115, -1), (key3143, -1), (key3068, 1), (key3076, 1), (key3068, 1), (key3142, 1), (key3076, 1), (key3142, 1)]

def rawRow1116 : Integer.Sparse Key := [(key2755, -2), (key2754, -2), (key2755, -2), (key2691, 1), (key2684, 1), (key2717, 1), (key2684, 1), (key2717, 1), (key2691, 1), (key3014, 2), (key3013, 2), (key3014, 2), (key2691, -1), (key2684, -1), (key2820, -1), (key2684, -1), (key2820, -1), (key2691, -1), (key3115, -1), (key3105, -1), (key3143, -1), (key3105, -1), (key3143, -1), (key3115, -1), (key3076, 1), (key3068, 1), (key3142, 1), (key3068, 1), (key3142, 1), (key3076, 1)]

def rawRow1117 : Integer.Sparse Key := [(key2755, -2), (key2755, -2), (key2754, -2), (key2717, 1), (key2717, 1), (key2691, 1), (key2691, 1), (key2684, 1), (key2684, 1), (key3014, 2), (key3014, 2), (key3013, 2), (key2820, -1), (key2820, -1), (key2691, -1), (key2691, -1), (key2684, -1), (key2684, -1), (key3143, -1), (key3143, -1), (key3115, -1), (key3115, -1), (key3105, -1), (key3105, -1), (key3142, 1), (key3142, 1), (key3076, 1), (key3076, 1), (key3068, 1), (key3068, 1)]

def rawRow1118 : Integer.Sparse Key := [(key2813, -2), (key2820, -2), (key2820, -2), (key2813, 1), (key2820, 1), (key2813, 1), (key2921, 1), (key2820, 1), (key2921, 1), (key2710, 2), (key2717, 2), (key2717, 2), (key2710, -1), (key2717, -1), (key2710, -1), (key3024, -1), (key2717, -1), (key3024, -1), (key2679, -1), (key2691, -1), (key2679, -1), (key2755, -1), (key2691, -1), (key2755, -1), (key2679, 1), (key2691, 1), (key3047, 1), (key3115, 1), (key3058, 1), (key3115, 1)]

def rawRow1119 : Integer.Sparse Key := [(key2820, -2), (key2813, -2), (key2820, -2), (key2820, 1), (key2813, 1), (key2921, 1), (key2813, 1), (key2921, 1), (key2820, 1), (key2717, 2), (key2710, 2), (key2717, 2), (key2717, -1), (key2710, -1), (key3024, -1), (key2710, -1), (key3024, -1), (key2717, -1), (key2691, -1), (key2679, -1), (key2755, -1), (key2679, -1), (key2755, -1), (key2691, -1), (key2691, 1), (key2679, 1), (key3115, 1), (key3047, 1), (key3115, 1), (key3058, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1120 : Integer.Sparse Key := [(key2820, -2), (key2820, -2), (key2813, -2), (key2921, 1), (key2921, 1), (key2820, 1), (key2820, 1), (key2813, 1), (key2813, 1), (key2717, 2), (key2717, 2), (key2710, 2), (key3024, -1), (key3024, -1), (key2717, -1), (key2717, -1), (key2710, -1), (key2710, -1), (key2755, -1), (key2755, -1), (key2691, -1), (key2691, -1), (key2679, -1), (key2679, -1), (key3014, 1), (key3014, 1), (key2691, 1), (key2691, 1), (key2679, 1), (key3047, 1)]

def rawRow1121 : Integer.Sparse Key := [(key2921, -2), (key2921, -2), (key2921, -2), (key2820, 1), (key2820, 1), (key2820, 1), (key2820, 1), (key2820, 1), (key2820, 1), (key3024, 2), (key3024, 2), (key3024, 2), (key2717, -1), (key2717, -1), (key2717, -1), (key2717, -1), (key2717, -1), (key2717, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key3014, -1), (key2755, 1), (key2755, 1), (key2755, 1), (key2755, 1), (key2755, 1), (key2755, 1)]

def rawRow1122 : Integer.Sparse Key := [(key3013, -2), (key3014, -2), (key3014, -2), (key3013, 1), (key3014, 1), (key3013, 1), (key3024, 1), (key3014, 1), (key3024, 1), (key2754, 2), (key2755, 2), (key2755, 2), (key2754, -1), (key2755, -1), (key2754, -1), (key2921, -1), (key2755, -1), (key2921, -1), (key2684, -1), (key2691, -1), (key2684, -1), (key2717, -1), (key2691, -1), (key2717, -1), (key2684, 1), (key2691, 1), (key2684, 1), (key2820, 1), (key2691, 1), (key2820, 1)]

def rawRow1123 : Integer.Sparse Key := [(key3014, -2), (key3013, -2), (key3014, -2), (key3014, 1), (key3013, 1), (key3024, 1), (key3013, 1), (key3024, 1), (key3014, 1), (key2755, 2), (key2754, 2), (key2755, 2), (key2755, -1), (key2754, -1), (key2921, -1), (key2754, -1), (key2921, -1), (key2755, -1), (key2691, -1), (key2684, -1), (key2717, -1), (key2684, -1), (key2717, -1), (key2691, -1), (key2691, 1), (key2684, 1), (key2820, 1), (key2684, 1), (key2820, 1), (key2691, 1)]

def rawRow1124 : Integer.Sparse Key := [(key3014, -2), (key3014, -2), (key3013, -2), (key3024, 1), (key3024, 1), (key3014, 1), (key3014, 1), (key3013, 1), (key3013, 1), (key2755, 2), (key2755, 2), (key2754, 2), (key2921, -1), (key2921, -1), (key2755, -1), (key2755, -1), (key2754, -1), (key2754, -1), (key2717, -1), (key2717, -1), (key2691, -1), (key2691, -1), (key2684, -1), (key2684, -1), (key2820, 1), (key2820, 1), (key2691, 1), (key2691, 1), (key2684, 1), (key2684, 1)]

def rawRow1125 : Integer.Sparse Key := [(key3024, -2), (key3024, -2), (key3024, -2), (key3014, 1), (key3014, 1), (key3014, 1), (key3014, 1), (key3014, 1), (key3014, 1), (key2921, 2), (key2921, 2), (key2921, 2), (key2755, -1), (key2755, -1), (key2755, -1), (key2755, -1), (key2755, -1), (key2755, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2820, -1), (key2717, 1), (key2717, 1), (key2717, 1), (key2717, 1), (key2717, 1), (key2717, 1)]

def rawRow1126 : Integer.Sparse Key := [(key1048, -2), (key1062, -2), (key1062, -2), (key1054, 6), (key1134, 2), (key1142, 2), (key1142, 2), (key1054, -2), (key1054, -2), (key1238, -2), (key1142, -6), (key1062, 2), (key1062, 2), (key1240, 2)]

def rawRow1127 : Integer.Sparse Key := [(key1062, -2), (key1048, -2), (key1062, -2), (key1054, 6), (key1142, 2), (key1134, 2), (key1142, 2), (key1054, -2), (key1238, -2), (key1054, -2), (key1142, -6), (key1062, 2), (key1240, 2), (key1062, 2)]

def rawRow1128 : Integer.Sparse Key := [(key1062, -2), (key1062, -2), (key1048, -2), (key1054, 6), (key1142, 2), (key1142, 2), (key1134, 2), (key1238, -2), (key1054, -2), (key1054, -2), (key1142, -6), (key1240, 2), (key1062, 2), (key1062, 2)]

def rawRow1129 : Integer.Sparse Key := [(key1054, -2), (key1062, -2), (key1062, -2), (key1048, 6), (key1238, 2), (key1240, 2), (key1240, 2), (key1048, -2), (key1048, -2), (key1134, -2), (key1240, -6), (key1062, 2), (key1062, 2), (key1142, 2)]

def rawRow1130 : Integer.Sparse Key := [(key1062, -2), (key1054, -2), (key1062, -2), (key1048, 6), (key1240, 2), (key1238, 2), (key1240, 2), (key1048, -2), (key1134, -2), (key1048, -2), (key1240, -6), (key1062, 2), (key1142, 2), (key1062, 2)]

def rawRow1131 : Integer.Sparse Key := [(key1062, -2), (key1062, -2), (key1054, -2), (key1048, 6), (key1240, 2), (key1240, 2), (key1238, 2), (key1134, -2), (key1048, -2), (key1048, -2), (key1240, -6), (key1142, 2), (key1062, 2), (key1062, 2)]

def rawRow1132 : Integer.Sparse Key := [(key1134, -2), (key1142, -2), (key1142, -2), (key1142, 6), (key1048, 2), (key1062, 2), (key1062, 2), (key1062, -2), (key1062, -2), (key1240, -2), (key1054, -6), (key1054, 2), (key1054, 2), (key1238, 2)]

def rawRow1133 : Integer.Sparse Key := [(key1142, -2), (key1134, -2), (key1142, -2), (key1142, 6), (key1062, 2), (key1048, 2), (key1062, 2), (key1062, -2), (key1240, -2), (key1062, -2), (key1054, -6), (key1054, 2), (key1238, 2), (key1054, 2)]

def rawRow1134 : Integer.Sparse Key := [(key1142, -2), (key1142, -2), (key1134, -2), (key1142, 6), (key1062, 2), (key1062, 2), (key1048, 2), (key1240, -2), (key1062, -2), (key1062, -2), (key1054, -6), (key1238, 2), (key1054, 2), (key1054, 2)]

def rawRow1135 : Integer.Sparse Key := [(key1142, -2), (key1142, -2), (key1142, -2), (key1134, 6), (key1240, 2), (key1240, 2), (key1240, 2), (key1048, -2), (key1048, -2), (key1048, -2), (key1238, -6), (key1054, 2), (key1054, 2), (key1054, 2)]

def rawRow1136 : Integer.Sparse Key := [(key1238, -2), (key1240, -2), (key1240, -2), (key1240, 6), (key1054, 2), (key1062, 2), (key1062, 2), (key1062, -2), (key1062, -2), (key1142, -2), (key1048, -6), (key1048, 2), (key1048, 2), (key1134, 2)]

def rawRow1137 : Integer.Sparse Key := [(key1240, -2), (key1238, -2), (key1240, -2), (key1240, 6), (key1062, 2), (key1054, 2), (key1062, 2), (key1062, -2), (key1142, -2), (key1062, -2), (key1048, -6), (key1048, 2), (key1134, 2), (key1048, 2)]

def rawRow1138 : Integer.Sparse Key := [(key1240, -2), (key1240, -2), (key1238, -2), (key1240, 6), (key1062, 2), (key1062, 2), (key1054, 2), (key1142, -2), (key1062, -2), (key1062, -2), (key1048, -6), (key1134, 2), (key1048, 2), (key1048, 2)]

def rawRow1139 : Integer.Sparse Key := [(key1240, -2), (key1240, -2), (key1240, -2), (key1238, 6), (key1142, 2), (key1142, 2), (key1142, 2), (key1054, -2), (key1054, -2), (key1054, -2), (key1134, -6), (key1048, 2), (key1048, 2), (key1048, 2)]

def rawRow1140 : Integer.Sparse Key := [(key3063, -6), (key3049, 2), (key3049, 2), (key3065, 2), (key3098, 6), (key3049, -2), (key3049, -2), (key3102, -2), (key3098, -2), (key3098, -2), (key3124, -2), (key3063, 2), (key3063, 2), (key3126, 2)]

def rawRow1141 : Integer.Sparse Key := [(key3063, -6), (key3049, 2), (key3065, 2), (key3049, 2), (key3098, 6), (key3049, -2), (key3102, -2), (key3049, -2), (key3098, -2), (key3124, -2), (key3098, -2), (key3063, 2), (key3126, 2), (key3063, 2)]

def rawRow1142 : Integer.Sparse Key := [(key3063, -6), (key3065, 2), (key3049, 2), (key3049, 2), (key3098, 6), (key3102, -2), (key3049, -2), (key3049, -2), (key3124, -2), (key3098, -2), (key3098, -2), (key3126, 2), (key3063, 2), (key3063, 2)]

def rawRow1143 : Integer.Sparse Key := [(key3065, -6), (key3049, 2), (key3049, 2), (key3063, 2), (key3102, 6), (key3049, -2), (key3049, -2), (key3098, -2), (key3102, -2), (key3102, -2), (key3126, -2), (key3065, 2), (key3065, 2), (key3124, 2)]

def rawRow1144 : Integer.Sparse Key := [(key3065, -6), (key3049, 2), (key3063, 2), (key3049, 2), (key3102, 6), (key3049, -2), (key3098, -2), (key3049, -2), (key3102, -2), (key3126, -2), (key3102, -2), (key3065, 2), (key3124, 2), (key3065, 2)]

def rawRow1145 : Integer.Sparse Key := [(key3065, -6), (key3063, 2), (key3049, 2), (key3049, 2), (key3102, 6), (key3098, -2), (key3049, -2), (key3049, -2), (key3126, -2), (key3102, -2), (key3102, -2), (key3124, 2), (key3065, 2), (key3065, 2)]

def rawRow1146 : Integer.Sparse Key := [(key3098, -6), (key3098, 2), (key3098, 2), (key3124, 2), (key3063, 6), (key3063, -2), (key3063, -2), (key3126, -2), (key3049, -2), (key3049, -2), (key3065, -2), (key3049, 2), (key3049, 2), (key3102, 2)]

def rawRow1147 : Integer.Sparse Key := [(key3098, -6), (key3098, 2), (key3124, 2), (key3098, 2), (key3063, 6), (key3063, -2), (key3126, -2), (key3063, -2), (key3049, -2), (key3065, -2), (key3049, -2), (key3049, 2), (key3102, 2), (key3049, 2)]

def rawRow1148 : Integer.Sparse Key := [(key3098, -6), (key3124, 2), (key3098, 2), (key3098, 2), (key3063, 6), (key3126, -2), (key3063, -2), (key3063, -2), (key3065, -2), (key3049, -2), (key3049, -2), (key3102, 2), (key3049, 2), (key3049, 2)]

def rawRow1149 : Integer.Sparse Key := [(key3124, -6), (key3098, 2), (key3098, 2), (key3098, 2), (key3126, 6), (key3063, -2), (key3063, -2), (key3063, -2), (key3102, -2), (key3102, -2), (key3102, -2), (key3065, 2), (key3065, 2), (key3065, 2)]

def rawRow1150 : Integer.Sparse Key := [(key3102, -6), (key3102, 2), (key3102, 2), (key3126, 2), (key3065, 6), (key3065, -2), (key3065, -2), (key3124, -2), (key3049, -2), (key3049, -2), (key3063, -2), (key3049, 2), (key3049, 2), (key3098, 2)]

def rawRow1151 : Integer.Sparse Key := [(key3102, -6), (key3102, 2), (key3126, 2), (key3102, 2), (key3065, 6), (key3065, -2), (key3124, -2), (key3065, -2), (key3049, -2), (key3063, -2), (key3049, -2), (key3049, 2), (key3098, 2), (key3049, 2)]

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

def rawRow1152 : Integer.Sparse Key := [(key3102, -6), (key3126, 2), (key3102, 2), (key3102, 2), (key3065, 6), (key3124, -2), (key3065, -2), (key3065, -2), (key3063, -2), (key3049, -2), (key3049, -2), (key3098, 2), (key3049, 2), (key3049, 2)]

def rawRow1153 : Integer.Sparse Key := [(key3126, -6), (key3102, 2), (key3102, 2), (key3102, 2), (key3124, 6), (key3065, -2), (key3065, -2), (key3065, -2), (key3098, -2), (key3098, -2), (key3098, -2), (key3063, 2), (key3063, 2), (key3063, 2)]

def rawRow1154 : Integer.Sparse Key := [(key1405, -1), (key1414, -1), (key1405, -1), (key1910, -1), (key1414, -1), (key1910, -1), (key1410, 2), (key1410, 2), (key1908, 2), (key1433, 1), (key1439, 1), (key1433, 1), (key1925, 1), (key1439, 1), (key1925, 1), (key1410, -1), (key1477, -1), (key1410, -1), (key1908, -1), (key1477, -1), (key1908, -1), (key1439, -2), (key1439, -2), (key1925, -2), (key1414, 1), (key1479, 1), (key1414, 1), (key1910, 1), (key1479, 1), (key1910, 1)]

def rawRow1155 : Integer.Sparse Key := [(key1414, -1), (key1405, -1), (key1910, -1), (key1405, -1), (key1910, -1), (key1414, -1), (key1410, 2), (key1908, 2), (key1410, 2), (key1439, 1), (key1433, 1), (key1925, 1), (key1433, 1), (key1925, 1), (key1439, 1), (key1477, -1), (key1410, -1), (key1908, -1), (key1410, -1), (key1908, -1), (key1477, -1), (key1439, -2), (key1925, -2), (key1439, -2), (key1479, 1), (key1414, 1), (key1910, 1), (key1414, 1), (key1910, 1), (key1479, 1)]

def rawRow1156 : Integer.Sparse Key := [(key1910, -1), (key1910, -1), (key1414, -1), (key1414, -1), (key1405, -1), (key1405, -1), (key1908, 2), (key1410, 2), (key1410, 2), (key1925, 1), (key1925, 1), (key1439, 1), (key1439, 1), (key1433, 1), (key1433, 1), (key1908, -1), (key1908, -1), (key1477, -1), (key1477, -1), (key1410, -1), (key1410, -1), (key1925, -2), (key1439, -2), (key1439, -2), (key1910, 1), (key1910, 1), (key1479, 1), (key1479, 1), (key1414, 1), (key1414, 1)]

def rawRow1157 : Integer.Sparse Key := [(key1410, -1), (key1414, -1), (key1410, -1), (key1588, -1), (key1414, -1), (key1588, -1), (key1405, 2), (key1405, 2), (key1582, 2), (key1477, 1), (key1479, 1), (key1477, 1), (key1688, 1), (key1479, 1), (key1688, 1), (key1405, -1), (key1433, -1), (key1405, -1), (key1582, -1), (key1433, -1), (key1582, -1), (key1479, -2), (key1479, -2), (key1688, -2), (key1414, 1), (key1439, 1), (key1414, 1), (key1588, 1), (key1439, 1), (key1588, 1)]

def rawRow1158 : Integer.Sparse Key := [(key1414, -1), (key1410, -1), (key1588, -1), (key1410, -1), (key1588, -1), (key1414, -1), (key1405, 2), (key1582, 2), (key1405, 2), (key1479, 1), (key1477, 1), (key1688, 1), (key1477, 1), (key1688, 1), (key1479, 1), (key1433, -1), (key1405, -1), (key1582, -1), (key1405, -1), (key1582, -1), (key1433, -1), (key1479, -2), (key1688, -2), (key1479, -2), (key1439, 1), (key1414, 1), (key1588, 1), (key1414, 1), (key1588, 1), (key1439, 1)]

def rawRow1159 : Integer.Sparse Key := [(key1588, -1), (key1588, -1), (key1414, -1), (key1414, -1), (key1410, -1), (key1410, -1), (key1582, 2), (key1405, 2), (key1405, 2), (key1688, 1), (key1688, 1), (key1479, 1), (key1479, 1), (key1477, 1), (key1477, 1), (key1582, -1), (key1582, -1), (key1433, -1), (key1433, -1), (key1405, -1), (key1405, -1), (key1688, -2), (key1479, -2), (key1479, -2), (key1588, 1), (key1588, 1), (key1439, 1), (key1439, 1), (key1414, 1), (key1414, 1)]

def rawRow1160 : Integer.Sparse Key := [(key1433, -1), (key1439, -1), (key1433, -1), (key1925, -1), (key1439, -1), (key1925, -1), (key1439, 2), (key1439, 2), (key1925, 2), (key1405, 1), (key1414, 1), (key1405, 1), (key1910, 1), (key1414, 1), (key1910, 1), (key1414, -1), (key1479, -1), (key1414, -1), (key1910, -1), (key1479, -1), (key1910, -1), (key1410, -2), (key1410, -2), (key1908, -2), (key1410, 1), (key1477, 1), (key1410, 1), (key1908, 1), (key1477, 1), (key1908, 1)]

def rawRow1161 : Integer.Sparse Key := [(key1439, -1), (key1433, -1), (key1925, -1), (key1433, -1), (key1925, -1), (key1439, -1), (key1439, 2), (key1925, 2), (key1439, 2), (key1414, 1), (key1405, 1), (key1910, 1), (key1405, 1), (key1910, 1), (key1414, 1), (key1479, -1), (key1414, -1), (key1910, -1), (key1414, -1), (key1910, -1), (key1479, -1), (key1410, -2), (key1908, -2), (key1410, -2), (key1477, 1), (key1410, 1), (key1908, 1), (key1410, 1), (key1908, 1), (key1477, 1)]

def rawRow1162 : Integer.Sparse Key := [(key1925, -1), (key1925, -1), (key1439, -1), (key1439, -1), (key1433, -1), (key1433, -1), (key1925, 2), (key1439, 2), (key1439, 2), (key1910, 1), (key1910, 1), (key1414, 1), (key1414, 1), (key1405, 1), (key1405, 1), (key1910, -1), (key1910, -1), (key1479, -1), (key1479, -1), (key1414, -1), (key1414, -1), (key1908, -2), (key1410, -2), (key1410, -2), (key1908, 1), (key1908, 1), (key1477, 1), (key1477, 1), (key1410, 1), (key1410, 1)]

def rawRow1163 : Integer.Sparse Key := [(key1439, -1), (key1439, -1), (key1439, -1), (key1439, -1), (key1439, -1), (key1439, -1), (key1433, 2), (key1433, 2), (key1433, 2), (key1479, 1), (key1479, 1), (key1479, 1), (key1479, 1), (key1479, 1), (key1479, 1), (key1405, -1), (key1405, -1), (key1405, -1), (key1405, -1), (key1405, -1), (key1405, -1), (key1477, -2), (key1477, -2), (key1477, -2), (key1410, 1), (key1410, 1), (key1410, 1), (key1410, 1), (key1410, 1), (key1410, 1)]

def rawRow1164 : Integer.Sparse Key := [(key1477, -1), (key1479, -1), (key1477, -1), (key1688, -1), (key1479, -1), (key1688, -1), (key1479, 2), (key1479, 2), (key1688, 2), (key1410, 1), (key1414, 1), (key1410, 1), (key1588, 1), (key1414, 1), (key1588, 1), (key1414, -1), (key1439, -1), (key1414, -1), (key1588, -1), (key1439, -1), (key1588, -1), (key1405, -2), (key1405, -2), (key1582, -2), (key1405, 1), (key1433, 1), (key1405, 1), (key1582, 1), (key1433, 1), (key1582, 1)]

def rawRow1165 : Integer.Sparse Key := [(key1479, -1), (key1477, -1), (key1688, -1), (key1477, -1), (key1688, -1), (key1479, -1), (key1479, 2), (key1688, 2), (key1479, 2), (key1414, 1), (key1410, 1), (key1588, 1), (key1410, 1), (key1588, 1), (key1414, 1), (key1439, -1), (key1414, -1), (key1588, -1), (key1414, -1), (key1588, -1), (key1439, -1), (key1405, -2), (key1582, -2), (key1405, -2), (key1433, 1), (key1405, 1), (key1582, 1), (key1405, 1), (key1582, 1), (key1433, 1)]

def rawRow1166 : Integer.Sparse Key := [(key1688, -1), (key1688, -1), (key1479, -1), (key1479, -1), (key1477, -1), (key1477, -1), (key1688, 2), (key1479, 2), (key1479, 2), (key1588, 1), (key1588, 1), (key1414, 1), (key1414, 1), (key1410, 1), (key1410, 1), (key1588, -1), (key1588, -1), (key1439, -1), (key1439, -1), (key1414, -1), (key1414, -1), (key1582, -2), (key1405, -2), (key1405, -2), (key1582, 1), (key1582, 1), (key1433, 1), (key1433, 1), (key1405, 1), (key1405, 1)]

def rawRow1167 : Integer.Sparse Key := [(key1479, -1), (key1479, -1), (key1479, -1), (key1479, -1), (key1479, -1), (key1479, -1), (key1477, 2), (key1477, 2), (key1477, 2), (key1439, 1), (key1439, 1), (key1439, 1), (key1439, 1), (key1439, 1), (key1439, 1), (key1410, -1), (key1410, -1), (key1410, -1), (key1410, -1), (key1410, -1), (key1410, -1), (key1433, -2), (key1433, -2), (key1433, -2), (key1405, 1), (key1405, 1), (key1405, 1), (key1405, 1), (key1405, 1), (key1405, 1)]

def rawRow1168 : Integer.Sparse Key := [(key3081, -2), (key3093, -2), (key3093, -2), (key3083, 2), (key3089, 2), (key3089, 2), (key3086, 2), (key3114, 2), (key3114, 2), (key3089, -6), (key3092, -2), (key3114, -2), (key3114, -2), (key3093, 6)]

def rawRow1169 : Integer.Sparse Key := [(key3093, -2), (key3081, -2), (key3093, -2), (key3089, 2), (key3083, 2), (key3089, 2), (key3114, 2), (key3086, 2), (key3114, 2), (key3089, -6), (key3114, -2), (key3092, -2), (key3114, -2), (key3093, 6)]

def rawRow1170 : Integer.Sparse Key := [(key3093, -2), (key3093, -2), (key3081, -2), (key3089, 2), (key3089, 2), (key3083, 2), (key3114, 2), (key3114, 2), (key3086, 2), (key3089, -6), (key3114, -2), (key3114, -2), (key3092, -2), (key3093, 6)]

def rawRow1171 : Integer.Sparse Key := [(key3083, -2), (key3089, -2), (key3089, -2), (key3081, 2), (key3086, 2), (key3086, 2), (key3089, 2), (key3114, 2), (key3114, 2), (key3086, -6), (key3093, -2), (key3114, -2), (key3114, -2), (key3092, 6)]

def rawRow1172 : Integer.Sparse Key := [(key3089, -2), (key3083, -2), (key3089, -2), (key3086, 2), (key3081, 2), (key3086, 2), (key3114, 2), (key3089, 2), (key3114, 2), (key3086, -6), (key3114, -2), (key3093, -2), (key3114, -2), (key3092, 6)]

def rawRow1173 : Integer.Sparse Key := [(key3089, -2), (key3089, -2), (key3083, -2), (key3086, 2), (key3086, 2), (key3081, 2), (key3114, 2), (key3114, 2), (key3089, 2), (key3086, -6), (key3114, -2), (key3114, -2), (key3093, -2), (key3092, 6)]

def rawRow1174 : Integer.Sparse Key := [(key3086, -2), (key3114, -2), (key3114, -2), (key3089, 2), (key3114, 2), (key3114, 2), (key3081, 2), (key3093, 2), (key3093, 2), (key3093, -6), (key3083, -2), (key3089, -2), (key3089, -2), (key3089, 6)]

def rawRow1175 : Integer.Sparse Key := [(key3114, -2), (key3086, -2), (key3114, -2), (key3114, 2), (key3089, 2), (key3114, 2), (key3093, 2), (key3081, 2), (key3093, 2), (key3093, -6), (key3089, -2), (key3083, -2), (key3089, -2), (key3089, 6)]

def rawRow1176 : Integer.Sparse Key := [(key3114, -2), (key3114, -2), (key3086, -2), (key3114, 2), (key3114, 2), (key3089, 2), (key3093, 2), (key3093, 2), (key3081, 2), (key3093, -6), (key3089, -2), (key3089, -2), (key3083, -2), (key3089, 6)]

def rawRow1177 : Integer.Sparse Key := [(key3089, -2), (key3089, -2), (key3089, -2), (key3086, 2), (key3086, 2), (key3086, 2), (key3093, 2), (key3093, 2), (key3093, 2), (key3081, -6), (key3089, -2), (key3089, -2), (key3089, -2), (key3083, 6)]

def rawRow1178 : Integer.Sparse Key := [(key3092, -2), (key3114, -2), (key3114, -2), (key3093, 2), (key3114, 2), (key3114, 2), (key3083, 2), (key3089, 2), (key3089, 2), (key3089, -6), (key3081, -2), (key3086, -2), (key3086, -2), (key3086, 6)]

def rawRow1179 : Integer.Sparse Key := [(key3114, -2), (key3092, -2), (key3114, -2), (key3114, 2), (key3093, 2), (key3114, 2), (key3089, 2), (key3083, 2), (key3089, 2), (key3089, -6), (key3086, -2), (key3081, -2), (key3086, -2), (key3086, 6)]

def rawRow1180 : Integer.Sparse Key := [(key3114, -2), (key3114, -2), (key3092, -2), (key3114, 2), (key3114, 2), (key3093, 2), (key3089, 2), (key3089, 2), (key3083, 2), (key3089, -6), (key3086, -2), (key3086, -2), (key3081, -2), (key3086, 6)]

def rawRow1181 : Integer.Sparse Key := [(key3093, -2), (key3093, -2), (key3093, -2), (key3092, 2), (key3092, 2), (key3092, 2), (key3089, 2), (key3089, 2), (key3089, 2), (key3083, -6), (key3086, -2), (key3086, -2), (key3086, -2), (key3081, 6)]

def rawRow1182 : Integer.Sparse Key := [(key1424, -2), (key1424, -2), (key1448, -2), (key1455, 1), (key1458, 1), (key1455, 1), (key1467, 1), (key1458, 1), (key1467, 1), (key1573, 2), (key1573, 2), (key1597, 2), (key1655, -1), (key1660, -1), (key1655, -1), (key1668, -1), (key1660, -1), (key1668, -1), (key1788, -1), (key1791, -1), (key1788, -1), (key1799, -1), (key1791, -1), (key1799, -1), (key1813, 1), (key1818, 1), (key1813, 1), (key1826, 1), (key1818, 1), (key1826, 1)]

def rawRow1183 : Integer.Sparse Key := [(key1424, -2), (key1448, -2), (key1424, -2), (key1458, 1), (key1455, 1), (key1467, 1), (key1455, 1), (key1467, 1), (key1458, 1), (key1573, 2), (key1597, 2), (key1573, 2), (key1660, -1), (key1655, -1), (key1668, -1), (key1655, -1), (key1668, -1), (key1660, -1), (key1791, -1), (key1788, -1), (key1799, -1), (key1788, -1), (key1799, -1), (key1791, -1), (key1818, 1), (key1813, 1), (key1826, 1), (key1813, 1), (key1826, 1), (key1818, 1)]

def rawRow1184 : Integer.Sparse Key := [(key1448, -2), (key1424, -2), (key1424, -2), (key1467, 1), (key1467, 1), (key1458, 1), (key1458, 1), (key1455, 1), (key1455, 1), (key1597, 2), (key1573, 2), (key1573, 2), (key1668, -1), (key1668, -1), (key1660, -1), (key1660, -1), (key1655, -1), (key1655, -1), (key1799, -1), (key1799, -1), (key1791, -1), (key1791, -1), (key1788, -1), (key1788, -1), (key1826, 1), (key1826, 1), (key1818, 1), (key1818, 1), (key1813, 1), (key1813, 1)]

def rawRow1185 : Integer.Sparse Key := [(key1391, -2), (key1455, -2), (key1467, -2), (key1391, 1), (key1398, 1), (key1424, 1), (key1448, 1), (key1458, 1), (key1467, 1), (key1546, 2), (key1655, 2), (key1668, 2), (key1546, -1), (key1560, -1), (key1573, -1), (key1597, -1), (key1660, -1), (key1668, -1), (key1772, -1), (key1775, -1), (key1813, -1), (key1826, -1), (key1840, -1), (key1845, -1), (key1772, 1), (key1781, 1), (key1788, 1), (key1799, 1), (key1842, 1), (key1845, 1)]

def rawRow1186 : Integer.Sparse Key := [(key1391, -2), (key1467, -2), (key1455, -2), (key1398, 1), (key1391, 1), (key1448, 1), (key1424, 1), (key1467, 1), (key1458, 1), (key1546, 2), (key1668, 2), (key1655, 2), (key1560, -1), (key1546, -1), (key1597, -1), (key1573, -1), (key1668, -1), (key1660, -1), (key1775, -1), (key1772, -1), (key1826, -1), (key1813, -1), (key1845, -1), (key1840, -1), (key1781, 1), (key1772, 1), (key1799, 1), (key1788, 1), (key1845, 1), (key1842, 1)]

def rawRow1187 : Integer.Sparse Key := [(key1455, -2), (key1391, -2), (key1467, -2), (key1424, 1), (key1458, 1), (key1391, 1), (key1467, 1), (key1398, 1), (key1448, 1), (key1655, 2), (key1546, 2), (key1668, 2), (key1573, -1), (key1660, -1), (key1546, -1), (key1668, -1), (key1560, -1), (key1597, -1), (key1813, -1), (key1840, -1), (key1772, -1), (key1845, -1), (key1775, -1), (key1826, -1), (key1788, 1), (key1842, 1), (key1772, 1), (key1845, 1), (key1781, 1), (key1799, 1)]

def rawRow1188 : Integer.Sparse Key := [(key1455, -2), (key1467, -2), (key1391, -2), (key1458, 1), (key1424, 1), (key1467, 1), (key1391, 1), (key1448, 1), (key1398, 1), (key1655, 2), (key1668, 2), (key1546, 2), (key1660, -1), (key1573, -1), (key1668, -1), (key1546, -1), (key1597, -1), (key1560, -1), (key1840, -1), (key1813, -1), (key1845, -1), (key1772, -1), (key1826, -1), (key1775, -1), (key1842, 1), (key1788, 1), (key1845, 1), (key1772, 1), (key1799, 1), (key1781, 1)]

def rawRow1189 : Integer.Sparse Key := [(key1467, -2), (key1391, -2), (key1455, -2), (key1448, 1), (key1467, 1), (key1398, 1), (key1458, 1), (key1391, 1), (key1424, 1), (key1668, 2), (key1546, 2), (key1655, 2), (key1597, -1), (key1668, -1), (key1560, -1), (key1660, -1), (key1546, -1), (key1573, -1), (key1826, -1), (key1845, -1), (key1775, -1), (key1840, -1), (key1772, -1), (key1813, -1), (key1799, 1), (key1845, 1), (key1781, 1), (key1842, 1), (key1772, 1), (key1788, 1)]

def rawRow1190 : Integer.Sparse Key := [(key1467, -2), (key1455, -2), (key1391, -2), (key1467, 1), (key1448, 1), (key1458, 1), (key1398, 1), (key1424, 1), (key1391, 1), (key1668, 2), (key1655, 2), (key1546, 2), (key1668, -1), (key1597, -1), (key1660, -1), (key1560, -1), (key1573, -1), (key1546, -1), (key1845, -1), (key1826, -1), (key1840, -1), (key1775, -1), (key1813, -1), (key1772, -1), (key1845, 1), (key1799, 1), (key1842, 1), (key1781, 1), (key1788, 1), (key1772, 1)]

def rawRow1191 : Integer.Sparse Key := [(key1573, -2), (key1573, -2), (key1597, -2), (key1788, 1), (key1791, 1), (key1788, 1), (key1799, 1), (key1791, 1), (key1799, 1), (key1424, 2), (key1424, 2), (key1448, 2), (key1813, -1), (key1818, -1), (key1813, -1), (key1826, -1), (key1818, -1), (key1826, -1), (key1455, -1), (key1458, -1), (key1455, -1), (key1467, -1), (key1458, -1), (key1467, -1), (key1655, 1), (key1660, 1), (key1655, 1), (key1668, 1), (key1660, 1), (key1668, 1)]

def rawRow1192 : Integer.Sparse Key := [(key1573, -2), (key1597, -2), (key1573, -2), (key1791, 1), (key1788, 1), (key1799, 1), (key1788, 1), (key1799, 1), (key1791, 1), (key1424, 2), (key1448, 2), (key1424, 2), (key1818, -1), (key1813, -1), (key1826, -1), (key1813, -1), (key1826, -1), (key1818, -1), (key1458, -1), (key1455, -1), (key1467, -1), (key1455, -1), (key1467, -1), (key1458, -1), (key1660, 1), (key1655, 1), (key1668, 1), (key1655, 1), (key1668, 1), (key1660, 1)]

def rawRow1193 : Integer.Sparse Key := [(key1597, -2), (key1573, -2), (key1573, -2), (key1799, 1), (key1799, 1), (key1791, 1), (key1791, 1), (key1788, 1), (key1788, 1), (key1448, 2), (key1424, 2), (key1424, 2), (key1826, -1), (key1826, -1), (key1818, -1), (key1818, -1), (key1813, -1), (key1813, -1), (key1467, -1), (key1467, -1), (key1458, -1), (key1458, -1), (key1455, -1), (key1455, -1), (key1668, 1), (key1668, 1), (key1660, 1), (key1660, 1), (key1655, 1), (key1655, 1)]

def rawRow1194 : Integer.Sparse Key := [(key1546, -2), (key1655, -2), (key1668, -2), (key1772, 1), (key1775, 1), (key1813, 1), (key1826, 1), (key1840, 1), (key1845, 1), (key1391, 2), (key1455, 2), (key1467, 2), (key1772, -1), (key1781, -1), (key1788, -1), (key1799, -1), (key1842, -1), (key1845, -1), (key1391, -1), (key1398, -1), (key1424, -1), (key1448, -1), (key1458, -1), (key1467, -1), (key1546, 1), (key1560, 1), (key1573, 1), (key1597, 1), (key1660, 1), (key1668, 1)]

def rawRow1195 : Integer.Sparse Key := [(key1546, -2), (key1668, -2), (key1655, -2), (key1775, 1), (key1772, 1), (key1826, 1), (key1813, 1), (key1845, 1), (key1840, 1), (key1391, 2), (key1467, 2), (key1455, 2), (key1781, -1), (key1772, -1), (key1799, -1), (key1788, -1), (key1845, -1), (key1842, -1), (key1398, -1), (key1391, -1), (key1448, -1), (key1424, -1), (key1467, -1), (key1458, -1), (key1560, 1), (key1546, 1), (key1597, 1), (key1573, 1), (key1668, 1), (key1660, 1)]

def rawRow1196 : Integer.Sparse Key := [(key1655, -2), (key1546, -2), (key1668, -2), (key1813, 1), (key1840, 1), (key1772, 1), (key1845, 1), (key1775, 1), (key1826, 1), (key1455, 2), (key1391, 2), (key1467, 2), (key1788, -1), (key1842, -1), (key1772, -1), (key1845, -1), (key1781, -1), (key1799, -1), (key1424, -1), (key1458, -1), (key1391, -1), (key1467, -1), (key1398, -1), (key1448, -1), (key1573, 1), (key1660, 1), (key1546, 1), (key1668, 1), (key1560, 1), (key1597, 1)]

def rawRow1197 : Integer.Sparse Key := [(key1655, -2), (key1668, -2), (key1546, -2), (key1840, 1), (key1813, 1), (key1845, 1), (key1772, 1), (key1826, 1), (key1775, 1), (key1455, 2), (key1467, 2), (key1391, 2), (key1842, -1), (key1788, -1), (key1845, -1), (key1772, -1), (key1799, -1), (key1781, -1), (key1458, -1), (key1424, -1), (key1467, -1), (key1391, -1), (key1448, -1), (key1398, -1), (key1660, 1), (key1573, 1), (key1668, 1), (key1546, 1), (key1597, 1), (key1560, 1)]

def rawRow1198 : Integer.Sparse Key := [(key1668, -2), (key1546, -2), (key1655, -2), (key1826, 1), (key1845, 1), (key1775, 1), (key1840, 1), (key1772, 1), (key1813, 1), (key1467, 2), (key1391, 2), (key1455, 2), (key1799, -1), (key1845, -1), (key1781, -1), (key1842, -1), (key1772, -1), (key1788, -1), (key1448, -1), (key1467, -1), (key1398, -1), (key1458, -1), (key1391, -1), (key1424, -1), (key1597, 1), (key1668, 1), (key1560, 1), (key1660, 1), (key1546, 1), (key1573, 1)]

def rawRow1199 : Integer.Sparse Key := [(key1668, -2), (key1655, -2), (key1546, -2), (key1845, 1), (key1826, 1), (key1840, 1), (key1775, 1), (key1813, 1), (key1772, 1), (key1467, 2), (key1455, 2), (key1391, 2), (key1845, -1), (key1799, -1), (key1842, -1), (key1781, -1), (key1788, -1), (key1772, -1), (key1467, -1), (key1448, -1), (key1458, -1), (key1398, -1), (key1424, -1), (key1391, -1), (key1668, 1), (key1597, 1), (key1660, 1), (key1560, 1), (key1573, 1), (key1546, 1)]

def rawRow1200 : Integer.Sparse Key := [(key238, -6), (key250, 2), (key250, 2), (key259, 2), (key304, 6), (key318, -2), (key318, -2), (key327, -2), (key387, -2), (key387, -2), (key396, -2), (key408, 2), (key408, 2), (key417, 2)]

def rawRow1201 : Integer.Sparse Key := [(key238, -6), (key250, 2), (key259, 2), (key250, 2), (key304, 6), (key318, -2), (key327, -2), (key318, -2), (key387, -2), (key396, -2), (key387, -2), (key408, 2), (key417, 2), (key408, 2)]

def rawRow1202 : Integer.Sparse Key := [(key238, -6), (key259, 2), (key250, 2), (key250, 2), (key304, 6), (key327, -2), (key318, -2), (key318, -2), (key396, -2), (key387, -2), (key387, -2), (key417, 2), (key408, 2), (key408, 2)]

def rawRow1203 : Integer.Sparse Key := [(key250, -6), (key238, 2), (key250, 2), (key259, 2), (key318, 6), (key304, -2), (key318, -2), (key327, -2), (key408, -2), (key437, -2), (key441, -2), (key387, 2), (key437, 2), (key449, 2)]

def rawRow1204 : Integer.Sparse Key := [(key250, -6), (key238, 2), (key259, 2), (key250, 2), (key318, 6), (key304, -2), (key327, -2), (key318, -2), (key408, -2), (key441, -2), (key437, -2), (key387, 2), (key449, 2), (key437, 2)]

def rawRow1205 : Integer.Sparse Key := [(key250, -6), (key250, 2), (key238, 2), (key259, 2), (key318, 6), (key318, -2), (key304, -2), (key327, -2), (key437, -2), (key408, -2), (key441, -2), (key437, 2), (key387, 2), (key449, 2)]

def rawRow1206 : Integer.Sparse Key := [(key250, -6), (key250, 2), (key259, 2), (key238, 2), (key318, 6), (key318, -2), (key327, -2), (key304, -2), (key437, -2), (key441, -2), (key408, -2), (key437, 2), (key449, 2), (key387, 2)]

def rawRow1207 : Integer.Sparse Key := [(key250, -6), (key259, 2), (key238, 2), (key250, 2), (key318, 6), (key327, -2), (key304, -2), (key318, -2), (key441, -2), (key408, -2), (key437, -2), (key449, 2), (key387, 2), (key437, 2)]

def rawRow1208 : Integer.Sparse Key := [(key250, -6), (key259, 2), (key250, 2), (key238, 2), (key318, 6), (key327, -2), (key318, -2), (key304, -2), (key441, -2), (key437, -2), (key408, -2), (key449, 2), (key437, 2), (key387, 2)]

def rawRow1209 : Integer.Sparse Key := [(key304, -6), (key387, 2), (key387, 2), (key396, 2), (key238, 6), (key408, -2), (key408, -2), (key417, -2), (key250, -2), (key250, -2), (key259, -2), (key318, 2), (key318, 2), (key327, 2)]

def rawRow1210 : Integer.Sparse Key := [(key304, -6), (key387, 2), (key396, 2), (key387, 2), (key238, 6), (key408, -2), (key417, -2), (key408, -2), (key250, -2), (key259, -2), (key250, -2), (key318, 2), (key327, 2), (key318, 2)]

def rawRow1211 : Integer.Sparse Key := [(key304, -6), (key396, 2), (key387, 2), (key387, 2), (key238, 6), (key417, -2), (key408, -2), (key408, -2), (key259, -2), (key250, -2), (key250, -2), (key327, 2), (key318, 2), (key318, 2)]

def rawRow1212 : Integer.Sparse Key := [(key318, -6), (key408, 2), (key437, 2), (key441, 2), (key250, 6), (key387, -2), (key437, -2), (key449, -2), (key238, -2), (key250, -2), (key259, -2), (key304, 2), (key318, 2), (key327, 2)]

def rawRow1213 : Integer.Sparse Key := [(key318, -6), (key408, 2), (key441, 2), (key437, 2), (key250, 6), (key387, -2), (key449, -2), (key437, -2), (key238, -2), (key259, -2), (key250, -2), (key304, 2), (key327, 2), (key318, 2)]

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

def rawRow1287 : Integer.Sparse Key := [(key445, -1), (key435, -1), (key661, -1), (key316, -1), (key660, -1), (key321, -1), (key453, 2), (key662, 2), (key331, 2), (key346, 1), (key316, 1), (key347, 1), (key302, 1), (key331, 1), (key307, 1), (key661, -1), (key657, -1), (key662, -1), (key655, -1), (key658, -1), (key656, -1), (key321, -2), (key331, -2), (key307, -2), (key445, 1), (key411, 1), (key453, 1), (key390, 1), (key421, 1), (key400, 1)]

def rawRow1288 : Integer.Sparse Key := [(key660, -1), (key661, -1), (key321, -1), (key445, -1), (key316, -1), (key435, -1), (key662, 2), (key331, 2), (key453, 2), (key331, 1), (key347, 1), (key307, 1), (key346, 1), (key302, 1), (key316, 1), (key658, -1), (key662, -1), (key656, -1), (key661, -1), (key655, -1), (key657, -1), (key331, -2), (key307, -2), (key321, -2), (key421, 1), (key453, 1), (key400, 1), (key445, 1), (key390, 1), (key411, 1)]

def rawRow1289 : Integer.Sparse Key := [(key661, -1), (key660, -1), (key445, -1), (key321, -1), (key435, -1), (key316, -1), (key662, 2), (key453, 2), (key331, 2), (key347, 1), (key331, 1), (key346, 1), (key307, 1), (key316, 1), (key302, 1), (key662, -1), (key658, -1), (key661, -1), (key656, -1), (key657, -1), (key655, -1), (key331, -2), (key321, -2), (key307, -2), (key453, 1), (key421, 1), (key445, 1), (key400, 1), (key411, 1), (key390, 1)]

def rawRow1290 : Integer.Sparse Key := [(key1433, -2), (key1439, -2), (key1439, -2), (key1477, 2), (key1479, 2), (key1479, 2), (key1582, 2), (key1588, 2), (key1588, 2), (key1688, -6), (key1908, -2), (key1910, -2), (key1910, -2), (key1925, 6)]

def rawRow1291 : Integer.Sparse Key := [(key1439, -2), (key1433, -2), (key1439, -2), (key1479, 2), (key1477, 2), (key1479, 2), (key1588, 2), (key1582, 2), (key1588, 2), (key1688, -6), (key1910, -2), (key1908, -2), (key1910, -2), (key1925, 6)]

def rawRow1292 : Integer.Sparse Key := [(key1439, -2), (key1439, -2), (key1433, -2), (key1479, 2), (key1479, 2), (key1477, 2), (key1588, 2), (key1588, 2), (key1582, 2), (key1688, -6), (key1910, -2), (key1910, -2), (key1908, -2), (key1925, 6)]

def rawRow1293 : Integer.Sparse Key := [(key1405, -2), (key1414, -2), (key1479, -2), (key1410, 2), (key1414, 2), (key1439, 2), (key1582, 2), (key1588, 2), (key1688, 2), (key1588, -6), (key1908, -2), (key1910, -2), (key1925, -2), (key1910, 6)]

def rawRow1294 : Integer.Sparse Key := [(key1414, -2), (key1405, -2), (key1479, -2), (key1414, 2), (key1410, 2), (key1439, 2), (key1588, 2), (key1582, 2), (key1688, 2), (key1588, -6), (key1910, -2), (key1908, -2), (key1925, -2), (key1910, 6)]

def rawRow1295 : Integer.Sparse Key := [(key1405, -2), (key1479, -2), (key1414, -2), (key1410, 2), (key1439, 2), (key1414, 2), (key1582, 2), (key1688, 2), (key1588, 2), (key1588, -6), (key1908, -2), (key1925, -2), (key1910, -2), (key1910, 6)]

def rawRow1296 : Integer.Sparse Key := [(key1479, -2), (key1405, -2), (key1414, -2), (key1439, 2), (key1410, 2), (key1414, 2), (key1688, 2), (key1582, 2), (key1588, 2), (key1588, -6), (key1925, -2), (key1908, -2), (key1910, -2), (key1910, 6)]

def rawRow1297 : Integer.Sparse Key := [(key1414, -2), (key1479, -2), (key1405, -2), (key1414, 2), (key1439, 2), (key1410, 2), (key1588, 2), (key1688, 2), (key1582, 2), (key1588, -6), (key1910, -2), (key1925, -2), (key1908, -2), (key1910, 6)]

def rawRow1298 : Integer.Sparse Key := [(key1479, -2), (key1414, -2), (key1405, -2), (key1439, 2), (key1414, 2), (key1410, 2), (key1688, 2), (key1588, 2), (key1582, 2), (key1588, -6), (key1925, -2), (key1910, -2), (key1908, -2), (key1910, 6)]

def rawRow1299 : Integer.Sparse Key := [(key1582, -2), (key1588, -2), (key1588, -2), (key1908, 2), (key1910, 2), (key1910, 2), (key1433, 2), (key1439, 2), (key1439, 2), (key1925, -6), (key1477, -2), (key1479, -2), (key1479, -2), (key1688, 6)]

end MUB6.Certificate.GramRows

end OAI
end


