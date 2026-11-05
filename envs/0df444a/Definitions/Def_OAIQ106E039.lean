-- Prove2me | Definitions.Def_OAIQ106E039
-- name    : OAIQ106E039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:00:37.280193+00:00
-- url     : https://prove2.me/theorems/e164f256-6eb3-4779-aa41-a4a1f8e52c48
-- title:
--   Definitions bundle OAIQ106E039 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2616 declarations of OpenAI's Lean: 2616 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow0`, `OAI.MUB6.Certificate.GramRows.rawRow1`, `OAI.MUB6.Certificate.GramRows.rawRow10`, `OAI.MUB6.Certificate.GramRows.rawRow100`, `OAI.MUB6.Certificate.GramRows.rawRow1000`, `OAI.MUB6.Certificate.GramRows.rawRow10000`, `OAI.MUB6.Certificate.GramRows.rawRow10001`, `OAI.MUB6.Certificate.GramRows.rawRow10002`, `OAI.MUB6.Certificate.GramRows.rawRow10003`, `OAI.MUB6.Certificate.GramRows.rawRow10004`, `OAI.MUB6.Certificate.GramRows.rawRow10005`, `OAI.MUB6.Certificate.GramRows.rawRow10006`, `OAI.MUB6.Certificate.GramRows.rawRow10007`, `OAI.MUB6.Certificate.GramRows.rawRow10008`, `OAI.MUB6.Certificate.GramRows.rawRow10009`, `OAI.MUB6.Certificate.GramRows.rawRow1001`, `OAI.MUB6.Certificate.GramRows.rawRow10010`, `OAI.MUB6.Certificate.GramRows.rawRow10011`, `OAI.MUB6.Certificate.GramRows.rawRow10012`, `OAI.MUB6.Certificate.GramRows.rawRow10013`, `OAI.MUB6.Certificate.GramRows.rawRow10014`, `OAI.MUB6.Certificate.GramRows.rawRow10015`, `OAI.MUB6.Certificate.GramRows.rawRow10016`, `OAI.MUB6.Certificate.GramRows.rawRow10017`, `OAI.MUB6.Certificate.GramRows.rawRow10018`, `OAI.MUB6.Certificate.GramRows.rawRow10019`, `OAI.MUB6.Certificate.GramRows.rawRow1002`, `OAI.MUB6.Certificate.GramRows.rawRow10020`, `OAI.MUB6.Certificate.GramRows.rawRow10021`, `OAI.MUB6.Certificate.GramRows.rawRow10022`, `OAI.MUB6.Certificate.GramRows.rawRow10023`, `OAI.MUB6.Certificate.GramRows.rawRow10024`, `OAI.MUB6.Certificate.GramRows.rawRow10025`, `OAI.MUB6.Certificate.GramRows.rawRow10026`, `OAI.MUB6.Certificate.GramRows.rawRow10027`, `OAI.MUB6.Certificate.GramRows.rawRow10028`, `OAI.MUB6.Certificate.GramRows.rawRow10029`, `OAI.MUB6.Certificate.GramRows.rawRow1003`, `OAI.MUB6.Certificate.GramRows.rawRow10030`, `OAI.MUB6.Certificate.GramRows.rawRow10031` and 2576 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block102`, `MutuallyUnbiased_GramRows_Block103`, `MutuallyUnbiased_GramRows_Block104`, `MutuallyUnbiased_GramRows_Block105`, `MutuallyUnbiased_GramRows_Block106`, `MutuallyUnbiased_GramRows_Block107`, `MutuallyUnbiased_GramRows_Block108`, `MutuallyUnbiased_GramRows_Block109`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block168`, `MutuallyUnbiased_GramRows_Block169`, `MutuallyUnbiased_GramRows_Block170`, `MutuallyUnbiased_GramRows_Block171`, `MutuallyUnbiased_GramRows_Block172`, `MutuallyUnbiased_GramRows_Block173`, `MutuallyUnbiased_GramRows_Block174`, `MutuallyUnbiased_GramRows_Block175`, `MutuallyUnbiased_GramRows_Block178`, `MutuallyUnbiased_GramRows_Block179`, `MutuallyUnbiased_GramRows_Block180`, `MutuallyUnbiased_GramRows_Block181`, `MutuallyUnbiased_GramRows_Block182`, `MutuallyUnbiased_GramRows_Block28`, `MutuallyUnbiased_GramRows_Block29`, `MutuallyUnbiased_GramRows_Block30`, `MutuallyUnbiased_GramRows_Block31`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E040` and `OAIQ106E041`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7_e`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8_e` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9_e`.
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

def rawRow0 : Integer.Sparse Key := [(key236, -1), (key239, -1), (key239, 2), (key248, 1), (key251, 1), (key251, -1), (key260, -1), (key267, -2), (key267, 1), (key271, 1), (key302, 1), (key305, 1), (key305, -2), (key316, -1), (key319, -1), (key319, 1), (key328, 1), (key335, 2), (key335, -1), (key340, -1), (key385, -1), (key388, -1), (key388, 1), (key397, 1), (key406, 1), (key409, 1), (key409, -1), (key418, -1), (key467, -1), (key469, -1), (key467, 1), (key475, 1), (key568, 2), (key568, -1), (key572, -1), (key578, -2), (key578, 1), (key583, 1), (key593, 1), (key595, 1), (key593, -1), (key601, -1)]

def rawRow1 : Integer.Sparse Key := [(key239, -1), (key236, -1), (key239, 2), (key251, 1), (key248, 1), (key260, -1), (key251, -1), (key267, -2), (key271, 1), (key267, 1), (key305, 1), (key302, 1), (key305, -2), (key319, -1), (key316, -1), (key328, 1), (key319, 1), (key335, 2), (key340, -1), (key335, -1), (key388, -1), (key385, -1), (key397, 1), (key388, 1), (key409, 1), (key406, 1), (key418, -1), (key409, -1), (key469, -1), (key467, -1), (key475, 1), (key467, 1), (key568, 2), (key572, -1), (key568, -1), (key578, -2), (key583, 1), (key578, 1), (key595, 1), (key593, 1), (key601, -1), (key593, -1)]

def rawRow10 : Integer.Sparse Key := [(key302, -1), (key305, -1), (key305, 2), (key316, 1), (key319, 1), (key319, -1), (key335, -1), (key328, -2), (key328, 1), (key340, 1), (key236, 1), (key239, 1), (key239, -2), (key406, -1), (key409, -1), (key409, 1), (key418, 1), (key578, 2), (key578, -1), (key583, -1), (key248, -1), (key251, -1), (key251, 1), (key260, 1), (key316, 1), (key319, 1), (key319, -1), (key328, -1), (key593, -1), (key595, -1), (key593, 1), (key601, 1), (key267, 2), (key267, -1), (key271, -1), (key335, -2), (key335, 1), (key340, 1), (key467, 1), (key469, 1), (key467, -1), (key475, -1)]

def rawRow11 : Integer.Sparse Key := [(key305, -1), (key302, -1), (key305, 2), (key319, 1), (key316, 1), (key335, -1), (key319, -1), (key328, -2), (key340, 1), (key328, 1), (key239, 1), (key236, 1), (key239, -2), (key409, -1), (key406, -1), (key418, 1), (key409, 1), (key578, 2), (key583, -1), (key578, -1), (key251, -1), (key248, -1), (key260, 1), (key251, 1), (key319, 1), (key316, 1), (key328, -1), (key319, -1), (key595, -1), (key593, -1), (key601, 1), (key593, 1), (key267, 2), (key271, -1), (key267, -1), (key335, -2), (key340, 1), (key335, 1), (key469, 1), (key467, 1), (key475, -1), (key467, -1)]

def rawRow100 : Integer.Sparse Key := [(key2739, -2), (key2749, 1), (key2751, 1), (key2675, 2), (key2730, -1), (key2751, -1), (key2672, -1), (key2675, -1), (key2707, 1), (key2739, 1), (key2952, 2), (key2962, -1), (key2964, -1), (key2620, -2), (key2833, 1), (key2964, 1), (key2617, 1), (key2620, 1), (key2810, -1), (key2833, -1), (key2730, -2), (key2985, 1), (key2994, 1), (key2643, 2), (key2978, -1), (key2994, -1), (key2633, -1), (key2643, -1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2906, -1), (key2915, -1), (key2655, -1), (key2656, -1), (key2899, 1), (key2915, 1), (key2650, 1), (key2656, 1), (key2739, -1), (key2751, -1)]

def rawRow101 : Integer.Sparse Key := [(key2739, -2), (key2751, 1), (key2749, 1), (key2675, 2), (key2751, -1), (key2730, -1), (key2675, -1), (key2672, -1), (key2739, 1), (key2707, 1), (key2952, 2), (key2964, -1), (key2962, -1), (key2620, -2), (key2964, 1), (key2833, 1), (key2620, 1), (key2617, 1), (key2833, -1), (key2810, -1), (key2730, -2), (key2994, 1), (key2985, 1), (key2643, 2), (key2994, -1), (key2978, -1), (key2643, -1), (key2633, -1), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2915, -1), (key2906, -1), (key2656, -1), (key2655, -1), (key2915, 1), (key2899, 1), (key2656, 1), (key2650, 1), (key2751, -1), (key2739, -1)]

def rawRow102 : Integer.Sparse Key := [(key2749, -2), (key2739, 1), (key2751, 1), (key2730, 2), (key2675, -1), (key2751, -1), (key2707, -1), (key2730, -1), (key2672, 1), (key2749, 1), (key2962, 2), (key2952, -1), (key2964, -1), (key2833, -2), (key2620, 1), (key2964, 1), (key2810, 1), (key2833, 1), (key2617, -1), (key2962, -1), (key2985, -2), (key2730, 1), (key2994, 1), (key2978, 2), (key2643, -1), (key2994, -1), (key2707, -1), (key2978, -1), (key2633, 1), (key2985, 1), (key2906, 1), (key3001, 1), (key2749, -1), (key3004, -1), (key2899, -1), (key2999, -1), (key2655, 1), (key3004, 1), (key2739, 1), (key2999, 1), (key2650, -1), (key3001, -1)]

def rawRow103 : Integer.Sparse Key := [(key2749, -2), (key2751, 1), (key2739, 1), (key2730, 2), (key2751, -1), (key2675, -1), (key2730, -1), (key2707, -1), (key2749, 1), (key2672, 1), (key2962, 2), (key2964, -1), (key2952, -1), (key2833, -2), (key2964, 1), (key2620, 1), (key2833, 1), (key2810, 1), (key2962, -1), (key2617, -1), (key2985, -2), (key2994, 1), (key2730, 1), (key2978, 2), (key2994, -1), (key2643, -1), (key2978, -1), (key2707, -1), (key2985, 1), (key2633, 1), (key3001, 1), (key2906, 1), (key3004, -1), (key2749, -1), (key2999, -1), (key2899, -1), (key3004, 1), (key2655, 1), (key2999, 1), (key2739, 1), (key3001, -1), (key2650, -1)]

def rawRow104 : Integer.Sparse Key := [(key2787, -2), (key2797, 1), (key2797, 1), (key2810, 2), (key2899, -1), (key2899, -1), (key2833, -1), (key2833, -1), (key2906, 1), (key2906, 1), (key2633, 2), (key2643, -1), (key2643, -1), (key2707, -2), (key2978, 1), (key2978, 1), (key2730, 1), (key2730, 1), (key2985, -1), (key2985, -1), (key2617, -2), (key2655, 1), (key2655, 1), (key2672, 2), (key2749, -1), (key2749, -1), (key2945, -1), (key2945, -1), (key2962, 1), (key2962, 1), (key2620, 1), (key2620, 1), (key2643, -1), (key2643, -1), (key2675, -1), (key2675, -1), (key2730, 1), (key2730, 1), (key2797, 1), (key2797, 1), (key2833, -1), (key2833, -1)]

def rawRow105 : Integer.Sparse Key := [(key2797, -2), (key2787, 1), (key2797, 1), (key2899, 2), (key2810, -1), (key2899, -1), (key2906, -1), (key2915, -1), (key2833, 1), (key2915, 1), (key2643, 2), (key2633, -1), (key2643, -1), (key2978, -2), (key2707, 1), (key2978, 1), (key2985, 1), (key2994, 1), (key2730, -1), (key2994, -1), (key2655, -2), (key2617, 1), (key2655, 1), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, -1), (key3004, -1), (key2945, 1), (key3004, 1), (key2643, 1), (key2656, 1), (key2620, -1), (key2656, -1), (key2730, -1), (key2751, -1), (key2675, 1), (key2751, 1), (key2833, 1), (key2915, 1), (key2797, -1), (key2915, -1)]

def rawRow106 : Integer.Sparse Key := [(key2797, -2), (key2797, 1), (key2787, 1), (key2899, 2), (key2899, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, 1), (key2833, 1), (key2643, 2), (key2643, -1), (key2633, -1), (key2978, -2), (key2978, 1), (key2707, 1), (key2994, 1), (key2985, 1), (key2994, -1), (key2730, -1), (key2655, -2), (key2655, 1), (key2617, 1), (key2749, 2), (key2749, -1), (key2672, -1), (key3004, -1), (key2962, -1), (key3004, 1), (key2945, 1), (key2656, 1), (key2643, 1), (key2656, -1), (key2620, -1), (key2751, -1), (key2730, -1), (key2751, 1), (key2675, 1), (key2915, 1), (key2833, 1), (key2915, -1), (key2797, -1)]

def rawRow107 : Integer.Sparse Key := [(key2810, -2), (key2833, 1), (key2833, 1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2899, 1), (key2899, 1), (key2707, 2), (key2730, -1), (key2730, -1), (key2633, -2), (key2985, 1), (key2985, 1), (key2643, 1), (key2643, 1), (key2978, -1), (key2978, -1), (key2672, -2), (key2749, 1), (key2749, 1), (key2617, 2), (key2962, -1), (key2962, -1), (key2655, -1), (key2655, -1), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2797, -1), (key2797, -1), (key2620, -1), (key2620, -1), (key2833, 1), (key2833, 1), (key2643, 1), (key2643, 1), (key2730, -1), (key2730, -1)]

def rawRow108 : Integer.Sparse Key := [(key2833, -2), (key2810, 1), (key2833, 1), (key2906, 2), (key2787, -1), (key2906, -1), (key2899, -1), (key2915, -1), (key2797, 1), (key2915, 1), (key2730, 2), (key2707, -1), (key2730, -1), (key2985, -2), (key2633, 1), (key2985, 1), (key2978, 1), (key2994, 1), (key2643, -1), (key2994, -1), (key2749, -2), (key2672, 1), (key2749, 1), (key2962, 2), (key2617, -1), (key2962, -1), (key2749, -1), (key3004, -1), (key2655, 1), (key3004, 1), (key2797, 1), (key2946, 1), (key2675, -1), (key2946, -1), (key2833, -1), (key2964, -1), (key2620, 1), (key2964, 1), (key2730, 1), (key2994, 1), (key2643, -1), (key2994, -1)]

def rawRow109 : Integer.Sparse Key := [(key2833, -2), (key2833, 1), (key2810, 1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2899, -1), (key2915, 1), (key2797, 1), (key2730, 2), (key2730, -1), (key2707, -1), (key2985, -2), (key2985, 1), (key2633, 1), (key2994, 1), (key2978, 1), (key2994, -1), (key2643, -1), (key2749, -2), (key2749, 1), (key2672, 1), (key2962, 2), (key2962, -1), (key2617, -1), (key3004, -1), (key2749, -1), (key3004, 1), (key2655, 1), (key2946, 1), (key2797, 1), (key2946, -1), (key2675, -1), (key2964, -1), (key2833, -1), (key2964, 1), (key2620, 1), (key2994, 1), (key2730, 1), (key2994, -1), (key2643, -1)]

def rawRow110 : Integer.Sparse Key := [(key2899, -2), (key2906, 1), (key2915, 1), (key2797, 2), (key2833, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, 1), (key2899, 1), (key2978, 2), (key2985, -1), (key2994, -1), (key2643, -2), (key2730, 1), (key2994, 1), (key2633, 1), (key2643, 1), (key2707, -1), (key2978, -1), (key2945, -2), (key2962, 1), (key3004, 1), (key2655, 2), (key2749, -1), (key3004, -1), (key2617, -1), (key2655, -1), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2833, -1), (key2915, -1), (key2643, -1), (key2656, -1), (key2797, 1), (key2915, 1), (key2620, 1), (key2656, 1), (key2675, -1), (key2751, -1)]

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

def rawRow10000 : Integer.Sparse Key := [(key167, -6), (key187, -6), (key165, -6), (key167, -6), (key94, 2), (key156, 2), (key88, 2), (key167, 2), (key187, 2), (key11, 2), (key156, 2), (key5, 2), (key88, 2), (key167, 2), (key11, 2), (key94, 2)]

def rawRow10001 : Integer.Sparse Key := [(key187, -6), (key167, -6), (key165, -6), (key167, -6), (key156, 2), (key94, 2), (key88, 2), (key187, 2), (key167, 2), (key156, 2), (key11, 2), (key88, 2), (key5, 2), (key167, 2), (key94, 2), (key11, 2)]

def rawRow10002 : Integer.Sparse Key := [(key167, -6), (key167, -6), (key187, -6), (key165, -6), (key167, 2), (key167, 2), (key187, 2), (key11, 2), (key11, 2), (key94, 2), (key94, 2), (key156, 2), (key156, 2), (key5, 2), (key88, 2), (key88, 2)]

def rawRow10003 : Integer.Sparse Key := [(key167, -6), (key187, -6), (key167, -6), (key165, -6), (key167, 2), (key187, 2), (key167, 2), (key94, 2), (key156, 2), (key11, 2), (key156, 2), (key11, 2), (key94, 2), (key88, 2), (key5, 2), (key88, 2)]

def rawRow10004 : Integer.Sparse Key := [(key187, -6), (key167, -6), (key167, -6), (key165, -6), (key187, 2), (key167, 2), (key167, 2), (key156, 2), (key94, 2), (key156, 2), (key11, 2), (key94, 2), (key11, 2), (key88, 2), (key88, 2), (key5, 2)]

def rawRow10005 : Integer.Sparse Key := [(key1002, -6), (key1115, -6), (key1151, -6), (key1151, -6), (key1002, 2), (key1016, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1072, 2), (key1124, 2), (key1124, 2), (key1151, 2), (key1151, 2), (key1167, 2), (key1167, 2)]

def rawRow10006 : Integer.Sparse Key := [(key1002, -6), (key1151, -6), (key1115, -6), (key1151, -6), (key1016, 2), (key1002, 2), (key1016, 2), (key1072, 2), (key1037, 2), (key1072, 2), (key1151, 2), (key1167, 2), (key1124, 2), (key1167, 2), (key1124, 2), (key1151, 2)]

def rawRow10007 : Integer.Sparse Key := [(key1002, -6), (key1151, -6), (key1151, -6), (key1115, -6), (key1016, 2), (key1016, 2), (key1002, 2), (key1072, 2), (key1072, 2), (key1037, 2), (key1167, 2), (key1151, 2), (key1167, 2), (key1124, 2), (key1151, 2), (key1124, 2)]

def rawRow10008 : Integer.Sparse Key := [(key1115, -6), (key1002, -6), (key1151, -6), (key1151, -6), (key1037, 2), (key1124, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1151, 2), (key1016, 2), (key1016, 2), (key1072, 2), (key1072, 2), (key1167, 2), (key1167, 2)]

def rawRow10009 : Integer.Sparse Key := [(key1115, -6), (key1151, -6), (key1002, -6), (key1151, -6), (key1124, 2), (key1037, 2), (key1124, 2), (key1151, 2), (key1002, 2), (key1151, 2), (key1072, 2), (key1167, 2), (key1016, 2), (key1167, 2), (key1016, 2), (key1072, 2)]

def rawRow10010 : Integer.Sparse Key := [(key1115, -6), (key1151, -6), (key1151, -6), (key1002, -6), (key1124, 2), (key1124, 2), (key1037, 2), (key1151, 2), (key1151, 2), (key1002, 2), (key1167, 2), (key1072, 2), (key1167, 2), (key1016, 2), (key1072, 2), (key1016, 2)]

def rawRow10011 : Integer.Sparse Key := [(key1151, -6), (key1002, -6), (key1115, -6), (key1151, -6), (key1072, 2), (key1151, 2), (key1167, 2), (key1016, 2), (key1124, 2), (key1167, 2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

def rawRow10012 : Integer.Sparse Key := [(key1151, -6), (key1002, -6), (key1151, -6), (key1115, -6), (key1072, 2), (key1167, 2), (key1151, 2), (key1016, 2), (key1167, 2), (key1124, 2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

def rawRow10013 : Integer.Sparse Key := [(key1151, -6), (key1115, -6), (key1002, -6), (key1151, -6), (key1151, 2), (key1072, 2), (key1167, 2), (key1124, 2), (key1016, 2), (key1167, 2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

def rawRow10014 : Integer.Sparse Key := [(key1151, -6), (key1115, -6), (key1151, -6), (key1002, -6), (key1151, 2), (key1167, 2), (key1072, 2), (key1124, 2), (key1167, 2), (key1016, 2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

def rawRow10015 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1002, -6), (key1115, -6), (key1167, 2), (key1072, 2), (key1151, 2), (key1167, 2), (key1016, 2), (key1124, 2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

def rawRow10016 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1115, -6), (key1002, -6), (key1167, 2), (key1151, 2), (key1072, 2), (key1167, 2), (key1124, 2), (key1016, 2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

def rawRow10017 : Integer.Sparse Key := [(key1016, -6), (key1124, -6), (key1124, -6), (key1167, -6), (key1002, 2), (key1002, 2), (key1016, 2), (key1037, 2), (key1037, 2), (key1072, 2), (key1115, 2), (key1124, 2), (key1115, 2), (key1151, 2), (key1124, 2), (key1151, 2)]

def rawRow10018 : Integer.Sparse Key := [(key1016, -6), (key1124, -6), (key1167, -6), (key1124, -6), (key1002, 2), (key1016, 2), (key1002, 2), (key1037, 2), (key1072, 2), (key1037, 2), (key1124, 2), (key1115, 2), (key1151, 2), (key1115, 2), (key1151, 2), (key1124, 2)]

def rawRow10019 : Integer.Sparse Key := [(key1016, -6), (key1167, -6), (key1124, -6), (key1124, -6), (key1016, 2), (key1002, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1037, 2), (key1151, 2), (key1151, 2), (key1124, 2), (key1124, 2), (key1115, 2), (key1115, 2)]

def rawRow10020 : Integer.Sparse Key := [(key1124, -6), (key1016, -6), (key1124, -6), (key1167, -6), (key1037, 2), (key1115, 2), (key1124, 2), (key1002, 2), (key1115, 2), (key1151, 2), (key1002, 2), (key1016, 2), (key1037, 2), (key1072, 2), (key1124, 2), (key1151, 2)]

def rawRow10021 : Integer.Sparse Key := [(key1124, -6), (key1016, -6), (key1167, -6), (key1124, -6), (key1037, 2), (key1124, 2), (key1115, 2), (key1002, 2), (key1151, 2), (key1115, 2), (key1016, 2), (key1002, 2), (key1072, 2), (key1037, 2), (key1151, 2), (key1124, 2)]

def rawRow10022 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1016, -6), (key1167, -6), (key1115, 2), (key1037, 2), (key1124, 2), (key1115, 2), (key1002, 2), (key1151, 2), (key1037, 2), (key1124, 2), (key1002, 2), (key1151, 2), (key1016, 2), (key1072, 2)]

def rawRow10023 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1167, -6), (key1016, -6), (key1115, 2), (key1124, 2), (key1037, 2), (key1115, 2), (key1151, 2), (key1002, 2), (key1124, 2), (key1037, 2), (key1151, 2), (key1002, 2), (key1072, 2), (key1016, 2)]

def rawRow10024 : Integer.Sparse Key := [(key1124, -6), (key1167, -6), (key1016, -6), (key1124, -6), (key1124, 2), (key1037, 2), (key1115, 2), (key1151, 2), (key1002, 2), (key1115, 2), (key1072, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1002, 2), (key1037, 2)]

def rawRow10025 : Integer.Sparse Key := [(key1124, -6), (key1167, -6), (key1124, -6), (key1016, -6), (key1124, 2), (key1115, 2), (key1037, 2), (key1151, 2), (key1115, 2), (key1002, 2), (key1151, 2), (key1072, 2), (key1124, 2), (key1016, 2), (key1037, 2), (key1002, 2)]

def rawRow10026 : Integer.Sparse Key := [(key1167, -6), (key1016, -6), (key1124, -6), (key1124, -6), (key1072, 2), (key1151, 2), (key1151, 2), (key1016, 2), (key1124, 2), (key1124, 2), (key1002, 2), (key1002, 2), (key1037, 2), (key1037, 2), (key1115, 2), (key1115, 2)]

def rawRow10027 : Integer.Sparse Key := [(key1167, -6), (key1124, -6), (key1016, -6), (key1124, -6), (key1151, 2), (key1072, 2), (key1151, 2), (key1124, 2), (key1016, 2), (key1124, 2), (key1037, 2), (key1115, 2), (key1002, 2), (key1115, 2), (key1002, 2), (key1037, 2)]

def rawRow10028 : Integer.Sparse Key := [(key1167, -6), (key1124, -6), (key1124, -6), (key1016, -6), (key1151, 2), (key1151, 2), (key1072, 2), (key1124, 2), (key1124, 2), (key1016, 2), (key1115, 2), (key1037, 2), (key1115, 2), (key1002, 2), (key1037, 2), (key1002, 2)]

def rawRow10029 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1101, -6), (key1229, -6), (key981, 2), (key981, 2), (key987, 2), (key1095, 2), (key1095, 2), (key1166, 2), (key1166, 2), (key1173, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key1246, 2)]

def rawRow10030 : Integer.Sparse Key := [(key1095, -6), (key1101, -6), (key1095, -6), (key1229, -6), (key981, 2), (key987, 2), (key981, 2), (key1166, 2), (key1173, 2), (key1095, 2), (key1173, 2), (key1095, 2), (key1166, 2), (key1246, 2), (key1229, 2), (key1246, 2)]

def rawRow10031 : Integer.Sparse Key := [(key1101, -6), (key1095, -6), (key1095, -6), (key1229, -6), (key987, 2), (key981, 2), (key981, 2), (key1173, 2), (key1166, 2), (key1173, 2), (key1095, 2), (key1166, 2), (key1095, 2), (key1246, 2), (key1246, 2), (key1229, 2)]

def rawRow10032 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1229, -6), (key1101, -6), (key1095, 2), (key1095, 2), (key1229, 2), (key981, 2), (key981, 2), (key1166, 2), (key1166, 2), (key1246, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1173, 2)]

def rawRow10033 : Integer.Sparse Key := [(key1095, -6), (key1229, -6), (key1095, -6), (key1101, -6), (key1095, 2), (key1229, 2), (key1095, 2), (key1166, 2), (key1246, 2), (key981, 2), (key1246, 2), (key981, 2), (key1166, 2), (key1173, 2), (key987, 2), (key1173, 2)]

def rawRow10034 : Integer.Sparse Key := [(key1229, -6), (key1095, -6), (key1095, -6), (key1101, -6), (key1229, 2), (key1095, 2), (key1095, 2), (key1246, 2), (key1166, 2), (key1246, 2), (key981, 2), (key1166, 2), (key981, 2), (key1173, 2), (key1173, 2), (key987, 2)]

def rawRow10035 : Integer.Sparse Key := [(key1095, -6), (key1101, -6), (key1229, -6), (key1095, -6), (key1166, 2), (key1173, 2), (key1246, 2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key981, 2), (key1095, 2), (key1166, 2)]

def rawRow10036 : Integer.Sparse Key := [(key1101, -6), (key1095, -6), (key1229, -6), (key1095, -6), (key1173, 2), (key1166, 2), (key1246, 2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key981, 2), (key1166, 2), (key1095, 2)]

def rawRow10037 : Integer.Sparse Key := [(key1095, -6), (key1229, -6), (key1101, -6), (key1095, -6), (key1166, 2), (key1246, 2), (key1173, 2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1095, 2), (key981, 2), (key1166, 2)]

def rawRow10038 : Integer.Sparse Key := [(key1229, -6), (key1095, -6), (key1101, -6), (key1095, -6), (key1246, 2), (key1166, 2), (key1173, 2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1095, 2), (key1166, 2), (key981, 2)]

def rawRow10039 : Integer.Sparse Key := [(key1101, -6), (key1229, -6), (key1095, -6), (key1095, -6), (key1173, 2), (key1246, 2), (key1166, 2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1166, 2), (key981, 2), (key1095, 2)]

def rawRow10040 : Integer.Sparse Key := [(key1229, -6), (key1101, -6), (key1095, -6), (key1095, -6), (key1246, 2), (key1173, 2), (key1166, 2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1166, 2), (key1095, 2), (key981, 2)]

def rawRow10041 : Integer.Sparse Key := [(key1166, -6), (key1173, -6), (key1173, -6), (key1246, -6), (key981, 2), (key987, 2), (key987, 2), (key1095, 2), (key1101, 2), (key1095, 2), (key1173, 2), (key1101, 2), (key1173, 2), (key1229, 2), (key1229, 2), (key1246, 2)]

def rawRow10042 : Integer.Sparse Key := [(key1173, -6), (key1166, -6), (key1173, -6), (key1246, -6), (key987, 2), (key981, 2), (key987, 2), (key1101, 2), (key1095, 2), (key1173, 2), (key1095, 2), (key1173, 2), (key1101, 2), (key1229, 2), (key1246, 2), (key1229, 2)]

def rawRow10043 : Integer.Sparse Key := [(key1173, -6), (key1173, -6), (key1166, -6), (key1246, -6), (key987, 2), (key987, 2), (key981, 2), (key1173, 2), (key1173, 2), (key1101, 2), (key1101, 2), (key1095, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key1229, 2)]

def rawRow10044 : Integer.Sparse Key := [(key1166, -6), (key1173, -6), (key1246, -6), (key1173, -6), (key1095, 2), (key1101, 2), (key1229, 2), (key981, 2), (key987, 2), (key1095, 2), (key1173, 2), (key1229, 2), (key1246, 2), (key987, 2), (key1101, 2), (key1173, 2)]

def rawRow10045 : Integer.Sparse Key := [(key1173, -6), (key1166, -6), (key1246, -6), (key1173, -6), (key1101, 2), (key1095, 2), (key1229, 2), (key987, 2), (key981, 2), (key1173, 2), (key1095, 2), (key1246, 2), (key1229, 2), (key987, 2), (key1173, 2), (key1101, 2)]

def rawRow10046 : Integer.Sparse Key := [(key1166, -6), (key1246, -6), (key1173, -6), (key1173, -6), (key1095, 2), (key1229, 2), (key1101, 2), (key1095, 2), (key1229, 2), (key981, 2), (key1246, 2), (key987, 2), (key1173, 2), (key1101, 2), (key987, 2), (key1173, 2)]

def rawRow10047 : Integer.Sparse Key := [(key1246, -6), (key1166, -6), (key1173, -6), (key1173, -6), (key1229, 2), (key1095, 2), (key1101, 2), (key1229, 2), (key1095, 2), (key1246, 2), (key981, 2), (key1173, 2), (key987, 2), (key1101, 2), (key1173, 2), (key987, 2)]

def rawRow10048 : Integer.Sparse Key := [(key1173, -6), (key1246, -6), (key1166, -6), (key1173, -6), (key1101, 2), (key1229, 2), (key1095, 2), (key1173, 2), (key1246, 2), (key987, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1173, 2), (key987, 2), (key1101, 2)]

def rawRow10049 : Integer.Sparse Key := [(key1246, -6), (key1173, -6), (key1166, -6), (key1173, -6), (key1229, 2), (key1101, 2), (key1095, 2), (key1246, 2), (key1173, 2), (key1229, 2), (key987, 2), (key1095, 2), (key981, 2), (key1173, 2), (key1101, 2), (key987, 2)]

def rawRow10050 : Integer.Sparse Key := [(key1173, -6), (key1173, -6), (key1246, -6), (key1166, -6), (key1173, 2), (key1173, 2), (key1246, 2), (key987, 2), (key987, 2), (key1101, 2), (key1101, 2), (key1229, 2), (key1229, 2), (key981, 2), (key1095, 2), (key1095, 2)]

def rawRow10051 : Integer.Sparse Key := [(key1173, -6), (key1246, -6), (key1173, -6), (key1166, -6), (key1173, 2), (key1246, 2), (key1173, 2), (key1101, 2), (key1229, 2), (key987, 2), (key1229, 2), (key987, 2), (key1101, 2), (key1095, 2), (key981, 2), (key1095, 2)]

def rawRow10052 : Integer.Sparse Key := [(key1246, -6), (key1173, -6), (key1173, -6), (key1166, -6), (key1246, 2), (key1173, 2), (key1173, 2), (key1229, 2), (key1101, 2), (key1229, 2), (key987, 2), (key1101, 2), (key987, 2), (key1095, 2), (key1095, 2), (key981, 2)]

def rawRow10053 : Integer.Sparse Key := [(key1003, -2), (key1003, -2), (key1009, -2), (key1116, -2), (key1116, -2), (key1152, -2), (key1152, -2), (key1159, -2), (key1159, -2), (key1233, -2), (key1243, -2), (key1243, -2), (key1003, 1), (key1003, 1), (key1017, 1), (key1017, 1), (key1022, 1), (key1022, 1), (key1038, 1), (key1038, 1), (key1073, 1), (key1073, 1), (key1080, 1), (key1080, 1), (key1125, 1), (key1125, 1), (key1152, 1), (key1152, 1), (key1174, 1), (key1174, 1), (key1236, 1), (key1236, 1), (key1243, 1), (key1243, 1), (key1247, 1), (key1247, 1)]

def rawRow10054 : Integer.Sparse Key := [(key1003, -2), (key1009, -2), (key1003, -2), (key1152, -2), (key1159, -2), (key1116, -2), (key1159, -2), (key1116, -2), (key1152, -2), (key1243, -2), (key1233, -2), (key1243, -2), (key1017, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1247, 1), (key1236, 1), (key1243, 1)]

def rawRow10055 : Integer.Sparse Key := [(key1009, -2), (key1003, -2), (key1003, -2), (key1159, -2), (key1152, -2), (key1159, -2), (key1116, -2), (key1152, -2), (key1116, -2), (key1243, -2), (key1243, -2), (key1233, -2), (key1022, 1), (key1017, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1003, 1), (key1080, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1038, 1), (key1174, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1125, 1), (key1247, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1243, 1), (key1236, 1)]

def rawRow10056 : Integer.Sparse Key := [(key1116, -2), (key1116, -2), (key1233, -2), (key1003, -2), (key1003, -2), (key1152, -2), (key1152, -2), (key1243, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1159, -2), (key1038, 1), (key1038, 1), (key1125, 1), (key1125, 1), (key1236, 1), (key1236, 1), (key1003, 1), (key1003, 1), (key1152, 1), (key1152, 1), (key1243, 1), (key1243, 1), (key1017, 1), (key1017, 1), (key1073, 1), (key1073, 1), (key1247, 1), (key1247, 1), (key1022, 1), (key1022, 1), (key1080, 1), (key1080, 1), (key1174, 1), (key1174, 1)]

def rawRow10057 : Integer.Sparse Key := [(key1116, -2), (key1233, -2), (key1116, -2), (key1152, -2), (key1243, -2), (key1003, -2), (key1243, -2), (key1003, -2), (key1152, -2), (key1159, -2), (key1009, -2), (key1159, -2), (key1125, 1), (key1236, 1), (key1038, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1174, 1), (key1022, 1), (key1080, 1)]

def rawRow10058 : Integer.Sparse Key := [(key1233, -2), (key1116, -2), (key1116, -2), (key1243, -2), (key1152, -2), (key1243, -2), (key1003, -2), (key1152, -2), (key1003, -2), (key1159, -2), (key1159, -2), (key1009, -2), (key1236, 1), (key1125, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1038, 1), (key1243, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1003, 1), (key1247, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1017, 1), (key1174, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1080, 1), (key1022, 1)]

def rawRow10059 : Integer.Sparse Key := [(key1152, -2), (key1159, -2), (key1243, -2), (key1003, -2), (key1009, -2), (key1116, -2), (key1159, -2), (key1233, -2), (key1243, -2), (key1003, -2), (key1116, -2), (key1152, -2), (key1073, 1), (key1080, 1), (key1152, 1), (key1174, 1), (key1243, 1), (key1247, 1), (key1017, 1), (key1022, 1), (key1125, 1), (key1174, 1), (key1236, 1), (key1247, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1003, 1), (key1017, 1), (key1038, 1), (key1073, 1), (key1125, 1), (key1152, 1)]

def rawRow10060 : Integer.Sparse Key := [(key1159, -2), (key1152, -2), (key1243, -2), (key1009, -2), (key1003, -2), (key1159, -2), (key1116, -2), (key1243, -2), (key1233, -2), (key1003, -2), (key1152, -2), (key1116, -2), (key1080, 1), (key1073, 1), (key1174, 1), (key1152, 1), (key1247, 1), (key1243, 1), (key1022, 1), (key1017, 1), (key1174, 1), (key1125, 1), (key1247, 1), (key1236, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1017, 1), (key1003, 1), (key1073, 1), (key1038, 1), (key1152, 1), (key1125, 1)]

def rawRow10061 : Integer.Sparse Key := [(key1152, -2), (key1243, -2), (key1159, -2), (key1116, -2), (key1233, -2), (key1003, -2), (key1243, -2), (key1009, -2), (key1159, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1152, 1), (key1243, 1), (key1073, 1), (key1247, 1), (key1080, 1), (key1174, 1), (key1125, 1), (key1236, 1), (key1017, 1), (key1247, 1), (key1022, 1), (key1174, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1038, 1), (key1125, 1), (key1003, 1), (key1152, 1), (key1017, 1), (key1073, 1)]

def rawRow10062 : Integer.Sparse Key := [(key1243, -2), (key1152, -2), (key1159, -2), (key1233, -2), (key1116, -2), (key1243, -2), (key1003, -2), (key1159, -2), (key1009, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1243, 1), (key1152, 1), (key1247, 1), (key1073, 1), (key1174, 1), (key1080, 1), (key1236, 1), (key1125, 1), (key1247, 1), (key1017, 1), (key1174, 1), (key1022, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1125, 1), (key1038, 1), (key1152, 1), (key1003, 1), (key1073, 1), (key1017, 1)]

def rawRow10063 : Integer.Sparse Key := [(key1159, -2), (key1243, -2), (key1152, -2), (key1159, -2), (key1243, -2), (key1009, -2), (key1233, -2), (key1003, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1174, 1), (key1247, 1), (key1080, 1), (key1243, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1247, 1), (key1022, 1), (key1236, 1), (key1017, 1), (key1125, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1017, 1), (key1125, 1), (key1003, 1), (key1038, 1)]

def rawRow10064 : Integer.Sparse Key := [(key1243, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1159, -2), (key1233, -2), (key1009, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1116, -2), (key1003, -2), (key1247, 1), (key1174, 1), (key1243, 1), (key1080, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1174, 1), (key1236, 1), (key1022, 1), (key1125, 1), (key1017, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1125, 1), (key1017, 1), (key1038, 1), (key1003, 1)]

def rawRow10065 : Integer.Sparse Key := [(key1017, -2), (key1022, -2), (key1022, -2), (key1125, -2), (key1130, -2), (key1125, -2), (key1174, -2), (key1130, -2), (key1174, -2), (key1236, -2), (key1236, -2), (key1247, -2), (key1003, 1), (key1009, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1022, 1), (key1038, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1080, 1), (key1116, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1159, 1), (key1233, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1236, 1), (key1243, 1)]

def rawRow10066 : Integer.Sparse Key := [(key1022, -2), (key1017, -2), (key1022, -2), (key1130, -2), (key1125, -2), (key1174, -2), (key1125, -2), (key1174, -2), (key1130, -2), (key1236, -2), (key1247, -2), (key1236, -2), (key1009, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1233, 1), (key1243, 1), (key1236, 1)]

def rawRow10067 : Integer.Sparse Key := [(key1022, -2), (key1022, -2), (key1017, -2), (key1174, -2), (key1174, -2), (key1130, -2), (key1130, -2), (key1125, -2), (key1125, -2), (key1247, -2), (key1236, -2), (key1236, -2), (key1022, 1), (key1022, 1), (key1009, 1), (key1009, 1), (key1003, 1), (key1003, 1), (key1080, 1), (key1080, 1), (key1044, 1), (key1044, 1), (key1038, 1), (key1038, 1), (key1159, 1), (key1159, 1), (key1130, 1), (key1130, 1), (key1116, 1), (key1116, 1), (key1243, 1), (key1243, 1), (key1236, 1), (key1236, 1), (key1233, 1), (key1233, 1)]

def rawRow10068 : Integer.Sparse Key := [(key1125, -2), (key1130, -2), (key1236, -2), (key1017, -2), (key1022, -2), (key1125, -2), (key1174, -2), (key1236, -2), (key1247, -2), (key1022, -2), (key1130, -2), (key1174, -2), (key1038, 1), (key1044, 1), (key1116, 1), (key1130, 1), (key1233, 1), (key1236, 1), (key1003, 1), (key1009, 1), (key1116, 1), (key1159, 1), (key1233, 1), (key1243, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1009, 1), (key1022, 1), (key1044, 1), (key1080, 1), (key1130, 1), (key1159, 1)]

def rawRow10069 : Integer.Sparse Key := [(key1130, -2), (key1125, -2), (key1236, -2), (key1022, -2), (key1017, -2), (key1174, -2), (key1125, -2), (key1247, -2), (key1236, -2), (key1022, -2), (key1174, -2), (key1130, -2), (key1044, 1), (key1038, 1), (key1130, 1), (key1116, 1), (key1236, 1), (key1233, 1), (key1009, 1), (key1003, 1), (key1159, 1), (key1116, 1), (key1243, 1), (key1233, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1022, 1), (key1009, 1), (key1080, 1), (key1044, 1), (key1159, 1), (key1130, 1)]

def rawRow10070 : Integer.Sparse Key := [(key1125, -2), (key1236, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1017, -2), (key1247, -2), (key1022, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1174, -2), (key1116, 1), (key1233, 1), (key1038, 1), (key1236, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1233, 1), (key1003, 1), (key1243, 1), (key1009, 1), (key1159, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1009, 1), (key1159, 1), (key1022, 1), (key1080, 1)]

def rawRow10071 : Integer.Sparse Key := [(key1236, -2), (key1125, -2), (key1130, -2), (key1236, -2), (key1125, -2), (key1247, -2), (key1017, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1233, 1), (key1116, 1), (key1236, 1), (key1038, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1116, 1), (key1243, 1), (key1003, 1), (key1159, 1), (key1009, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1159, 1), (key1009, 1), (key1080, 1), (key1022, 1)]

def rawRow10072 : Integer.Sparse Key := [(key1130, -2), (key1236, -2), (key1125, -2), (key1174, -2), (key1247, -2), (key1022, -2), (key1236, -2), (key1017, -2), (key1125, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1130, 1), (key1236, 1), (key1044, 1), (key1233, 1), (key1038, 1), (key1116, 1), (key1159, 1), (key1243, 1), (key1009, 1), (key1233, 1), (key1003, 1), (key1116, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1080, 1), (key1159, 1), (key1022, 1), (key1130, 1), (key1009, 1), (key1044, 1)]

def rawRow10073 : Integer.Sparse Key := [(key1236, -2), (key1130, -2), (key1125, -2), (key1247, -2), (key1174, -2), (key1236, -2), (key1022, -2), (key1125, -2), (key1017, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1236, 1), (key1130, 1), (key1233, 1), (key1044, 1), (key1116, 1), (key1038, 1), (key1243, 1), (key1159, 1), (key1233, 1), (key1009, 1), (key1116, 1), (key1003, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1159, 1), (key1080, 1), (key1130, 1), (key1022, 1), (key1044, 1), (key1009, 1)]

def rawRow10074 : Integer.Sparse Key := [(key1174, -2), (key1174, -2), (key1247, -2), (key1022, -2), (key1022, -2), (key1130, -2), (key1130, -2), (key1236, -2), (key1236, -2), (key1017, -2), (key1125, -2), (key1125, -2), (key1080, 1), (key1080, 1), (key1159, 1), (key1159, 1), (key1243, 1), (key1243, 1), (key1022, 1), (key1022, 1), (key1130, 1), (key1130, 1), (key1236, 1), (key1236, 1), (key1009, 1), (key1009, 1), (key1044, 1), (key1044, 1), (key1233, 1), (key1233, 1), (key1003, 1), (key1003, 1), (key1038, 1), (key1038, 1), (key1116, 1), (key1116, 1)]

def rawRow10075 : Integer.Sparse Key := [(key1174, -2), (key1247, -2), (key1174, -2), (key1130, -2), (key1236, -2), (key1022, -2), (key1236, -2), (key1022, -2), (key1130, -2), (key1125, -2), (key1017, -2), (key1125, -2), (key1159, 1), (key1243, 1), (key1080, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1116, 1), (key1003, 1), (key1038, 1)]

def rawRow10076 : Integer.Sparse Key := [(key1247, -2), (key1174, -2), (key1174, -2), (key1236, -2), (key1130, -2), (key1236, -2), (key1022, -2), (key1130, -2), (key1022, -2), (key1125, -2), (key1125, -2), (key1017, -2), (key1243, 1), (key1159, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1080, 1), (key1236, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1022, 1), (key1233, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1009, 1), (key1116, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1038, 1), (key1003, 1)]

def rawRow10077 : Integer.Sparse Key := [(key1094, -24), (key980, 6), (key1094, 6), (key1165, 6), (key1165, 6)]

def rawRow10078 : Integer.Sparse Key := [(key1094, -24), (key980, 6), (key1165, 6), (key1094, 6), (key1165, 6)]

def rawRow10079 : Integer.Sparse Key := [(key1094, -24), (key980, 6), (key1165, 6), (key1165, 6), (key1094, 6)]

def rawRow10080 : Integer.Sparse Key := [(key1094, -24), (key1094, 6), (key980, 6), (key1165, 6), (key1165, 6)]

def rawRow10081 : Integer.Sparse Key := [(key1094, -24), (key1094, 6), (key1165, 6), (key980, 6), (key1165, 6)]

def rawRow10082 : Integer.Sparse Key := [(key1094, -24), (key1094, 6), (key1165, 6), (key1165, 6), (key980, 6)]

def rawRow10083 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key980, 6), (key1094, 6), (key1165, 6)]

def rawRow10084 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key980, 6), (key1165, 6), (key1094, 6)]

def rawRow10085 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1094, 6), (key980, 6), (key1165, 6)]

def rawRow10086 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1094, 6), (key1165, 6), (key980, 6)]

def rawRow10087 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1165, 6), (key980, 6), (key1094, 6)]

def rawRow10088 : Integer.Sparse Key := [(key1094, -24), (key1165, 6), (key1165, 6), (key1094, 6), (key980, 6)]

def rawRow10089 : Integer.Sparse Key := [(key1165, -24), (key980, 6), (key1094, 6), (key1094, 6), (key1165, 6)]

def rawRow10090 : Integer.Sparse Key := [(key1165, -24), (key980, 6), (key1094, 6), (key1165, 6), (key1094, 6)]

def rawRow10091 : Integer.Sparse Key := [(key1165, -24), (key980, 6), (key1165, 6), (key1094, 6), (key1094, 6)]

def rawRow10092 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key980, 6), (key1094, 6), (key1165, 6)]

def rawRow10093 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key980, 6), (key1165, 6), (key1094, 6)]

def rawRow10094 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1094, 6), (key980, 6), (key1165, 6)]

def rawRow10095 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1094, 6), (key1165, 6), (key980, 6)]

def rawRow10096 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1165, 6), (key980, 6), (key1094, 6)]

def rawRow10097 : Integer.Sparse Key := [(key1165, -24), (key1094, 6), (key1165, 6), (key1094, 6), (key980, 6)]

def rawRow10098 : Integer.Sparse Key := [(key1165, -24), (key1165, 6), (key980, 6), (key1094, 6), (key1094, 6)]

def rawRow10099 : Integer.Sparse Key := [(key1165, -24), (key1165, 6), (key1094, 6), (key980, 6), (key1094, 6)]

def rawRow10100 : Integer.Sparse Key := [(key1165, -24), (key1165, 6), (key1094, 6), (key1094, 6), (key980, 6)]

def rawRow10101 : Integer.Sparse Key := [(key1038, -2), (key1038, -2), (key1044, -2), (key1116, -2), (key1116, -2), (key1125, -2), (key1125, -2), (key1130, -2), (key1130, -2), (key1233, -2), (key1236, -2), (key1236, -2), (key1003, 2), (key1003, 2), (key1009, 2), (key1116, 2), (key1116, 2), (key1152, 2), (key1152, 2), (key1159, 2), (key1159, 2), (key1233, 2), (key1243, 2), (key1243, 2)]

def rawRow10102 : Integer.Sparse Key := [(key1038, -2), (key1044, -2), (key1038, -2), (key1125, -2), (key1130, -2), (key1116, -2), (key1130, -2), (key1116, -2), (key1125, -2), (key1236, -2), (key1233, -2), (key1236, -2), (key1003, 2), (key1009, 2), (key1003, 2), (key1152, 2), (key1159, 2), (key1116, 2), (key1159, 2), (key1116, 2), (key1152, 2), (key1243, 2), (key1233, 2), (key1243, 2)]

def rawRow10103 : Integer.Sparse Key := [(key1044, -2), (key1038, -2), (key1038, -2), (key1130, -2), (key1125, -2), (key1130, -2), (key1116, -2), (key1125, -2), (key1116, -2), (key1236, -2), (key1236, -2), (key1233, -2), (key1009, 2), (key1003, 2), (key1003, 2), (key1159, 2), (key1152, 2), (key1159, 2), (key1116, 2), (key1152, 2), (key1116, 2), (key1243, 2), (key1243, 2), (key1233, 2)]

def rawRow10104 : Integer.Sparse Key := [(key1116, -2), (key1116, -2), (key1233, -2), (key1038, -2), (key1038, -2), (key1125, -2), (key1125, -2), (key1236, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1130, -2), (key1116, 2), (key1116, 2), (key1233, 2), (key1003, 2), (key1003, 2), (key1152, 2), (key1152, 2), (key1243, 2), (key1243, 2), (key1009, 2), (key1159, 2), (key1159, 2)]

def rawRow10105 : Integer.Sparse Key := [(key1116, -2), (key1233, -2), (key1116, -2), (key1125, -2), (key1236, -2), (key1038, -2), (key1236, -2), (key1038, -2), (key1125, -2), (key1130, -2), (key1044, -2), (key1130, -2), (key1116, 2), (key1233, 2), (key1116, 2), (key1152, 2), (key1243, 2), (key1003, 2), (key1243, 2), (key1003, 2), (key1152, 2), (key1159, 2), (key1009, 2), (key1159, 2)]

def rawRow10106 : Integer.Sparse Key := [(key1233, -2), (key1116, -2), (key1116, -2), (key1236, -2), (key1125, -2), (key1236, -2), (key1038, -2), (key1125, -2), (key1038, -2), (key1130, -2), (key1130, -2), (key1044, -2), (key1233, 2), (key1116, 2), (key1116, 2), (key1243, 2), (key1152, 2), (key1243, 2), (key1003, 2), (key1152, 2), (key1003, 2), (key1159, 2), (key1159, 2), (key1009, 2)]

def rawRow10107 : Integer.Sparse Key := [(key1125, -2), (key1130, -2), (key1236, -2), (key1038, -2), (key1044, -2), (key1116, -2), (key1130, -2), (key1233, -2), (key1236, -2), (key1038, -2), (key1116, -2), (key1125, -2), (key1152, 2), (key1159, 2), (key1243, 2), (key1003, 2), (key1009, 2), (key1116, 2), (key1159, 2), (key1233, 2), (key1243, 2), (key1003, 2), (key1116, 2), (key1152, 2)]

def rawRow10108 : Integer.Sparse Key := [(key1130, -2), (key1125, -2), (key1236, -2), (key1044, -2), (key1038, -2), (key1130, -2), (key1116, -2), (key1236, -2), (key1233, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1159, 2), (key1152, 2), (key1243, 2), (key1009, 2), (key1003, 2), (key1159, 2), (key1116, 2), (key1243, 2), (key1233, 2), (key1003, 2), (key1152, 2), (key1116, 2)]

def rawRow10109 : Integer.Sparse Key := [(key1125, -2), (key1236, -2), (key1130, -2), (key1116, -2), (key1233, -2), (key1038, -2), (key1236, -2), (key1044, -2), (key1130, -2), (key1116, -2), (key1038, -2), (key1125, -2), (key1152, 2), (key1243, 2), (key1159, 2), (key1116, 2), (key1233, 2), (key1003, 2), (key1243, 2), (key1009, 2), (key1159, 2), (key1116, 2), (key1003, 2), (key1152, 2)]

def rawRow10110 : Integer.Sparse Key := [(key1236, -2), (key1125, -2), (key1130, -2), (key1233, -2), (key1116, -2), (key1236, -2), (key1038, -2), (key1130, -2), (key1044, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1243, 2), (key1152, 2), (key1159, 2), (key1233, 2), (key1116, 2), (key1243, 2), (key1003, 2), (key1159, 2), (key1009, 2), (key1116, 2), (key1152, 2), (key1003, 2)]

def rawRow10111 : Integer.Sparse Key := [(key1130, -2), (key1236, -2), (key1125, -2), (key1130, -2), (key1236, -2), (key1044, -2), (key1233, -2), (key1038, -2), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1159, 2), (key1243, 2), (key1152, 2), (key1159, 2), (key1243, 2), (key1009, 2), (key1233, 2), (key1003, 2), (key1116, 2), (key1152, 2), (key1003, 2), (key1116, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10112 : Integer.Sparse Key := [(key1236, -2), (key1130, -2), (key1125, -2), (key1236, -2), (key1130, -2), (key1233, -2), (key1044, -2), (key1116, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1038, -2), (key1243, 2), (key1159, 2), (key1152, 2), (key1243, 2), (key1159, 2), (key1233, 2), (key1009, 2), (key1116, 2), (key1003, 2), (key1152, 2), (key1116, 2), (key1003, 2)]

def rawRow10113 : Integer.Sparse Key := [(key1073, -2), (key1080, -2), (key1080, -2), (key1152, -2), (key1159, -2), (key1152, -2), (key1174, -2), (key1159, -2), (key1174, -2), (key1243, -2), (key1243, -2), (key1247, -2), (key1017, 2), (key1022, 2), (key1022, 2), (key1125, 2), (key1130, 2), (key1125, 2), (key1174, 2), (key1130, 2), (key1174, 2), (key1236, 2), (key1236, 2), (key1247, 2)]

def rawRow10114 : Integer.Sparse Key := [(key1080, -2), (key1073, -2), (key1080, -2), (key1159, -2), (key1152, -2), (key1174, -2), (key1152, -2), (key1174, -2), (key1159, -2), (key1243, -2), (key1247, -2), (key1243, -2), (key1022, 2), (key1017, 2), (key1022, 2), (key1130, 2), (key1125, 2), (key1174, 2), (key1125, 2), (key1174, 2), (key1130, 2), (key1236, 2), (key1247, 2), (key1236, 2)]

def rawRow10115 : Integer.Sparse Key := [(key1080, -2), (key1080, -2), (key1073, -2), (key1174, -2), (key1174, -2), (key1159, -2), (key1159, -2), (key1152, -2), (key1152, -2), (key1247, -2), (key1243, -2), (key1243, -2), (key1022, 2), (key1022, 2), (key1017, 2), (key1174, 2), (key1174, 2), (key1130, 2), (key1130, 2), (key1125, 2), (key1125, 2), (key1247, 2), (key1236, 2), (key1236, 2)]

def rawRow10116 : Integer.Sparse Key := [(key1152, -2), (key1159, -2), (key1243, -2), (key1073, -2), (key1080, -2), (key1152, -2), (key1174, -2), (key1243, -2), (key1247, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1125, 2), (key1130, 2), (key1236, 2), (key1017, 2), (key1022, 2), (key1125, 2), (key1174, 2), (key1236, 2), (key1247, 2), (key1022, 2), (key1130, 2), (key1174, 2)]

def rawRow10117 : Integer.Sparse Key := [(key1159, -2), (key1152, -2), (key1243, -2), (key1080, -2), (key1073, -2), (key1174, -2), (key1152, -2), (key1247, -2), (key1243, -2), (key1080, -2), (key1174, -2), (key1159, -2), (key1130, 2), (key1125, 2), (key1236, 2), (key1022, 2), (key1017, 2), (key1174, 2), (key1125, 2), (key1247, 2), (key1236, 2), (key1022, 2), (key1174, 2), (key1130, 2)]

def rawRow10118 : Integer.Sparse Key := [(key1152, -2), (key1243, -2), (key1159, -2), (key1152, -2), (key1243, -2), (key1073, -2), (key1247, -2), (key1080, -2), (key1174, -2), (key1159, -2), (key1080, -2), (key1174, -2), (key1125, 2), (key1236, 2), (key1130, 2), (key1125, 2), (key1236, 2), (key1017, 2), (key1247, 2), (key1022, 2), (key1174, 2), (key1130, 2), (key1022, 2), (key1174, 2)]

def rawRow10119 : Integer.Sparse Key := [(key1243, -2), (key1152, -2), (key1159, -2), (key1243, -2), (key1152, -2), (key1247, -2), (key1073, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1080, -2), (key1236, 2), (key1125, 2), (key1130, 2), (key1236, 2), (key1125, 2), (key1247, 2), (key1017, 2), (key1174, 2), (key1022, 2), (key1130, 2), (key1174, 2), (key1022, 2)]

def rawRow10120 : Integer.Sparse Key := [(key1159, -2), (key1243, -2), (key1152, -2), (key1174, -2), (key1247, -2), (key1080, -2), (key1243, -2), (key1073, -2), (key1152, -2), (key1174, -2), (key1080, -2), (key1159, -2), (key1130, 2), (key1236, 2), (key1125, 2), (key1174, 2), (key1247, 2), (key1022, 2), (key1236, 2), (key1017, 2), (key1125, 2), (key1174, 2), (key1022, 2), (key1130, 2)]

def rawRow10121 : Integer.Sparse Key := [(key1243, -2), (key1159, -2), (key1152, -2), (key1247, -2), (key1174, -2), (key1243, -2), (key1080, -2), (key1152, -2), (key1073, -2), (key1174, -2), (key1159, -2), (key1080, -2), (key1236, 2), (key1130, 2), (key1125, 2), (key1247, 2), (key1174, 2), (key1236, 2), (key1022, 2), (key1125, 2), (key1017, 2), (key1174, 2), (key1130, 2), (key1022, 2)]

def rawRow10122 : Integer.Sparse Key := [(key1174, -2), (key1174, -2), (key1247, -2), (key1080, -2), (key1080, -2), (key1159, -2), (key1159, -2), (key1243, -2), (key1243, -2), (key1073, -2), (key1152, -2), (key1152, -2), (key1174, 2), (key1174, 2), (key1247, 2), (key1022, 2), (key1022, 2), (key1130, 2), (key1130, 2), (key1236, 2), (key1236, 2), (key1017, 2), (key1125, 2), (key1125, 2)]

def rawRow10123 : Integer.Sparse Key := [(key1174, -2), (key1247, -2), (key1174, -2), (key1159, -2), (key1243, -2), (key1080, -2), (key1243, -2), (key1080, -2), (key1159, -2), (key1152, -2), (key1073, -2), (key1152, -2), (key1174, 2), (key1247, 2), (key1174, 2), (key1130, 2), (key1236, 2), (key1022, 2), (key1236, 2), (key1022, 2), (key1130, 2), (key1125, 2), (key1017, 2), (key1125, 2)]

def rawRow10124 : Integer.Sparse Key := [(key1247, -2), (key1174, -2), (key1174, -2), (key1243, -2), (key1159, -2), (key1243, -2), (key1080, -2), (key1159, -2), (key1080, -2), (key1152, -2), (key1152, -2), (key1073, -2), (key1247, 2), (key1174, 2), (key1174, 2), (key1236, 2), (key1130, 2), (key1236, 2), (key1022, 2), (key1130, 2), (key1022, 2), (key1125, 2), (key1125, 2), (key1017, 2)]

def rawRow10125 : Integer.Sparse Key := [(key210, -2), (key210, -2), (key213, -2), (key430, -2), (key430, -2), (key590, -2), (key590, -2), (key592, -2), (key592, -2), (key461, -2), (key609, -2), (key609, -2), (key25, 1), (key25, 1), (key37, 1), (key37, 1), (key40, 1), (key40, 1), (key50, 1), (key50, 1), (key76, 1), (key76, 1), (key81, 1), (key81, 1), (key117, 1), (key117, 1), (key139, 1), (key139, 1), (key162, 1), (key162, 1), (key197, 1), (key197, 1), (key201, 1), (key201, 1), (key204, 1), (key204, 1)]

def rawRow10126 : Integer.Sparse Key := [(key210, -2), (key213, -2), (key210, -2), (key590, -2), (key592, -2), (key430, -2), (key592, -2), (key430, -2), (key590, -2), (key609, -2), (key461, -2), (key609, -2), (key37, 1), (key40, 1), (key25, 1), (key40, 1), (key25, 1), (key37, 1), (key76, 1), (key81, 1), (key50, 1), (key81, 1), (key50, 1), (key76, 1), (key139, 1), (key162, 1), (key117, 1), (key162, 1), (key117, 1), (key139, 1), (key201, 1), (key204, 1), (key197, 1), (key204, 1), (key197, 1), (key201, 1)]

def rawRow10127 : Integer.Sparse Key := [(key213, -2), (key210, -2), (key210, -2), (key592, -2), (key590, -2), (key592, -2), (key430, -2), (key590, -2), (key430, -2), (key609, -2), (key609, -2), (key461, -2), (key40, 1), (key37, 1), (key40, 1), (key25, 1), (key37, 1), (key25, 1), (key81, 1), (key76, 1), (key81, 1), (key50, 1), (key76, 1), (key50, 1), (key162, 1), (key139, 1), (key162, 1), (key117, 1), (key139, 1), (key117, 1), (key204, 1), (key201, 1), (key204, 1), (key197, 1), (key201, 1), (key197, 1)]

def rawRow10128 : Integer.Sparse Key := [(key430, -2), (key430, -2), (key461, -2), (key210, -2), (key210, -2), (key590, -2), (key590, -2), (key609, -2), (key609, -2), (key213, -2), (key592, -2), (key592, -2), (key379, 1), (key379, 1), (key464, 1), (key464, 1), (key483, 1), (key483, 1), (key210, 1), (key210, 1), (key590, 1), (key590, 1), (key609, 1), (key609, 1), (key37, 1), (key37, 1), (key76, 1), (key76, 1), (key204, 1), (key204, 1), (key40, 1), (key40, 1), (key81, 1), (key81, 1), (key162, 1), (key162, 1)]

def rawRow10129 : Integer.Sparse Key := [(key430, -2), (key461, -2), (key430, -2), (key590, -2), (key609, -2), (key210, -2), (key609, -2), (key210, -2), (key590, -2), (key592, -2), (key213, -2), (key592, -2), (key464, 1), (key483, 1), (key379, 1), (key483, 1), (key379, 1), (key464, 1), (key590, 1), (key609, 1), (key210, 1), (key609, 1), (key210, 1), (key590, 1), (key565, 1), (key615, 1), (key215, 1), (key615, 1), (key37, 1), (key76, 1), (key81, 1), (key162, 1), (key40, 1), (key162, 1), (key40, 1), (key81, 1)]

def rawRow10130 : Integer.Sparse Key := [(key461, -2), (key430, -2), (key430, -2), (key609, -2), (key590, -2), (key609, -2), (key210, -2), (key590, -2), (key210, -2), (key592, -2), (key592, -2), (key213, -2), (key483, 1), (key464, 1), (key483, 1), (key379, 1), (key464, 1), (key379, 1), (key609, 1), (key590, 1), (key609, 1), (key210, 1), (key590, 1), (key210, 1), (key615, 1), (key565, 1), (key615, 1), (key215, 1), (key76, 1), (key37, 1), (key162, 1), (key81, 1), (key162, 1), (key40, 1), (key81, 1), (key40, 1)]

def rawRow10131 : Integer.Sparse Key := [(key590, -2), (key592, -2), (key609, -2), (key210, -2), (key213, -2), (key430, -2), (key592, -2), (key461, -2), (key609, -2), (key210, -2), (key430, -2), (key590, -2), (key565, 1), (key567, 1), (key590, 1), (key612, 1), (key609, 1), (key615, 1), (key215, 1), (key217, 1), (key464, 1), (key612, 1), (key483, 1), (key615, 1), (key210, 1), (key217, 1), (key379, 1), (key567, 1), (key483, 1), (key609, 1), (key25, 1), (key37, 1), (key50, 1), (key76, 1), (key117, 1), (key139, 1)]

def rawRow10132 : Integer.Sparse Key := [(key592, -2), (key590, -2), (key609, -2), (key213, -2), (key210, -2), (key592, -2), (key430, -2), (key609, -2), (key461, -2), (key210, -2), (key590, -2), (key430, -2), (key567, 1), (key565, 1), (key612, 1), (key590, 1), (key615, 1), (key609, 1), (key217, 1), (key215, 1), (key612, 1), (key464, 1), (key615, 1), (key483, 1), (key217, 1), (key210, 1), (key567, 1), (key379, 1), (key609, 1), (key483, 1), (key37, 1), (key25, 1), (key76, 1), (key50, 1), (key139, 1), (key117, 1)]

def rawRow10133 : Integer.Sparse Key := [(key590, -2), (key609, -2), (key592, -2), (key430, -2), (key461, -2), (key210, -2), (key609, -2), (key213, -2), (key592, -2), (key430, -2), (key210, -2), (key590, -2), (key590, 1), (key609, 1), (key565, 1), (key615, 1), (key567, 1), (key612, 1), (key464, 1), (key483, 1), (key215, 1), (key615, 1), (key217, 1), (key612, 1), (key379, 1), (key483, 1), (key210, 1), (key609, 1), (key217, 1), (key567, 1), (key50, 1), (key117, 1), (key25, 1), (key139, 1), (key37, 1), (key76, 1)]

def rawRow10134 : Integer.Sparse Key := [(key609, -2), (key590, -2), (key592, -2), (key461, -2), (key430, -2), (key609, -2), (key210, -2), (key592, -2), (key213, -2), (key430, -2), (key590, -2), (key210, -2), (key609, 1), (key590, 1), (key615, 1), (key565, 1), (key612, 1), (key567, 1), (key483, 1), (key464, 1), (key615, 1), (key215, 1), (key612, 1), (key217, 1), (key483, 1), (key379, 1), (key609, 1), (key210, 1), (key567, 1), (key217, 1), (key117, 1), (key50, 1), (key139, 1), (key25, 1), (key76, 1), (key37, 1)]

def rawRow10135 : Integer.Sparse Key := [(key592, -2), (key609, -2), (key590, -2), (key592, -2), (key609, -2), (key213, -2), (key461, -2), (key210, -2), (key430, -2), (key590, -2), (key210, -2), (key430, -2), (key612, 1), (key615, 1), (key567, 1), (key609, 1), (key565, 1), (key590, 1), (key612, 1), (key615, 1), (key217, 1), (key483, 1), (key215, 1), (key464, 1), (key567, 1), (key609, 1), (key217, 1), (key483, 1), (key210, 1), (key379, 1), (key76, 1), (key139, 1), (key37, 1), (key117, 1), (key25, 1), (key50, 1)]

def rawRow10136 : Integer.Sparse Key := [(key609, -2), (key592, -2), (key590, -2), (key609, -2), (key592, -2), (key461, -2), (key213, -2), (key430, -2), (key210, -2), (key590, -2), (key430, -2), (key210, -2), (key615, 1), (key612, 1), (key609, 1), (key567, 1), (key590, 1), (key565, 1), (key615, 1), (key612, 1), (key483, 1), (key217, 1), (key464, 1), (key215, 1), (key609, 1), (key567, 1), (key483, 1), (key217, 1), (key379, 1), (key210, 1), (key139, 1), (key76, 1), (key117, 1), (key37, 1), (key50, 1), (key25, 1)]

def rawRow10137 : Integer.Sparse Key := [(key215, -2), (key217, -2), (key217, -2), (key464, -2), (key466, -2), (key464, -2), (key612, -2), (key466, -2), (key612, -2), (key483, -2), (key483, -2), (key615, -2), (key210, 1), (key213, 1), (key210, 1), (key217, 1), (key213, 1), (key217, 1), (key379, 1), (key382, 1), (key379, 1), (key567, 1), (key382, 1), (key567, 1), (key430, 1), (key466, 1), (key430, 1), (key592, 1), (key466, 1), (key592, 1), (key461, 1), (key483, 1), (key461, 1), (key609, 1), (key483, 1), (key609, 1)]

def rawRow10138 : Integer.Sparse Key := [(key217, -2), (key215, -2), (key217, -2), (key466, -2), (key464, -2), (key612, -2), (key464, -2), (key612, -2), (key466, -2), (key483, -2), (key615, -2), (key483, -2), (key213, 1), (key210, 1), (key217, 1), (key210, 1), (key217, 1), (key213, 1), (key382, 1), (key379, 1), (key567, 1), (key379, 1), (key567, 1), (key382, 1), (key466, 1), (key430, 1), (key592, 1), (key430, 1), (key592, 1), (key466, 1), (key483, 1), (key461, 1), (key609, 1), (key461, 1), (key609, 1), (key483, 1)]

def rawRow10139 : Integer.Sparse Key := [(key217, -2), (key217, -2), (key215, -2), (key612, -2), (key612, -2), (key466, -2), (key466, -2), (key464, -2), (key464, -2), (key615, -2), (key483, -2), (key483, -2), (key217, 1), (key217, 1), (key213, 1), (key213, 1), (key210, 1), (key210, 1), (key567, 1), (key567, 1), (key382, 1), (key382, 1), (key379, 1), (key379, 1), (key592, 1), (key592, 1), (key466, 1), (key466, 1), (key430, 1), (key430, 1), (key609, 1), (key609, 1), (key483, 1), (key483, 1), (key461, 1), (key461, 1)]

def rawRow10140 : Integer.Sparse Key := [(key464, -2), (key466, -2), (key483, -2), (key215, -2), (key217, -2), (key464, -2), (key612, -2), (key483, -2), (key615, -2), (key217, -2), (key466, -2), (key612, -2), (key379, 1), (key382, 1), (key430, 1), (key466, 1), (key461, 1), (key483, 1), (key210, 1), (key213, 1), (key430, 1), (key592, 1), (key461, 1), (key609, 1), (key210, 1), (key217, 1), (key379, 1), (key567, 1), (key483, 1), (key609, 1), (key213, 1), (key217, 1), (key382, 1), (key567, 1), (key466, 1), (key592, 1)]

def rawRow10141 : Integer.Sparse Key := [(key466, -2), (key464, -2), (key483, -2), (key217, -2), (key215, -2), (key612, -2), (key464, -2), (key615, -2), (key483, -2), (key217, -2), (key612, -2), (key466, -2), (key382, 1), (key379, 1), (key466, 1), (key430, 1), (key483, 1), (key461, 1), (key213, 1), (key210, 1), (key592, 1), (key430, 1), (key609, 1), (key461, 1), (key217, 1), (key210, 1), (key567, 1), (key379, 1), (key609, 1), (key483, 1), (key217, 1), (key213, 1), (key567, 1), (key382, 1), (key592, 1), (key466, 1)]

def rawRow10142 : Integer.Sparse Key := [(key464, -2), (key483, -2), (key466, -2), (key464, -2), (key483, -2), (key215, -2), (key615, -2), (key217, -2), (key612, -2), (key466, -2), (key217, -2), (key612, -2), (key430, 1), (key461, 1), (key379, 1), (key483, 1), (key382, 1), (key466, 1), (key430, 1), (key461, 1), (key210, 1), (key609, 1), (key213, 1), (key592, 1), (key379, 1), (key483, 1), (key210, 1), (key609, 1), (key217, 1), (key567, 1), (key382, 1), (key466, 1), (key213, 1), (key592, 1), (key217, 1), (key567, 1)]

def rawRow10143 : Integer.Sparse Key := [(key483, -2), (key464, -2), (key466, -2), (key483, -2), (key464, -2), (key615, -2), (key215, -2), (key612, -2), (key217, -2), (key466, -2), (key612, -2), (key217, -2), (key461, 1), (key430, 1), (key483, 1), (key379, 1), (key466, 1), (key382, 1), (key461, 1), (key430, 1), (key609, 1), (key210, 1), (key592, 1), (key213, 1), (key483, 1), (key379, 1), (key609, 1), (key210, 1), (key567, 1), (key217, 1), (key466, 1), (key382, 1), (key592, 1), (key213, 1), (key567, 1), (key217, 1)]

def rawRow10144 : Integer.Sparse Key := [(key466, -2), (key483, -2), (key464, -2), (key612, -2), (key615, -2), (key217, -2), (key483, -2), (key215, -2), (key464, -2), (key612, -2), (key217, -2), (key466, -2), (key466, 1), (key483, 1), (key382, 1), (key461, 1), (key379, 1), (key430, 1), (key592, 1), (key609, 1), (key213, 1), (key461, 1), (key210, 1), (key430, 1), (key567, 1), (key609, 1), (key217, 1), (key483, 1), (key210, 1), (key379, 1), (key567, 1), (key592, 1), (key217, 1), (key466, 1), (key213, 1), (key382, 1)]

def rawRow10145 : Integer.Sparse Key := [(key483, -2), (key466, -2), (key464, -2), (key615, -2), (key612, -2), (key483, -2), (key217, -2), (key464, -2), (key215, -2), (key612, -2), (key466, -2), (key217, -2), (key483, 1), (key466, 1), (key461, 1), (key382, 1), (key430, 1), (key379, 1), (key609, 1), (key592, 1), (key461, 1), (key213, 1), (key430, 1), (key210, 1), (key609, 1), (key567, 1), (key483, 1), (key217, 1), (key379, 1), (key210, 1), (key592, 1), (key567, 1), (key466, 1), (key217, 1), (key382, 1), (key213, 1)]

def rawRow10146 : Integer.Sparse Key := [(key612, -2), (key612, -2), (key615, -2), (key217, -2), (key217, -2), (key466, -2), (key466, -2), (key483, -2), (key483, -2), (key215, -2), (key464, -2), (key464, -2), (key567, 1), (key567, 1), (key592, 1), (key592, 1), (key609, 1), (key609, 1), (key217, 1), (key217, 1), (key466, 1), (key466, 1), (key483, 1), (key483, 1), (key213, 1), (key213, 1), (key382, 1), (key382, 1), (key461, 1), (key461, 1), (key210, 1), (key210, 1), (key379, 1), (key379, 1), (key430, 1), (key430, 1)]

def rawRow10147 : Integer.Sparse Key := [(key612, -2), (key615, -2), (key612, -2), (key466, -2), (key483, -2), (key217, -2), (key483, -2), (key217, -2), (key466, -2), (key464, -2), (key215, -2), (key464, -2), (key592, 1), (key609, 1), (key567, 1), (key609, 1), (key567, 1), (key592, 1), (key466, 1), (key483, 1), (key217, 1), (key483, 1), (key217, 1), (key466, 1), (key382, 1), (key461, 1), (key213, 1), (key461, 1), (key213, 1), (key382, 1), (key379, 1), (key430, 1), (key210, 1), (key430, 1), (key210, 1), (key379, 1)]

def rawRow10148 : Integer.Sparse Key := [(key615, -2), (key612, -2), (key612, -2), (key483, -2), (key466, -2), (key483, -2), (key217, -2), (key466, -2), (key217, -2), (key464, -2), (key464, -2), (key215, -2), (key609, 1), (key592, 1), (key609, 1), (key567, 1), (key592, 1), (key567, 1), (key483, 1), (key466, 1), (key483, 1), (key217, 1), (key466, 1), (key217, 1), (key461, 1), (key382, 1), (key461, 1), (key213, 1), (key382, 1), (key213, 1), (key430, 1), (key379, 1), (key430, 1), (key210, 1), (key379, 1), (key210, 1)]

def rawRow10149 : Integer.Sparse Key := [(key1003, 1), (key1003, 1), (key1017, 1), (key1017, 1), (key1022, 1), (key1022, 1), (key1038, 1), (key1038, 1), (key1073, 1), (key1073, 1), (key1080, 1), (key1080, 1), (key1125, 1), (key1125, 1), (key1152, 1), (key1152, 1), (key1174, 1), (key1174, 1), (key1236, 1), (key1236, 1), (key1243, 1), (key1243, 1), (key1247, 1), (key1247, 1), (key1009, -2), (key1022, -2), (key1022, -2), (key1044, -2), (key1080, -2), (key1080, -2), (key1130, -2), (key1130, -2), (key1159, -2), (key1159, -2), (key1174, -2), (key1174, -2)]

def rawRow10150 : Integer.Sparse Key := [(key1017, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1247, 1), (key1236, 1), (key1243, 1), (key1022, -2), (key1009, -2), (key1022, -2), (key1080, -2), (key1044, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1130, -2), (key1174, -2), (key1130, -2), (key1159, -2)]

def rawRow10151 : Integer.Sparse Key := [(key1022, 1), (key1017, 1), (key1022, 1), (key1003, 1), (key1017, 1), (key1003, 1), (key1080, 1), (key1073, 1), (key1080, 1), (key1038, 1), (key1073, 1), (key1038, 1), (key1174, 1), (key1152, 1), (key1174, 1), (key1125, 1), (key1152, 1), (key1125, 1), (key1247, 1), (key1243, 1), (key1247, 1), (key1236, 1), (key1243, 1), (key1236, 1), (key1022, -2), (key1022, -2), (key1009, -2), (key1080, -2), (key1080, -2), (key1044, -2), (key1174, -2), (key1159, -2), (key1174, -2), (key1130, -2), (key1159, -2), (key1130, -2)]

def rawRow10152 : Integer.Sparse Key := [(key1038, 1), (key1038, 1), (key1125, 1), (key1125, 1), (key1236, 1), (key1236, 1), (key1003, 1), (key1003, 1), (key1152, 1), (key1152, 1), (key1243, 1), (key1243, 1), (key1017, 1), (key1017, 1), (key1073, 1), (key1073, 1), (key1247, 1), (key1247, 1), (key1022, 1), (key1022, 1), (key1080, 1), (key1080, 1), (key1174, 1), (key1174, 1), (key1044, -2), (key1130, -2), (key1130, -2), (key1009, -2), (key1159, -2), (key1159, -2), (key1022, -2), (key1022, -2), (key1080, -2), (key1080, -2), (key1174, -2), (key1174, -2)]

def rawRow10153 : Integer.Sparse Key := [(key1125, 1), (key1236, 1), (key1038, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1174, 1), (key1022, 1), (key1080, 1), (key1130, -2), (key1044, -2), (key1130, -2), (key1159, -2), (key1009, -2), (key1159, -2), (key1080, -2), (key1174, -2), (key1022, -2), (key1174, -2), (key1022, -2), (key1080, -2)]

def rawRow10154 : Integer.Sparse Key := [(key1236, 1), (key1125, 1), (key1236, 1), (key1038, 1), (key1125, 1), (key1038, 1), (key1243, 1), (key1152, 1), (key1243, 1), (key1003, 1), (key1152, 1), (key1003, 1), (key1247, 1), (key1073, 1), (key1247, 1), (key1017, 1), (key1073, 1), (key1017, 1), (key1174, 1), (key1080, 1), (key1174, 1), (key1022, 1), (key1080, 1), (key1022, 1), (key1130, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1159, -2), (key1009, -2), (key1174, -2), (key1080, -2), (key1174, -2), (key1022, -2), (key1080, -2), (key1022, -2)]

def rawRow10155 : Integer.Sparse Key := [(key1073, 1), (key1080, 1), (key1152, 1), (key1174, 1), (key1243, 1), (key1247, 1), (key1017, 1), (key1022, 1), (key1125, 1), (key1174, 1), (key1236, 1), (key1247, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1003, 1), (key1017, 1), (key1038, 1), (key1073, 1), (key1125, 1), (key1152, 1), (key1080, -2), (key1159, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1174, -2), (key1009, -2), (key1022, -2), (key1044, -2), (key1080, -2), (key1130, -2), (key1159, -2)]

def rawRow10156 : Integer.Sparse Key := [(key1080, 1), (key1073, 1), (key1174, 1), (key1152, 1), (key1247, 1), (key1243, 1), (key1022, 1), (key1017, 1), (key1174, 1), (key1125, 1), (key1247, 1), (key1236, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1017, 1), (key1003, 1), (key1073, 1), (key1038, 1), (key1152, 1), (key1125, 1), (key1080, -2), (key1174, -2), (key1159, -2), (key1022, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1009, -2), (key1080, -2), (key1044, -2), (key1159, -2), (key1130, -2)]

def rawRow10157 : Integer.Sparse Key := [(key1152, 1), (key1243, 1), (key1073, 1), (key1247, 1), (key1080, 1), (key1174, 1), (key1125, 1), (key1236, 1), (key1017, 1), (key1247, 1), (key1022, 1), (key1174, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1038, 1), (key1125, 1), (key1003, 1), (key1152, 1), (key1017, 1), (key1073, 1), (key1159, -2), (key1080, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1174, -2), (key1044, -2), (key1130, -2), (key1009, -2), (key1159, -2), (key1022, -2), (key1080, -2)]

def rawRow10158 : Integer.Sparse Key := [(key1243, 1), (key1152, 1), (key1247, 1), (key1073, 1), (key1174, 1), (key1080, 1), (key1236, 1), (key1125, 1), (key1247, 1), (key1017, 1), (key1174, 1), (key1022, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1125, 1), (key1038, 1), (key1152, 1), (key1003, 1), (key1073, 1), (key1017, 1), (key1159, -2), (key1174, -2), (key1080, -2), (key1130, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1044, -2), (key1159, -2), (key1009, -2), (key1080, -2), (key1022, -2)]

def rawRow10159 : Integer.Sparse Key := [(key1174, 1), (key1247, 1), (key1080, 1), (key1243, 1), (key1073, 1), (key1152, 1), (key1174, 1), (key1247, 1), (key1022, 1), (key1236, 1), (key1017, 1), (key1125, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1073, 1), (key1152, 1), (key1017, 1), (key1125, 1), (key1003, 1), (key1038, 1), (key1174, -2), (key1080, -2), (key1159, -2), (key1174, -2), (key1022, -2), (key1130, -2), (key1080, -2), (key1159, -2), (key1022, -2), (key1130, -2), (key1009, -2), (key1044, -2)]

def rawRow10160 : Integer.Sparse Key := [(key1247, 1), (key1174, 1), (key1243, 1), (key1080, 1), (key1152, 1), (key1073, 1), (key1247, 1), (key1174, 1), (key1236, 1), (key1022, 1), (key1125, 1), (key1017, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1152, 1), (key1073, 1), (key1125, 1), (key1017, 1), (key1038, 1), (key1003, 1), (key1174, -2), (key1159, -2), (key1080, -2), (key1174, -2), (key1130, -2), (key1022, -2), (key1159, -2), (key1080, -2), (key1130, -2), (key1022, -2), (key1044, -2), (key1009, -2)]

def rawRow10161 : Integer.Sparse Key := [(key1003, 1), (key1009, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1022, 1), (key1038, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1080, 1), (key1116, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1159, 1), (key1233, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1236, 1), (key1243, 1), (key1003, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1038, -2), (key1073, -2), (key1116, -2), (key1125, -2), (key1116, -2), (key1152, -2), (key1125, -2), (key1152, -2)]

def rawRow10162 : Integer.Sparse Key := [(key1009, 1), (key1003, 1), (key1022, 1), (key1003, 1), (key1022, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1080, 1), (key1038, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1159, 1), (key1116, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1233, 1), (key1243, 1), (key1233, 1), (key1243, 1), (key1236, 1), (key1003, -2), (key1017, -2), (key1003, -2), (key1038, -2), (key1073, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1152, -2), (key1116, -2), (key1152, -2), (key1125, -2)]

def rawRow10163 : Integer.Sparse Key := [(key1022, 1), (key1022, 1), (key1009, 1), (key1009, 1), (key1003, 1), (key1003, 1), (key1080, 1), (key1080, 1), (key1044, 1), (key1044, 1), (key1038, 1), (key1038, 1), (key1159, 1), (key1159, 1), (key1130, 1), (key1130, 1), (key1116, 1), (key1116, 1), (key1243, 1), (key1243, 1), (key1236, 1), (key1236, 1), (key1233, 1), (key1233, 1), (key1017, -2), (key1003, -2), (key1003, -2), (key1073, -2), (key1038, -2), (key1038, -2), (key1152, -2), (key1152, -2), (key1125, -2), (key1125, -2), (key1116, -2), (key1116, -2)]

def rawRow10164 : Integer.Sparse Key := [(key1038, 1), (key1044, 1), (key1116, 1), (key1130, 1), (key1233, 1), (key1236, 1), (key1003, 1), (key1009, 1), (key1116, 1), (key1159, 1), (key1233, 1), (key1243, 1), (key1003, 1), (key1022, 1), (key1038, 1), (key1080, 1), (key1236, 1), (key1243, 1), (key1009, 1), (key1022, 1), (key1044, 1), (key1080, 1), (key1130, 1), (key1159, 1), (key1038, -2), (key1116, -2), (key1125, -2), (key1003, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1017, -2), (key1038, -2), (key1073, -2), (key1125, -2), (key1152, -2)]

def rawRow10165 : Integer.Sparse Key := [(key1044, 1), (key1038, 1), (key1130, 1), (key1116, 1), (key1236, 1), (key1233, 1), (key1009, 1), (key1003, 1), (key1159, 1), (key1116, 1), (key1243, 1), (key1233, 1), (key1022, 1), (key1003, 1), (key1080, 1), (key1038, 1), (key1243, 1), (key1236, 1), (key1022, 1), (key1009, 1), (key1080, 1), (key1044, 1), (key1159, 1), (key1130, 1), (key1038, -2), (key1125, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1116, -2), (key1017, -2), (key1003, -2), (key1073, -2), (key1038, -2), (key1152, -2), (key1125, -2)]

def rawRow10166 : Integer.Sparse Key := [(key1116, 1), (key1233, 1), (key1038, 1), (key1236, 1), (key1044, 1), (key1130, 1), (key1116, 1), (key1233, 1), (key1003, 1), (key1243, 1), (key1009, 1), (key1159, 1), (key1038, 1), (key1236, 1), (key1003, 1), (key1243, 1), (key1022, 1), (key1080, 1), (key1044, 1), (key1130, 1), (key1009, 1), (key1159, 1), (key1022, 1), (key1080, 1), (key1116, -2), (key1038, -2), (key1125, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1038, -2), (key1125, -2), (key1003, -2), (key1152, -2), (key1017, -2), (key1073, -2)]

def rawRow10167 : Integer.Sparse Key := [(key1233, 1), (key1116, 1), (key1236, 1), (key1038, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1116, 1), (key1243, 1), (key1003, 1), (key1159, 1), (key1009, 1), (key1236, 1), (key1038, 1), (key1243, 1), (key1003, 1), (key1080, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1159, 1), (key1009, 1), (key1080, 1), (key1022, 1), (key1116, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1125, -2), (key1038, -2), (key1152, -2), (key1003, -2), (key1073, -2), (key1017, -2)]

def rawRow10168 : Integer.Sparse Key := [(key1130, 1), (key1236, 1), (key1044, 1), (key1233, 1), (key1038, 1), (key1116, 1), (key1159, 1), (key1243, 1), (key1009, 1), (key1233, 1), (key1003, 1), (key1116, 1), (key1080, 1), (key1243, 1), (key1022, 1), (key1236, 1), (key1003, 1), (key1038, 1), (key1080, 1), (key1159, 1), (key1022, 1), (key1130, 1), (key1009, 1), (key1044, 1), (key1125, -2), (key1038, -2), (key1116, -2), (key1152, -2), (key1003, -2), (key1116, -2), (key1073, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1003, -2), (key1038, -2)]

def rawRow10169 : Integer.Sparse Key := [(key1236, 1), (key1130, 1), (key1233, 1), (key1044, 1), (key1116, 1), (key1038, 1), (key1243, 1), (key1159, 1), (key1233, 1), (key1009, 1), (key1116, 1), (key1003, 1), (key1243, 1), (key1080, 1), (key1236, 1), (key1022, 1), (key1038, 1), (key1003, 1), (key1159, 1), (key1080, 1), (key1130, 1), (key1022, 1), (key1044, 1), (key1009, 1), (key1125, -2), (key1116, -2), (key1038, -2), (key1152, -2), (key1116, -2), (key1003, -2), (key1152, -2), (key1073, -2), (key1125, -2), (key1017, -2), (key1038, -2), (key1003, -2)]

def rawRow10170 : Integer.Sparse Key := [(key1080, 1), (key1080, 1), (key1159, 1), (key1159, 1), (key1243, 1), (key1243, 1), (key1022, 1), (key1022, 1), (key1130, 1), (key1130, 1), (key1236, 1), (key1236, 1), (key1009, 1), (key1009, 1), (key1044, 1), (key1044, 1), (key1233, 1), (key1233, 1), (key1003, 1), (key1003, 1), (key1038, 1), (key1038, 1), (key1116, 1), (key1116, 1), (key1073, -2), (key1152, -2), (key1152, -2), (key1017, -2), (key1125, -2), (key1125, -2), (key1003, -2), (key1003, -2), (key1038, -2), (key1038, -2), (key1116, -2), (key1116, -2)]

def rawRow10171 : Integer.Sparse Key := [(key1159, 1), (key1243, 1), (key1080, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1116, 1), (key1003, 1), (key1038, 1), (key1152, -2), (key1073, -2), (key1152, -2), (key1125, -2), (key1017, -2), (key1125, -2), (key1038, -2), (key1116, -2), (key1003, -2), (key1116, -2), (key1003, -2), (key1038, -2)]

def rawRow10172 : Integer.Sparse Key := [(key1243, 1), (key1159, 1), (key1243, 1), (key1080, 1), (key1159, 1), (key1080, 1), (key1236, 1), (key1130, 1), (key1236, 1), (key1022, 1), (key1130, 1), (key1022, 1), (key1233, 1), (key1044, 1), (key1233, 1), (key1009, 1), (key1044, 1), (key1009, 1), (key1116, 1), (key1038, 1), (key1116, 1), (key1003, 1), (key1038, 1), (key1003, 1), (key1152, -2), (key1152, -2), (key1073, -2), (key1125, -2), (key1125, -2), (key1017, -2), (key1116, -2), (key1038, -2), (key1116, -2), (key1003, -2), (key1038, -2), (key1003, -2)]

def rawRow10173 : Integer.Sparse Key := [(key24, -6), (key106, -6), (key138, -6), (key138, -6), (key24, 2), (key36, 2), (key36, 2), (key49, 2), (key75, 2), (key75, 2), (key116, 2), (key116, 2), (key138, 2), (key138, 2), (key154, 2), (key154, 2)]

def rawRow10174 : Integer.Sparse Key := [(key24, -6), (key138, -6), (key106, -6), (key138, -6), (key36, 2), (key24, 2), (key36, 2), (key75, 2), (key49, 2), (key75, 2), (key138, 2), (key154, 2), (key116, 2), (key154, 2), (key116, 2), (key138, 2)]

def rawRow10175 : Integer.Sparse Key := [(key24, -6), (key138, -6), (key138, -6), (key106, -6), (key36, 2), (key36, 2), (key24, 2), (key75, 2), (key75, 2), (key49, 2), (key154, 2), (key138, 2), (key154, 2), (key116, 2), (key138, 2), (key116, 2)]

def rawRow10176 : Integer.Sparse Key := [(key106, -6), (key24, -6), (key138, -6), (key138, -6), (key49, 2), (key116, 2), (key116, 2), (key24, 2), (key138, 2), (key138, 2), (key36, 2), (key36, 2), (key75, 2), (key75, 2), (key154, 2), (key154, 2)]

def rawRow10177 : Integer.Sparse Key := [(key106, -6), (key138, -6), (key24, -6), (key138, -6), (key116, 2), (key49, 2), (key116, 2), (key138, 2), (key24, 2), (key138, 2), (key75, 2), (key154, 2), (key36, 2), (key154, 2), (key36, 2), (key75, 2)]

def rawRow10178 : Integer.Sparse Key := [(key106, -6), (key138, -6), (key138, -6), (key24, -6), (key116, 2), (key116, 2), (key49, 2), (key138, 2), (key138, 2), (key24, 2), (key154, 2), (key75, 2), (key154, 2), (key36, 2), (key75, 2), (key36, 2)]

def rawRow10179 : Integer.Sparse Key := [(key138, -6), (key24, -6), (key106, -6), (key138, -6), (key75, 2), (key138, 2), (key154, 2), (key36, 2), (key116, 2), (key154, 2), (key24, 2), (key36, 2), (key49, 2), (key75, 2), (key116, 2), (key138, 2)]

def rawRow10180 : Integer.Sparse Key := [(key138, -6), (key24, -6), (key138, -6), (key106, -6), (key75, 2), (key154, 2), (key138, 2), (key36, 2), (key154, 2), (key116, 2), (key36, 2), (key24, 2), (key75, 2), (key49, 2), (key138, 2), (key116, 2)]

def rawRow10181 : Integer.Sparse Key := [(key138, -6), (key106, -6), (key24, -6), (key138, -6), (key138, 2), (key75, 2), (key154, 2), (key116, 2), (key36, 2), (key154, 2), (key49, 2), (key116, 2), (key24, 2), (key138, 2), (key36, 2), (key75, 2)]

def rawRow10182 : Integer.Sparse Key := [(key138, -6), (key106, -6), (key138, -6), (key24, -6), (key138, 2), (key154, 2), (key75, 2), (key116, 2), (key154, 2), (key36, 2), (key116, 2), (key49, 2), (key138, 2), (key24, 2), (key75, 2), (key36, 2)]

def rawRow10183 : Integer.Sparse Key := [(key138, -6), (key138, -6), (key24, -6), (key106, -6), (key154, 2), (key75, 2), (key138, 2), (key154, 2), (key36, 2), (key116, 2), (key75, 2), (key138, 2), (key36, 2), (key116, 2), (key24, 2), (key49, 2)]

def rawRow10184 : Integer.Sparse Key := [(key138, -6), (key138, -6), (key106, -6), (key24, -6), (key154, 2), (key138, 2), (key75, 2), (key154, 2), (key116, 2), (key36, 2), (key138, 2), (key75, 2), (key116, 2), (key36, 2), (key49, 2), (key24, 2)]

def rawRow10185 : Integer.Sparse Key := [(key36, -6), (key116, -6), (key116, -6), (key154, -6), (key24, 2), (key24, 2), (key36, 2), (key49, 2), (key49, 2), (key75, 2), (key106, 2), (key116, 2), (key106, 2), (key138, 2), (key116, 2), (key138, 2)]

def rawRow10186 : Integer.Sparse Key := [(key36, -6), (key116, -6), (key154, -6), (key116, -6), (key24, 2), (key36, 2), (key24, 2), (key49, 2), (key75, 2), (key49, 2), (key116, 2), (key106, 2), (key138, 2), (key106, 2), (key138, 2), (key116, 2)]

def rawRow10187 : Integer.Sparse Key := [(key36, -6), (key154, -6), (key116, -6), (key116, -6), (key36, 2), (key24, 2), (key24, 2), (key75, 2), (key49, 2), (key49, 2), (key138, 2), (key138, 2), (key116, 2), (key116, 2), (key106, 2), (key106, 2)]

def rawRow10188 : Integer.Sparse Key := [(key116, -6), (key36, -6), (key116, -6), (key154, -6), (key49, 2), (key106, 2), (key116, 2), (key24, 2), (key106, 2), (key138, 2), (key24, 2), (key36, 2), (key49, 2), (key75, 2), (key116, 2), (key138, 2)]

def rawRow10189 : Integer.Sparse Key := [(key116, -6), (key36, -6), (key154, -6), (key116, -6), (key49, 2), (key116, 2), (key106, 2), (key24, 2), (key138, 2), (key106, 2), (key36, 2), (key24, 2), (key75, 2), (key49, 2), (key138, 2), (key116, 2)]

def rawRow10190 : Integer.Sparse Key := [(key116, -6), (key116, -6), (key36, -6), (key154, -6), (key106, 2), (key49, 2), (key116, 2), (key106, 2), (key24, 2), (key138, 2), (key49, 2), (key116, 2), (key24, 2), (key138, 2), (key36, 2), (key75, 2)]

def rawRow10191 : Integer.Sparse Key := [(key116, -6), (key116, -6), (key154, -6), (key36, -6), (key106, 2), (key116, 2), (key49, 2), (key106, 2), (key138, 2), (key24, 2), (key116, 2), (key49, 2), (key138, 2), (key24, 2), (key75, 2), (key36, 2)]

def rawRow10192 : Integer.Sparse Key := [(key116, -6), (key154, -6), (key36, -6), (key116, -6), (key116, 2), (key49, 2), (key106, 2), (key138, 2), (key24, 2), (key106, 2), (key75, 2), (key138, 2), (key36, 2), (key116, 2), (key24, 2), (key49, 2)]

def rawRow10193 : Integer.Sparse Key := [(key116, -6), (key154, -6), (key116, -6), (key36, -6), (key116, 2), (key106, 2), (key49, 2), (key138, 2), (key106, 2), (key24, 2), (key138, 2), (key75, 2), (key116, 2), (key36, 2), (key49, 2), (key24, 2)]

def rawRow10194 : Integer.Sparse Key := [(key154, -6), (key36, -6), (key116, -6), (key116, -6), (key75, 2), (key138, 2), (key138, 2), (key36, 2), (key116, 2), (key116, 2), (key24, 2), (key24, 2), (key49, 2), (key49, 2), (key106, 2), (key106, 2)]

def rawRow10195 : Integer.Sparse Key := [(key154, -6), (key116, -6), (key36, -6), (key116, -6), (key138, 2), (key75, 2), (key138, 2), (key116, 2), (key36, 2), (key116, 2), (key49, 2), (key106, 2), (key24, 2), (key106, 2), (key24, 2), (key49, 2)]

def rawRow10196 : Integer.Sparse Key := [(key154, -6), (key116, -6), (key116, -6), (key36, -6), (key138, 2), (key138, 2), (key75, 2), (key116, 2), (key116, 2), (key36, 2), (key106, 2), (key49, 2), (key106, 2), (key24, 2), (key49, 2), (key24, 2)]

def rawRow10197 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1099, 6), (key1184, 6), (key985, -6), (key1099, -6), (key1170, -6), (key1170, -6)]

def rawRow10198 : Integer.Sparse Key := [(key1095, 6), (key1099, 6), (key1095, 6), (key1184, 6), (key985, -6), (key1170, -6), (key1099, -6), (key1170, -6)]

def rawRow10199 : Integer.Sparse Key := [(key1099, 6), (key1095, 6), (key1095, 6), (key1184, 6), (key985, -6), (key1170, -6), (key1170, -6), (key1099, -6)]

def rawRow10200 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1184, 6), (key1099, 6), (key1099, -6), (key985, -6), (key1170, -6), (key1170, -6)]

def rawRow10201 : Integer.Sparse Key := [(key1095, 6), (key1184, 6), (key1095, 6), (key1099, 6), (key1099, -6), (key1170, -6), (key985, -6), (key1170, -6)]

def rawRow10202 : Integer.Sparse Key := [(key1184, 6), (key1095, 6), (key1095, 6), (key1099, 6), (key1099, -6), (key1170, -6), (key1170, -6), (key985, -6)]

def rawRow10203 : Integer.Sparse Key := [(key1095, 6), (key1099, 6), (key1184, 6), (key1095, 6), (key1170, -6), (key985, -6), (key1099, -6), (key1170, -6)]

def rawRow10204 : Integer.Sparse Key := [(key1099, 6), (key1095, 6), (key1184, 6), (key1095, 6), (key1170, -6), (key985, -6), (key1170, -6), (key1099, -6)]

def rawRow10205 : Integer.Sparse Key := [(key1095, 6), (key1184, 6), (key1099, 6), (key1095, 6), (key1170, -6), (key1099, -6), (key985, -6), (key1170, -6)]

def rawRow10206 : Integer.Sparse Key := [(key1184, 6), (key1095, 6), (key1099, 6), (key1095, 6), (key1170, -6), (key1099, -6), (key1170, -6), (key985, -6)]

def rawRow10207 : Integer.Sparse Key := [(key1099, 6), (key1184, 6), (key1095, 6), (key1095, 6), (key1170, -6), (key1170, -6), (key985, -6), (key1099, -6)]

def rawRow10208 : Integer.Sparse Key := [(key1184, 6), (key1099, 6), (key1095, 6), (key1095, 6), (key1170, -6), (key1170, -6), (key1099, -6), (key985, -6)]

def rawRow10209 : Integer.Sparse Key := [(key1166, 6), (key1170, 6), (key1170, 6), (key1221, 6), (key981, -6), (key1095, -6), (key1095, -6), (key1166, -6)]

def rawRow10210 : Integer.Sparse Key := [(key1170, 6), (key1166, 6), (key1170, 6), (key1221, 6), (key981, -6), (key1095, -6), (key1166, -6), (key1095, -6)]

def rawRow10211 : Integer.Sparse Key := [(key1170, 6), (key1170, 6), (key1166, 6), (key1221, 6), (key981, -6), (key1166, -6), (key1095, -6), (key1095, -6)]

def rawRow10212 : Integer.Sparse Key := [(key1166, 6), (key1170, 6), (key1221, 6), (key1170, 6), (key1095, -6), (key981, -6), (key1095, -6), (key1166, -6)]

def rawRow10213 : Integer.Sparse Key := [(key1170, 6), (key1166, 6), (key1221, 6), (key1170, 6), (key1095, -6), (key981, -6), (key1166, -6), (key1095, -6)]

def rawRow10214 : Integer.Sparse Key := [(key1166, 6), (key1221, 6), (key1170, 6), (key1170, 6), (key1095, -6), (key1095, -6), (key981, -6), (key1166, -6)]

def rawRow10215 : Integer.Sparse Key := [(key1221, 6), (key1166, 6), (key1170, 6), (key1170, 6), (key1095, -6), (key1095, -6), (key1166, -6), (key981, -6)]

def rawRow10216 : Integer.Sparse Key := [(key1170, 6), (key1221, 6), (key1166, 6), (key1170, 6), (key1095, -6), (key1166, -6), (key981, -6), (key1095, -6)]

def rawRow10217 : Integer.Sparse Key := [(key1221, 6), (key1170, 6), (key1166, 6), (key1170, 6), (key1095, -6), (key1166, -6), (key1095, -6), (key981, -6)]

def rawRow10218 : Integer.Sparse Key := [(key1170, 6), (key1170, 6), (key1221, 6), (key1166, 6), (key1166, -6), (key981, -6), (key1095, -6), (key1095, -6)]

def rawRow10219 : Integer.Sparse Key := [(key1170, 6), (key1221, 6), (key1170, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key981, -6), (key1095, -6)]

def rawRow10220 : Integer.Sparse Key := [(key1221, 6), (key1170, 6), (key1170, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key1095, -6), (key981, -6)]

def rawRow10221 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1101, 6), (key1229, 6), (key987, -6), (key1101, -6), (key1173, -6), (key1173, -6)]

def rawRow10222 : Integer.Sparse Key := [(key1095, 6), (key1101, 6), (key1095, 6), (key1229, 6), (key987, -6), (key1173, -6), (key1101, -6), (key1173, -6)]

def rawRow10223 : Integer.Sparse Key := [(key1101, 6), (key1095, 6), (key1095, 6), (key1229, 6), (key987, -6), (key1173, -6), (key1173, -6), (key1101, -6)]

def rawRow10224 : Integer.Sparse Key := [(key1095, 6), (key1095, 6), (key1229, 6), (key1101, 6), (key1101, -6), (key987, -6), (key1173, -6), (key1173, -6)]

def rawRow10225 : Integer.Sparse Key := [(key1095, 6), (key1229, 6), (key1095, 6), (key1101, 6), (key1101, -6), (key1173, -6), (key987, -6), (key1173, -6)]

def rawRow10226 : Integer.Sparse Key := [(key1229, 6), (key1095, 6), (key1095, 6), (key1101, 6), (key1101, -6), (key1173, -6), (key1173, -6), (key987, -6)]

def rawRow10227 : Integer.Sparse Key := [(key1095, 6), (key1101, 6), (key1229, 6), (key1095, 6), (key1173, -6), (key987, -6), (key1101, -6), (key1173, -6)]

def rawRow10228 : Integer.Sparse Key := [(key1101, 6), (key1095, 6), (key1229, 6), (key1095, 6), (key1173, -6), (key987, -6), (key1173, -6), (key1101, -6)]

def rawRow10229 : Integer.Sparse Key := [(key1095, 6), (key1229, 6), (key1101, 6), (key1095, 6), (key1173, -6), (key1101, -6), (key987, -6), (key1173, -6)]

def rawRow10230 : Integer.Sparse Key := [(key1229, 6), (key1095, 6), (key1101, 6), (key1095, 6), (key1173, -6), (key1101, -6), (key1173, -6), (key987, -6)]

def rawRow10231 : Integer.Sparse Key := [(key1101, 6), (key1229, 6), (key1095, 6), (key1095, 6), (key1173, -6), (key1173, -6), (key987, -6), (key1101, -6)]

def rawRow10232 : Integer.Sparse Key := [(key1229, 6), (key1101, 6), (key1095, 6), (key1095, 6), (key1173, -6), (key1173, -6), (key1101, -6), (key987, -6)]

def rawRow10233 : Integer.Sparse Key := [(key1166, 6), (key1173, 6), (key1173, 6), (key1246, 6), (key981, -6), (key1095, -6), (key1095, -6), (key1166, -6)]

def rawRow10234 : Integer.Sparse Key := [(key1173, 6), (key1166, 6), (key1173, 6), (key1246, 6), (key981, -6), (key1095, -6), (key1166, -6), (key1095, -6)]

def rawRow10235 : Integer.Sparse Key := [(key1173, 6), (key1173, 6), (key1166, 6), (key1246, 6), (key981, -6), (key1166, -6), (key1095, -6), (key1095, -6)]

def rawRow10236 : Integer.Sparse Key := [(key1166, 6), (key1173, 6), (key1246, 6), (key1173, 6), (key1095, -6), (key981, -6), (key1095, -6), (key1166, -6)]

def rawRow10237 : Integer.Sparse Key := [(key1173, 6), (key1166, 6), (key1246, 6), (key1173, 6), (key1095, -6), (key981, -6), (key1166, -6), (key1095, -6)]

def rawRow10238 : Integer.Sparse Key := [(key1166, 6), (key1246, 6), (key1173, 6), (key1173, 6), (key1095, -6), (key1095, -6), (key981, -6), (key1166, -6)]

def rawRow10239 : Integer.Sparse Key := [(key1246, 6), (key1166, 6), (key1173, 6), (key1173, 6), (key1095, -6), (key1095, -6), (key1166, -6), (key981, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10240 : Integer.Sparse Key := [(key1173, 6), (key1246, 6), (key1166, 6), (key1173, 6), (key1095, -6), (key1166, -6), (key981, -6), (key1095, -6)]

def rawRow10241 : Integer.Sparse Key := [(key1246, 6), (key1173, 6), (key1166, 6), (key1173, 6), (key1095, -6), (key1166, -6), (key1095, -6), (key981, -6)]

def rawRow10242 : Integer.Sparse Key := [(key1173, 6), (key1173, 6), (key1246, 6), (key1166, 6), (key1166, -6), (key981, -6), (key1095, -6), (key1095, -6)]

def rawRow10243 : Integer.Sparse Key := [(key1173, 6), (key1246, 6), (key1173, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key981, -6), (key1095, -6)]

def rawRow10244 : Integer.Sparse Key := [(key1246, 6), (key1173, 6), (key1173, 6), (key1166, 6), (key1166, -6), (key1095, -6), (key1095, -6), (key981, -6)]

def rawRow10245 : Integer.Sparse Key := [(key891, -6), (key891, -6), (key895, -6), (key916, -6), (key714, 2), (key714, 2), (key718, 2), (key891, 2), (key891, 2), (key947, 2), (key947, 2), (key948, 2), (key948, 2), (key916, 2), (key955, 2), (key955, 2)]

def rawRow10246 : Integer.Sparse Key := [(key891, -6), (key895, -6), (key891, -6), (key916, -6), (key714, 2), (key718, 2), (key714, 2), (key947, 2), (key948, 2), (key891, 2), (key948, 2), (key891, 2), (key947, 2), (key955, 2), (key916, 2), (key955, 2)]

def rawRow10247 : Integer.Sparse Key := [(key895, -6), (key891, -6), (key891, -6), (key916, -6), (key718, 2), (key714, 2), (key714, 2), (key948, 2), (key947, 2), (key948, 2), (key891, 2), (key947, 2), (key891, 2), (key955, 2), (key955, 2), (key916, 2)]

def rawRow10248 : Integer.Sparse Key := [(key891, -6), (key891, -6), (key916, -6), (key895, -6), (key891, 2), (key891, 2), (key916, 2), (key714, 2), (key714, 2), (key947, 2), (key947, 2), (key955, 2), (key955, 2), (key718, 2), (key948, 2), (key948, 2)]

def rawRow10249 : Integer.Sparse Key := [(key891, -6), (key916, -6), (key891, -6), (key895, -6), (key891, 2), (key916, 2), (key891, 2), (key947, 2), (key955, 2), (key714, 2), (key955, 2), (key714, 2), (key947, 2), (key948, 2), (key718, 2), (key948, 2)]

def rawRow10250 : Integer.Sparse Key := [(key916, -6), (key891, -6), (key891, -6), (key895, -6), (key916, 2), (key891, 2), (key891, 2), (key955, 2), (key947, 2), (key955, 2), (key714, 2), (key947, 2), (key714, 2), (key948, 2), (key948, 2), (key718, 2)]

def rawRow10251 : Integer.Sparse Key := [(key891, -6), (key895, -6), (key916, -6), (key891, -6), (key947, 2), (key948, 2), (key955, 2), (key714, 2), (key718, 2), (key891, 2), (key948, 2), (key916, 2), (key955, 2), (key714, 2), (key891, 2), (key947, 2)]

def rawRow10252 : Integer.Sparse Key := [(key895, -6), (key891, -6), (key916, -6), (key891, -6), (key948, 2), (key947, 2), (key955, 2), (key718, 2), (key714, 2), (key948, 2), (key891, 2), (key955, 2), (key916, 2), (key714, 2), (key947, 2), (key891, 2)]

def rawRow10253 : Integer.Sparse Key := [(key891, -6), (key916, -6), (key895, -6), (key891, -6), (key947, 2), (key955, 2), (key948, 2), (key891, 2), (key916, 2), (key714, 2), (key955, 2), (key718, 2), (key948, 2), (key891, 2), (key714, 2), (key947, 2)]

def rawRow10254 : Integer.Sparse Key := [(key916, -6), (key891, -6), (key895, -6), (key891, -6), (key955, 2), (key947, 2), (key948, 2), (key916, 2), (key891, 2), (key955, 2), (key714, 2), (key948, 2), (key718, 2), (key891, 2), (key947, 2), (key714, 2)]

def rawRow10255 : Integer.Sparse Key := [(key895, -6), (key916, -6), (key891, -6), (key891, -6), (key948, 2), (key955, 2), (key947, 2), (key948, 2), (key955, 2), (key718, 2), (key916, 2), (key714, 2), (key891, 2), (key947, 2), (key714, 2), (key891, 2)]

def rawRow10256 : Integer.Sparse Key := [(key916, -6), (key895, -6), (key891, -6), (key891, -6), (key955, 2), (key948, 2), (key947, 2), (key955, 2), (key948, 2), (key916, 2), (key718, 2), (key891, 2), (key714, 2), (key947, 2), (key891, 2), (key714, 2)]

def rawRow10257 : Integer.Sparse Key := [(key947, -6), (key948, -6), (key948, -6), (key955, -6), (key714, 2), (key718, 2), (key718, 2), (key891, 2), (key895, 2), (key891, 2), (key948, 2), (key895, 2), (key948, 2), (key916, 2), (key916, 2), (key955, 2)]

def rawRow10258 : Integer.Sparse Key := [(key948, -6), (key947, -6), (key948, -6), (key955, -6), (key718, 2), (key714, 2), (key718, 2), (key895, 2), (key891, 2), (key948, 2), (key891, 2), (key948, 2), (key895, 2), (key916, 2), (key955, 2), (key916, 2)]

def rawRow10259 : Integer.Sparse Key := [(key948, -6), (key948, -6), (key947, -6), (key955, -6), (key718, 2), (key718, 2), (key714, 2), (key948, 2), (key948, 2), (key895, 2), (key895, 2), (key891, 2), (key891, 2), (key955, 2), (key916, 2), (key916, 2)]

def rawRow10260 : Integer.Sparse Key := [(key947, -6), (key948, -6), (key955, -6), (key948, -6), (key891, 2), (key895, 2), (key916, 2), (key714, 2), (key718, 2), (key891, 2), (key948, 2), (key916, 2), (key955, 2), (key718, 2), (key895, 2), (key948, 2)]

def rawRow10261 : Integer.Sparse Key := [(key948, -6), (key947, -6), (key955, -6), (key948, -6), (key895, 2), (key891, 2), (key916, 2), (key718, 2), (key714, 2), (key948, 2), (key891, 2), (key955, 2), (key916, 2), (key718, 2), (key948, 2), (key895, 2)]

def rawRow10262 : Integer.Sparse Key := [(key947, -6), (key955, -6), (key948, -6), (key948, -6), (key891, 2), (key916, 2), (key895, 2), (key891, 2), (key916, 2), (key714, 2), (key955, 2), (key718, 2), (key948, 2), (key895, 2), (key718, 2), (key948, 2)]

def rawRow10263 : Integer.Sparse Key := [(key955, -6), (key947, -6), (key948, -6), (key948, -6), (key916, 2), (key891, 2), (key895, 2), (key916, 2), (key891, 2), (key955, 2), (key714, 2), (key948, 2), (key718, 2), (key895, 2), (key948, 2), (key718, 2)]

def rawRow10264 : Integer.Sparse Key := [(key948, -6), (key955, -6), (key947, -6), (key948, -6), (key895, 2), (key916, 2), (key891, 2), (key948, 2), (key955, 2), (key718, 2), (key916, 2), (key714, 2), (key891, 2), (key948, 2), (key718, 2), (key895, 2)]

def rawRow10265 : Integer.Sparse Key := [(key955, -6), (key948, -6), (key947, -6), (key948, -6), (key916, 2), (key895, 2), (key891, 2), (key955, 2), (key948, 2), (key916, 2), (key718, 2), (key891, 2), (key714, 2), (key948, 2), (key895, 2), (key718, 2)]

def rawRow10266 : Integer.Sparse Key := [(key948, -6), (key948, -6), (key955, -6), (key947, -6), (key948, 2), (key948, 2), (key955, 2), (key718, 2), (key718, 2), (key895, 2), (key895, 2), (key916, 2), (key916, 2), (key714, 2), (key891, 2), (key891, 2)]

def rawRow10267 : Integer.Sparse Key := [(key948, -6), (key955, -6), (key948, -6), (key947, -6), (key948, 2), (key955, 2), (key948, 2), (key895, 2), (key916, 2), (key718, 2), (key916, 2), (key718, 2), (key895, 2), (key891, 2), (key714, 2), (key891, 2)]

def rawRow10268 : Integer.Sparse Key := [(key955, -6), (key948, -6), (key948, -6), (key947, -6), (key955, 2), (key948, 2), (key948, 2), (key916, 2), (key895, 2), (key916, 2), (key718, 2), (key895, 2), (key718, 2), (key891, 2), (key891, 2), (key714, 2)]

def rawRow10269 : Integer.Sparse Key := [(key88, 6), (key88, 6), (key94, 6), (key156, 6), (key14, -6), (key97, -6), (key161, -6), (key161, -6)]

def rawRow10270 : Integer.Sparse Key := [(key88, 6), (key94, 6), (key88, 6), (key156, 6), (key14, -6), (key161, -6), (key97, -6), (key161, -6)]

def rawRow10271 : Integer.Sparse Key := [(key94, 6), (key88, 6), (key88, 6), (key156, 6), (key14, -6), (key161, -6), (key161, -6), (key97, -6)]

def rawRow10272 : Integer.Sparse Key := [(key88, 6), (key88, 6), (key156, 6), (key94, 6), (key97, -6), (key14, -6), (key161, -6), (key161, -6)]

def rawRow10273 : Integer.Sparse Key := [(key88, 6), (key156, 6), (key88, 6), (key94, 6), (key97, -6), (key161, -6), (key14, -6), (key161, -6)]

def rawRow10274 : Integer.Sparse Key := [(key156, 6), (key88, 6), (key88, 6), (key94, 6), (key97, -6), (key161, -6), (key161, -6), (key14, -6)]

def rawRow10275 : Integer.Sparse Key := [(key88, 6), (key94, 6), (key156, 6), (key88, 6), (key161, -6), (key14, -6), (key97, -6), (key161, -6)]

def rawRow10276 : Integer.Sparse Key := [(key94, 6), (key88, 6), (key156, 6), (key88, 6), (key161, -6), (key14, -6), (key161, -6), (key97, -6)]

def rawRow10277 : Integer.Sparse Key := [(key88, 6), (key156, 6), (key94, 6), (key88, 6), (key161, -6), (key97, -6), (key14, -6), (key161, -6)]

def rawRow10278 : Integer.Sparse Key := [(key156, 6), (key88, 6), (key94, 6), (key88, 6), (key161, -6), (key97, -6), (key161, -6), (key14, -6)]

def rawRow10279 : Integer.Sparse Key := [(key94, 6), (key156, 6), (key88, 6), (key88, 6), (key161, -6), (key161, -6), (key14, -6), (key97, -6)]

def rawRow10280 : Integer.Sparse Key := [(key156, 6), (key94, 6), (key88, 6), (key88, 6), (key161, -6), (key161, -6), (key97, -6), (key14, -6)]

def rawRow10281 : Integer.Sparse Key := [(key165, 6), (key167, 6), (key167, 6), (key187, 6), (key9, -6), (key92, -6), (key92, -6), (key153, -6)]

def rawRow10282 : Integer.Sparse Key := [(key167, 6), (key165, 6), (key167, 6), (key187, 6), (key9, -6), (key92, -6), (key153, -6), (key92, -6)]

def rawRow10283 : Integer.Sparse Key := [(key167, 6), (key167, 6), (key165, 6), (key187, 6), (key9, -6), (key153, -6), (key92, -6), (key92, -6)]

def rawRow10284 : Integer.Sparse Key := [(key165, 6), (key167, 6), (key187, 6), (key167, 6), (key92, -6), (key9, -6), (key92, -6), (key153, -6)]

def rawRow10285 : Integer.Sparse Key := [(key167, 6), (key165, 6), (key187, 6), (key167, 6), (key92, -6), (key9, -6), (key153, -6), (key92, -6)]

def rawRow10286 : Integer.Sparse Key := [(key165, 6), (key187, 6), (key167, 6), (key167, 6), (key92, -6), (key92, -6), (key9, -6), (key153, -6)]

def rawRow10287 : Integer.Sparse Key := [(key187, 6), (key165, 6), (key167, 6), (key167, 6), (key92, -6), (key92, -6), (key153, -6), (key9, -6)]

def rawRow10288 : Integer.Sparse Key := [(key167, 6), (key187, 6), (key165, 6), (key167, 6), (key92, -6), (key153, -6), (key9, -6), (key92, -6)]

def rawRow10289 : Integer.Sparse Key := [(key187, 6), (key167, 6), (key165, 6), (key167, 6), (key92, -6), (key153, -6), (key92, -6), (key9, -6)]

def rawRow10290 : Integer.Sparse Key := [(key167, 6), (key167, 6), (key187, 6), (key165, 6), (key153, -6), (key9, -6), (key92, -6), (key92, -6)]

def rawRow10291 : Integer.Sparse Key := [(key167, 6), (key187, 6), (key167, 6), (key165, 6), (key153, -6), (key92, -6), (key9, -6), (key92, -6)]

def rawRow10292 : Integer.Sparse Key := [(key187, 6), (key167, 6), (key167, 6), (key165, 6), (key153, -6), (key92, -6), (key92, -6), (key9, -6)]

def rawRow10293 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1099, -6), (key1184, -6), (key981, 2), (key981, 2), (key985, 2), (key1095, 2), (key1095, 2), (key1166, 2), (key1166, 2), (key1170, 2), (key1170, 2), (key1184, 2), (key1221, 2), (key1221, 2)]

def rawRow10294 : Integer.Sparse Key := [(key1095, -6), (key1099, -6), (key1095, -6), (key1184, -6), (key981, 2), (key985, 2), (key981, 2), (key1166, 2), (key1170, 2), (key1095, 2), (key1170, 2), (key1095, 2), (key1166, 2), (key1221, 2), (key1184, 2), (key1221, 2)]

def rawRow10295 : Integer.Sparse Key := [(key1099, -6), (key1095, -6), (key1095, -6), (key1184, -6), (key985, 2), (key981, 2), (key981, 2), (key1170, 2), (key1166, 2), (key1170, 2), (key1095, 2), (key1166, 2), (key1095, 2), (key1221, 2), (key1221, 2), (key1184, 2)]

def rawRow10296 : Integer.Sparse Key := [(key1095, -6), (key1095, -6), (key1184, -6), (key1099, -6), (key1095, 2), (key1095, 2), (key1184, 2), (key981, 2), (key981, 2), (key1166, 2), (key1166, 2), (key1221, 2), (key1221, 2), (key985, 2), (key1170, 2), (key1170, 2)]

def rawRow10297 : Integer.Sparse Key := [(key1095, -6), (key1184, -6), (key1095, -6), (key1099, -6), (key1095, 2), (key1184, 2), (key1095, 2), (key1166, 2), (key1221, 2), (key981, 2), (key1221, 2), (key981, 2), (key1166, 2), (key1170, 2), (key985, 2), (key1170, 2)]

def rawRow10298 : Integer.Sparse Key := [(key1184, -6), (key1095, -6), (key1095, -6), (key1099, -6), (key1184, 2), (key1095, 2), (key1095, 2), (key1221, 2), (key1166, 2), (key1221, 2), (key981, 2), (key1166, 2), (key981, 2), (key1170, 2), (key1170, 2), (key985, 2)]

def rawRow10299 : Integer.Sparse Key := [(key1095, -6), (key1099, -6), (key1184, -6), (key1095, -6), (key1166, 2), (key1170, 2), (key1221, 2), (key981, 2), (key985, 2), (key1095, 2), (key1170, 2), (key1184, 2), (key1221, 2), (key981, 2), (key1095, 2), (key1166, 2)]

def rawRow10300 : Integer.Sparse Key := [(key1099, -6), (key1095, -6), (key1184, -6), (key1095, -6), (key1170, 2), (key1166, 2), (key1221, 2), (key985, 2), (key981, 2), (key1170, 2), (key1095, 2), (key1221, 2), (key1184, 2), (key981, 2), (key1166, 2), (key1095, 2)]

def rawRow10301 : Integer.Sparse Key := [(key1095, -6), (key1184, -6), (key1099, -6), (key1095, -6), (key1166, 2), (key1221, 2), (key1170, 2), (key1095, 2), (key1184, 2), (key981, 2), (key1221, 2), (key985, 2), (key1170, 2), (key1095, 2), (key981, 2), (key1166, 2)]

def rawRow10302 : Integer.Sparse Key := [(key1184, -6), (key1095, -6), (key1099, -6), (key1095, -6), (key1221, 2), (key1166, 2), (key1170, 2), (key1184, 2), (key1095, 2), (key1221, 2), (key981, 2), (key1170, 2), (key985, 2), (key1095, 2), (key1166, 2), (key981, 2)]

def rawRow10303 : Integer.Sparse Key := [(key1099, -6), (key1184, -6), (key1095, -6), (key1095, -6), (key1170, 2), (key1221, 2), (key1166, 2), (key1170, 2), (key1221, 2), (key985, 2), (key1184, 2), (key981, 2), (key1095, 2), (key1166, 2), (key981, 2), (key1095, 2)]

def rawRow10304 : Integer.Sparse Key := [(key1184, -6), (key1099, -6), (key1095, -6), (key1095, -6), (key1221, 2), (key1170, 2), (key1166, 2), (key1221, 2), (key1170, 2), (key1184, 2), (key985, 2), (key1095, 2), (key981, 2), (key1166, 2), (key1095, 2), (key981, 2)]

def rawRow10305 : Integer.Sparse Key := [(key1166, -6), (key1170, -6), (key1170, -6), (key1221, -6), (key981, 2), (key985, 2), (key985, 2), (key1095, 2), (key1099, 2), (key1095, 2), (key1170, 2), (key1099, 2), (key1170, 2), (key1184, 2), (key1184, 2), (key1221, 2)]

def rawRow10306 : Integer.Sparse Key := [(key1170, -6), (key1166, -6), (key1170, -6), (key1221, -6), (key985, 2), (key981, 2), (key985, 2), (key1099, 2), (key1095, 2), (key1170, 2), (key1095, 2), (key1170, 2), (key1099, 2), (key1184, 2), (key1221, 2), (key1184, 2)]

def rawRow10307 : Integer.Sparse Key := [(key1170, -6), (key1170, -6), (key1166, -6), (key1221, -6), (key985, 2), (key985, 2), (key981, 2), (key1170, 2), (key1170, 2), (key1099, 2), (key1099, 2), (key1095, 2), (key1095, 2), (key1221, 2), (key1184, 2), (key1184, 2)]

def rawRow10308 : Integer.Sparse Key := [(key1166, -6), (key1170, -6), (key1221, -6), (key1170, -6), (key1095, 2), (key1099, 2), (key1184, 2), (key981, 2), (key985, 2), (key1095, 2), (key1170, 2), (key1184, 2), (key1221, 2), (key985, 2), (key1099, 2), (key1170, 2)]

def rawRow10309 : Integer.Sparse Key := [(key1170, -6), (key1166, -6), (key1221, -6), (key1170, -6), (key1099, 2), (key1095, 2), (key1184, 2), (key985, 2), (key981, 2), (key1170, 2), (key1095, 2), (key1221, 2), (key1184, 2), (key985, 2), (key1170, 2), (key1099, 2)]

def rawRow10310 : Integer.Sparse Key := [(key1166, -6), (key1221, -6), (key1170, -6), (key1170, -6), (key1095, 2), (key1184, 2), (key1099, 2), (key1095, 2), (key1184, 2), (key981, 2), (key1221, 2), (key985, 2), (key1170, 2), (key1099, 2), (key985, 2), (key1170, 2)]

def rawRow10311 : Integer.Sparse Key := [(key1221, -6), (key1166, -6), (key1170, -6), (key1170, -6), (key1184, 2), (key1095, 2), (key1099, 2), (key1184, 2), (key1095, 2), (key1221, 2), (key981, 2), (key1170, 2), (key985, 2), (key1099, 2), (key1170, 2), (key985, 2)]

def rawRow10312 : Integer.Sparse Key := [(key1170, -6), (key1221, -6), (key1166, -6), (key1170, -6), (key1099, 2), (key1184, 2), (key1095, 2), (key1170, 2), (key1221, 2), (key985, 2), (key1184, 2), (key981, 2), (key1095, 2), (key1170, 2), (key985, 2), (key1099, 2)]

def rawRow10313 : Integer.Sparse Key := [(key1221, -6), (key1170, -6), (key1166, -6), (key1170, -6), (key1184, 2), (key1099, 2), (key1095, 2), (key1221, 2), (key1170, 2), (key1184, 2), (key985, 2), (key1095, 2), (key981, 2), (key1170, 2), (key1099, 2), (key985, 2)]

def rawRow10314 : Integer.Sparse Key := [(key1170, -6), (key1170, -6), (key1221, -6), (key1166, -6), (key1170, 2), (key1170, 2), (key1221, 2), (key985, 2), (key985, 2), (key1099, 2), (key1099, 2), (key1184, 2), (key1184, 2), (key981, 2), (key1095, 2), (key1095, 2)]

def rawRow10315 : Integer.Sparse Key := [(key1170, -6), (key1221, -6), (key1170, -6), (key1166, -6), (key1170, 2), (key1221, 2), (key1170, 2), (key1099, 2), (key1184, 2), (key985, 2), (key1184, 2), (key985, 2), (key1099, 2), (key1095, 2), (key981, 2), (key1095, 2)]

def rawRow10316 : Integer.Sparse Key := [(key1221, -6), (key1170, -6), (key1170, -6), (key1166, -6), (key1221, 2), (key1170, 2), (key1170, 2), (key1184, 2), (key1099, 2), (key1184, 2), (key985, 2), (key1099, 2), (key985, 2), (key1095, 2), (key1095, 2), (key981, 2)]

def rawRow10317 : Integer.Sparse Key := [(key1037, -6), (key1115, -6), (key1124, -6), (key1124, -6), (key1002, 6), (key1115, 6), (key1151, 6), (key1151, 6)]

def rawRow10318 : Integer.Sparse Key := [(key1037, -6), (key1124, -6), (key1115, -6), (key1124, -6), (key1002, 6), (key1151, 6), (key1115, 6), (key1151, 6)]

def rawRow10319 : Integer.Sparse Key := [(key1037, -6), (key1124, -6), (key1124, -6), (key1115, -6), (key1002, 6), (key1151, 6), (key1151, 6), (key1115, 6)]

def rawRow10320 : Integer.Sparse Key := [(key1115, -6), (key1037, -6), (key1124, -6), (key1124, -6), (key1115, 6), (key1002, 6), (key1151, 6), (key1151, 6)]

def rawRow10321 : Integer.Sparse Key := [(key1115, -6), (key1124, -6), (key1037, -6), (key1124, -6), (key1115, 6), (key1151, 6), (key1002, 6), (key1151, 6)]

def rawRow10322 : Integer.Sparse Key := [(key1115, -6), (key1124, -6), (key1124, -6), (key1037, -6), (key1115, 6), (key1151, 6), (key1151, 6), (key1002, 6)]

def rawRow10323 : Integer.Sparse Key := [(key1124, -6), (key1037, -6), (key1115, -6), (key1124, -6), (key1151, 6), (key1002, 6), (key1115, 6), (key1151, 6)]

def rawRow10324 : Integer.Sparse Key := [(key1124, -6), (key1037, -6), (key1124, -6), (key1115, -6), (key1151, 6), (key1002, 6), (key1151, 6), (key1115, 6)]

def rawRow10325 : Integer.Sparse Key := [(key1124, -6), (key1115, -6), (key1037, -6), (key1124, -6), (key1151, 6), (key1115, 6), (key1002, 6), (key1151, 6)]

def rawRow10326 : Integer.Sparse Key := [(key1124, -6), (key1115, -6), (key1124, -6), (key1037, -6), (key1151, 6), (key1115, 6), (key1151, 6), (key1002, 6)]

def rawRow10327 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1037, -6), (key1115, -6), (key1151, 6), (key1151, 6), (key1002, 6), (key1115, 6)]

def rawRow10328 : Integer.Sparse Key := [(key1124, -6), (key1124, -6), (key1115, -6), (key1037, -6), (key1151, 6), (key1151, 6), (key1115, 6), (key1002, 6)]

def rawRow10329 : Integer.Sparse Key := [(key1072, -6), (key1151, -6), (key1151, -6), (key1167, -6), (key1016, 6), (key1124, 6), (key1124, 6), (key1167, 6)]

def rawRow10330 : Integer.Sparse Key := [(key1072, -6), (key1151, -6), (key1167, -6), (key1151, -6), (key1016, 6), (key1124, 6), (key1167, 6), (key1124, 6)]

def rawRow10331 : Integer.Sparse Key := [(key1072, -6), (key1167, -6), (key1151, -6), (key1151, -6), (key1016, 6), (key1167, 6), (key1124, 6), (key1124, 6)]

def rawRow10332 : Integer.Sparse Key := [(key1151, -6), (key1072, -6), (key1151, -6), (key1167, -6), (key1124, 6), (key1016, 6), (key1124, 6), (key1167, 6)]

def rawRow10333 : Integer.Sparse Key := [(key1151, -6), (key1072, -6), (key1167, -6), (key1151, -6), (key1124, 6), (key1016, 6), (key1167, 6), (key1124, 6)]

def rawRow10334 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1072, -6), (key1167, -6), (key1124, 6), (key1124, 6), (key1016, 6), (key1167, 6)]

def rawRow10335 : Integer.Sparse Key := [(key1151, -6), (key1151, -6), (key1167, -6), (key1072, -6), (key1124, 6), (key1124, 6), (key1167, 6), (key1016, 6)]

def rawRow10336 : Integer.Sparse Key := [(key1151, -6), (key1167, -6), (key1072, -6), (key1151, -6), (key1124, 6), (key1167, 6), (key1016, 6), (key1124, 6)]

def rawRow10337 : Integer.Sparse Key := [(key1151, -6), (key1167, -6), (key1151, -6), (key1072, -6), (key1124, 6), (key1167, 6), (key1124, 6), (key1016, 6)]

def rawRow10338 : Integer.Sparse Key := [(key1167, -6), (key1072, -6), (key1151, -6), (key1151, -6), (key1167, 6), (key1016, 6), (key1124, 6), (key1124, 6)]

def rawRow10339 : Integer.Sparse Key := [(key1167, -6), (key1151, -6), (key1072, -6), (key1151, -6), (key1167, 6), (key1124, 6), (key1016, 6), (key1124, 6)]

def rawRow10340 : Integer.Sparse Key := [(key1167, -6), (key1151, -6), (key1151, -6), (key1072, -6), (key1167, 6), (key1124, 6), (key1124, 6), (key1016, 6)]

def rawRow10341 : Integer.Sparse Key := [(key1004, -2), (key1008, -2), (key1008, -2), (key1117, -2), (key1157, -2), (key1157, -2), (key1195, -2), (key1195, -2), (key1214, -2), (key1214, -2), (key1216, -2), (key1216, -2), (key1004, 2), (key1021, 2), (key1021, 2), (key1039, 2), (key1078, 2), (key1078, 2), (key1201, 2), (key1201, 2), (key1214, 2), (key1214, 2), (key1225, 2), (key1225, 2)]

def rawRow10342 : Integer.Sparse Key := [(key1008, -2), (key1004, -2), (key1008, -2), (key1157, -2), (key1117, -2), (key1157, -2), (key1214, -2), (key1216, -2), (key1195, -2), (key1216, -2), (key1195, -2), (key1214, -2), (key1021, 2), (key1004, 2), (key1021, 2), (key1078, 2), (key1039, 2), (key1078, 2), (key1214, 2), (key1225, 2), (key1201, 2), (key1225, 2), (key1201, 2), (key1214, 2)]

def rawRow10343 : Integer.Sparse Key := [(key1008, -2), (key1008, -2), (key1004, -2), (key1157, -2), (key1157, -2), (key1117, -2), (key1216, -2), (key1214, -2), (key1216, -2), (key1195, -2), (key1214, -2), (key1195, -2), (key1021, 2), (key1021, 2), (key1004, 2), (key1078, 2), (key1078, 2), (key1039, 2), (key1225, 2), (key1214, 2), (key1225, 2), (key1201, 2), (key1214, 2), (key1201, 2)]

def rawRow10344 : Integer.Sparse Key := [(key1117, -2), (key1195, -2), (key1195, -2), (key1004, -2), (key1214, -2), (key1214, -2), (key1008, -2), (key1008, -2), (key1157, -2), (key1157, -2), (key1216, -2), (key1216, -2), (key1039, 2), (key1201, 2), (key1201, 2), (key1004, 2), (key1214, 2), (key1214, 2), (key1021, 2), (key1021, 2), (key1078, 2), (key1078, 2), (key1225, 2), (key1225, 2)]

def rawRow10345 : Integer.Sparse Key := [(key1195, -2), (key1117, -2), (key1195, -2), (key1214, -2), (key1004, -2), (key1214, -2), (key1157, -2), (key1216, -2), (key1008, -2), (key1216, -2), (key1008, -2), (key1157, -2), (key1201, 2), (key1039, 2), (key1201, 2), (key1214, 2), (key1004, 2), (key1214, 2), (key1078, 2), (key1225, 2), (key1021, 2), (key1225, 2), (key1021, 2), (key1078, 2)]

def rawRow10346 : Integer.Sparse Key := [(key1195, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1214, -2), (key1004, -2), (key1216, -2), (key1157, -2), (key1216, -2), (key1008, -2), (key1157, -2), (key1008, -2), (key1201, 2), (key1201, 2), (key1039, 2), (key1214, 2), (key1214, 2), (key1004, 2), (key1225, 2), (key1078, 2), (key1225, 2), (key1021, 2), (key1078, 2), (key1021, 2)]

def rawRow10347 : Integer.Sparse Key := [(key1157, -2), (key1214, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1216, -2), (key1004, -2), (key1008, -2), (key1117, -2), (key1157, -2), (key1195, -2), (key1214, -2), (key1078, 2), (key1214, 2), (key1225, 2), (key1021, 2), (key1201, 2), (key1225, 2), (key1004, 2), (key1021, 2), (key1039, 2), (key1078, 2), (key1201, 2), (key1214, 2)]

def rawRow10348 : Integer.Sparse Key := [(key1157, -2), (key1216, -2), (key1214, -2), (key1008, -2), (key1216, -2), (key1195, -2), (key1008, -2), (key1004, -2), (key1157, -2), (key1117, -2), (key1214, -2), (key1195, -2), (key1078, 2), (key1225, 2), (key1214, 2), (key1021, 2), (key1225, 2), (key1201, 2), (key1021, 2), (key1004, 2), (key1078, 2), (key1039, 2), (key1214, 2), (key1201, 2)]

def rawRow10349 : Integer.Sparse Key := [(key1214, -2), (key1157, -2), (key1216, -2), (key1195, -2), (key1008, -2), (key1216, -2), (key1117, -2), (key1195, -2), (key1004, -2), (key1214, -2), (key1008, -2), (key1157, -2), (key1214, 2), (key1078, 2), (key1225, 2), (key1201, 2), (key1021, 2), (key1225, 2), (key1039, 2), (key1201, 2), (key1004, 2), (key1214, 2), (key1021, 2), (key1078, 2)]

def rawRow10350 : Integer.Sparse Key := [(key1214, -2), (key1216, -2), (key1157, -2), (key1195, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1117, -2), (key1214, -2), (key1004, -2), (key1157, -2), (key1008, -2), (key1214, 2), (key1225, 2), (key1078, 2), (key1201, 2), (key1225, 2), (key1021, 2), (key1201, 2), (key1039, 2), (key1214, 2), (key1004, 2), (key1078, 2), (key1021, 2)]

def rawRow10351 : Integer.Sparse Key := [(key1216, -2), (key1157, -2), (key1214, -2), (key1216, -2), (key1008, -2), (key1195, -2), (key1157, -2), (key1214, -2), (key1008, -2), (key1195, -2), (key1004, -2), (key1117, -2), (key1225, 2), (key1078, 2), (key1214, 2), (key1225, 2), (key1021, 2), (key1201, 2), (key1078, 2), (key1214, 2), (key1021, 2), (key1201, 2), (key1004, 2), (key1039, 2)]

def rawRow10352 : Integer.Sparse Key := [(key1216, -2), (key1214, -2), (key1157, -2), (key1216, -2), (key1195, -2), (key1008, -2), (key1214, -2), (key1157, -2), (key1195, -2), (key1008, -2), (key1117, -2), (key1004, -2), (key1225, 2), (key1214, 2), (key1078, 2), (key1225, 2), (key1201, 2), (key1021, 2), (key1214, 2), (key1078, 2), (key1201, 2), (key1021, 2), (key1039, 2), (key1004, 2)]

def rawRow10353 : Integer.Sparse Key := [(key1021, -2), (key1021, -2), (key1023, -2), (key1129, -2), (key1129, -2), (key1176, -2), (key1201, -2), (key1202, -2), (key1201, -2), (key1225, -2), (key1202, -2), (key1225, -2), (key1008, 2), (key1008, 2), (key1023, 2), (key1043, 2), (key1043, 2), (key1081, 2), (key1195, 2), (key1202, 2), (key1195, 2), (key1216, 2), (key1202, 2), (key1216, 2)]

def rawRow10354 : Integer.Sparse Key := [(key1021, -2), (key1023, -2), (key1021, -2), (key1129, -2), (key1176, -2), (key1129, -2), (key1202, -2), (key1201, -2), (key1225, -2), (key1201, -2), (key1225, -2), (key1202, -2), (key1008, 2), (key1023, 2), (key1008, 2), (key1043, 2), (key1081, 2), (key1043, 2), (key1202, 2), (key1195, 2), (key1216, 2), (key1195, 2), (key1216, 2), (key1202, 2)]

def rawRow10355 : Integer.Sparse Key := [(key1023, -2), (key1021, -2), (key1021, -2), (key1176, -2), (key1129, -2), (key1129, -2), (key1225, -2), (key1225, -2), (key1202, -2), (key1202, -2), (key1201, -2), (key1201, -2), (key1023, 2), (key1008, 2), (key1008, 2), (key1081, 2), (key1043, 2), (key1043, 2), (key1216, 2), (key1216, 2), (key1202, 2), (key1202, 2), (key1195, 2), (key1195, 2)]

def rawRow10356 : Integer.Sparse Key := [(key1129, -2), (key1201, -2), (key1202, -2), (key1021, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1023, -2), (key1129, -2), (key1176, -2), (key1202, -2), (key1225, -2), (key1043, 2), (key1195, 2), (key1202, 2), (key1008, 2), (key1195, 2), (key1216, 2), (key1008, 2), (key1023, 2), (key1043, 2), (key1081, 2), (key1202, 2), (key1216, 2)]

def rawRow10357 : Integer.Sparse Key := [(key1129, -2), (key1202, -2), (key1201, -2), (key1021, -2), (key1225, -2), (key1201, -2), (key1023, -2), (key1021, -2), (key1176, -2), (key1129, -2), (key1225, -2), (key1202, -2), (key1043, 2), (key1202, 2), (key1195, 2), (key1008, 2), (key1216, 2), (key1195, 2), (key1023, 2), (key1008, 2), (key1081, 2), (key1043, 2), (key1216, 2), (key1202, 2)]

def rawRow10358 : Integer.Sparse Key := [(key1201, -2), (key1129, -2), (key1202, -2), (key1201, -2), (key1021, -2), (key1225, -2), (key1129, -2), (key1202, -2), (key1021, -2), (key1225, -2), (key1023, -2), (key1176, -2), (key1195, 2), (key1043, 2), (key1202, 2), (key1195, 2), (key1008, 2), (key1216, 2), (key1043, 2), (key1202, 2), (key1008, 2), (key1216, 2), (key1023, 2), (key1081, 2)]

def rawRow10359 : Integer.Sparse Key := [(key1201, -2), (key1202, -2), (key1129, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1202, -2), (key1129, -2), (key1225, -2), (key1021, -2), (key1176, -2), (key1023, -2), (key1195, 2), (key1202, 2), (key1043, 2), (key1195, 2), (key1216, 2), (key1008, 2), (key1202, 2), (key1043, 2), (key1216, 2), (key1008, 2), (key1081, 2), (key1023, 2)]

def rawRow10360 : Integer.Sparse Key := [(key1202, -2), (key1129, -2), (key1201, -2), (key1225, -2), (key1021, -2), (key1201, -2), (key1176, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1021, -2), (key1129, -2), (key1202, 2), (key1043, 2), (key1195, 2), (key1216, 2), (key1008, 2), (key1195, 2), (key1081, 2), (key1216, 2), (key1023, 2), (key1202, 2), (key1008, 2), (key1043, 2)]

def rawRow10361 : Integer.Sparse Key := [(key1202, -2), (key1201, -2), (key1129, -2), (key1225, -2), (key1201, -2), (key1021, -2), (key1225, -2), (key1176, -2), (key1202, -2), (key1023, -2), (key1129, -2), (key1021, -2), (key1202, 2), (key1195, 2), (key1043, 2), (key1216, 2), (key1195, 2), (key1008, 2), (key1216, 2), (key1081, 2), (key1202, 2), (key1023, 2), (key1043, 2), (key1008, 2)]

def rawRow10362 : Integer.Sparse Key := [(key1176, -2), (key1225, -2), (key1225, -2), (key1023, -2), (key1202, -2), (key1202, -2), (key1021, -2), (key1021, -2), (key1129, -2), (key1129, -2), (key1201, -2), (key1201, -2), (key1081, 2), (key1216, 2), (key1216, 2), (key1023, 2), (key1202, 2), (key1202, 2), (key1008, 2), (key1008, 2), (key1043, 2), (key1043, 2), (key1195, 2), (key1195, 2)]

def rawRow10363 : Integer.Sparse Key := [(key1225, -2), (key1176, -2), (key1225, -2), (key1202, -2), (key1023, -2), (key1202, -2), (key1129, -2), (key1201, -2), (key1021, -2), (key1201, -2), (key1021, -2), (key1129, -2), (key1216, 2), (key1081, 2), (key1216, 2), (key1202, 2), (key1023, 2), (key1202, 2), (key1043, 2), (key1195, 2), (key1008, 2), (key1195, 2), (key1008, 2), (key1043, 2)]

def rawRow10364 : Integer.Sparse Key := [(key1225, -2), (key1225, -2), (key1176, -2), (key1202, -2), (key1202, -2), (key1023, -2), (key1201, -2), (key1129, -2), (key1201, -2), (key1021, -2), (key1129, -2), (key1021, -2), (key1216, 2), (key1216, 2), (key1081, 2), (key1202, 2), (key1202, 2), (key1023, 2), (key1195, 2), (key1043, 2), (key1195, 2), (key1008, 2), (key1043, 2), (key1008, 2)]

def rawRow10365 : Integer.Sparse Key := [(key10, 2), (key13, 2), (key13, 2), (key93, 2), (key158, 2), (key158, 2), (key169, 2), (key169, 2), (key189, 2), (key189, 2), (key192, 2), (key192, 2), (key13, -2), (key13, -2), (key15, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key163, -2), (key163, -2), (key170, -2), (key192, -2), (key192, -2)]

def rawRow10366 : Integer.Sparse Key := [(key13, 2), (key10, 2), (key13, 2), (key158, 2), (key93, 2), (key158, 2), (key189, 2), (key192, 2), (key169, 2), (key192, 2), (key169, 2), (key189, 2), (key13, -2), (key15, -2), (key13, -2), (key158, -2), (key163, -2), (key96, -2), (key163, -2), (key96, -2), (key158, -2), (key192, -2), (key170, -2), (key192, -2)]

def rawRow10367 : Integer.Sparse Key := [(key13, 2), (key13, 2), (key10, 2), (key158, 2), (key158, 2), (key93, 2), (key192, 2), (key189, 2), (key192, 2), (key169, 2), (key189, 2), (key169, 2), (key15, -2), (key13, -2), (key13, -2), (key163, -2), (key158, -2), (key163, -2), (key96, -2), (key158, -2), (key96, -2), (key192, -2), (key192, -2), (key170, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10368 : Integer.Sparse Key := [(key93, 2), (key158, 2), (key158, 2), (key10, 2), (key189, 2), (key189, 2), (key13, 2), (key13, 2), (key158, 2), (key158, 2), (key192, 2), (key192, 2), (key96, -2), (key96, -2), (key170, -2), (key13, -2), (key13, -2), (key158, -2), (key158, -2), (key192, -2), (key192, -2), (key15, -2), (key163, -2), (key163, -2)]

def rawRow10369 : Integer.Sparse Key := [(key158, 2), (key93, 2), (key158, 2), (key189, 2), (key10, 2), (key189, 2), (key158, 2), (key192, 2), (key13, 2), (key192, 2), (key13, 2), (key158, 2), (key96, -2), (key170, -2), (key96, -2), (key158, -2), (key192, -2), (key13, -2), (key192, -2), (key13, -2), (key158, -2), (key163, -2), (key15, -2), (key163, -2)]

def rawRow10370 : Integer.Sparse Key := [(key158, 2), (key158, 2), (key93, 2), (key189, 2), (key189, 2), (key10, 2), (key192, 2), (key158, 2), (key192, 2), (key13, 2), (key158, 2), (key13, 2), (key170, -2), (key96, -2), (key96, -2), (key192, -2), (key158, -2), (key192, -2), (key13, -2), (key158, -2), (key13, -2), (key163, -2), (key163, -2), (key15, -2)]

def rawRow10371 : Integer.Sparse Key := [(key169, 2), (key189, 2), (key192, 2), (key13, 2), (key158, 2), (key192, 2), (key10, 2), (key13, 2), (key93, 2), (key158, 2), (key169, 2), (key189, 2), (key158, -2), (key163, -2), (key192, -2), (key13, -2), (key15, -2), (key96, -2), (key163, -2), (key170, -2), (key192, -2), (key13, -2), (key96, -2), (key158, -2)]

def rawRow10372 : Integer.Sparse Key := [(key169, 2), (key192, 2), (key189, 2), (key13, 2), (key192, 2), (key158, 2), (key13, 2), (key10, 2), (key158, 2), (key93, 2), (key189, 2), (key169, 2), (key163, -2), (key158, -2), (key192, -2), (key15, -2), (key13, -2), (key163, -2), (key96, -2), (key192, -2), (key170, -2), (key13, -2), (key158, -2), (key96, -2)]

def rawRow10373 : Integer.Sparse Key := [(key189, 2), (key169, 2), (key192, 2), (key158, 2), (key13, 2), (key192, 2), (key93, 2), (key158, 2), (key10, 2), (key189, 2), (key13, 2), (key158, 2), (key158, -2), (key192, -2), (key163, -2), (key96, -2), (key170, -2), (key13, -2), (key192, -2), (key15, -2), (key163, -2), (key96, -2), (key13, -2), (key158, -2)]

def rawRow10374 : Integer.Sparse Key := [(key189, 2), (key192, 2), (key169, 2), (key158, 2), (key192, 2), (key13, 2), (key158, 2), (key93, 2), (key189, 2), (key10, 2), (key158, 2), (key13, 2), (key192, -2), (key158, -2), (key163, -2), (key170, -2), (key96, -2), (key192, -2), (key13, -2), (key163, -2), (key15, -2), (key96, -2), (key158, -2), (key13, -2)]

def rawRow10375 : Integer.Sparse Key := [(key192, 2), (key169, 2), (key189, 2), (key192, 2), (key13, 2), (key158, 2), (key169, 2), (key189, 2), (key13, 2), (key158, 2), (key10, 2), (key93, 2), (key163, -2), (key192, -2), (key158, -2), (key163, -2), (key192, -2), (key15, -2), (key170, -2), (key13, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2)]

def rawRow10376 : Integer.Sparse Key := [(key192, 2), (key189, 2), (key169, 2), (key192, 2), (key158, 2), (key13, 2), (key189, 2), (key169, 2), (key158, 2), (key13, 2), (key93, 2), (key10, 2), (key192, -2), (key163, -2), (key158, -2), (key192, -2), (key163, -2), (key170, -2), (key15, -2), (key96, -2), (key13, -2), (key158, -2), (key96, -2), (key13, -2)]

def rawRow10377 : Integer.Sparse Key := [(key13, 2), (key13, 2), (key15, 2), (key96, 2), (key96, 2), (key170, 2), (key158, 2), (key163, 2), (key158, 2), (key192, 2), (key163, 2), (key192, 2), (key10, -2), (key13, -2), (key13, -2), (key93, -2), (key96, -2), (key93, -2), (key158, -2), (key96, -2), (key158, -2), (key169, -2), (key169, -2), (key189, -2)]

def rawRow10378 : Integer.Sparse Key := [(key13, 2), (key15, 2), (key13, 2), (key96, 2), (key170, 2), (key96, 2), (key163, 2), (key158, 2), (key192, 2), (key158, 2), (key192, 2), (key163, 2), (key13, -2), (key10, -2), (key13, -2), (key96, -2), (key93, -2), (key158, -2), (key93, -2), (key158, -2), (key96, -2), (key169, -2), (key189, -2), (key169, -2)]

def rawRow10379 : Integer.Sparse Key := [(key15, 2), (key13, 2), (key13, 2), (key170, 2), (key96, 2), (key96, 2), (key192, 2), (key192, 2), (key163, 2), (key163, 2), (key158, 2), (key158, 2), (key13, -2), (key13, -2), (key10, -2), (key158, -2), (key158, -2), (key96, -2), (key96, -2), (key93, -2), (key93, -2), (key189, -2), (key169, -2), (key169, -2)]

def rawRow10380 : Integer.Sparse Key := [(key96, 2), (key158, 2), (key163, 2), (key13, 2), (key158, 2), (key192, 2), (key13, 2), (key15, 2), (key96, 2), (key170, 2), (key163, 2), (key192, 2), (key93, -2), (key96, -2), (key158, -2), (key10, -2), (key13, -2), (key93, -2), (key158, -2), (key169, -2), (key189, -2), (key13, -2), (key96, -2), (key158, -2)]

def rawRow10381 : Integer.Sparse Key := [(key96, 2), (key163, 2), (key158, 2), (key13, 2), (key192, 2), (key158, 2), (key15, 2), (key13, 2), (key170, 2), (key96, 2), (key192, 2), (key163, 2), (key96, -2), (key93, -2), (key158, -2), (key13, -2), (key10, -2), (key158, -2), (key93, -2), (key189, -2), (key169, -2), (key13, -2), (key158, -2), (key96, -2)]

def rawRow10382 : Integer.Sparse Key := [(key158, 2), (key96, 2), (key163, 2), (key158, 2), (key13, 2), (key192, 2), (key96, 2), (key163, 2), (key13, 2), (key192, 2), (key15, 2), (key170, 2), (key93, -2), (key158, -2), (key96, -2), (key93, -2), (key158, -2), (key10, -2), (key189, -2), (key13, -2), (key158, -2), (key96, -2), (key13, -2), (key158, -2)]

def rawRow10383 : Integer.Sparse Key := [(key158, 2), (key163, 2), (key96, 2), (key158, 2), (key192, 2), (key13, 2), (key163, 2), (key96, 2), (key192, 2), (key13, 2), (key170, 2), (key15, 2), (key158, -2), (key93, -2), (key96, -2), (key158, -2), (key93, -2), (key189, -2), (key10, -2), (key158, -2), (key13, -2), (key96, -2), (key158, -2), (key13, -2)]

def rawRow10384 : Integer.Sparse Key := [(key163, 2), (key96, 2), (key158, 2), (key192, 2), (key13, 2), (key158, 2), (key170, 2), (key192, 2), (key15, 2), (key163, 2), (key13, 2), (key96, 2), (key96, -2), (key158, -2), (key93, -2), (key169, -2), (key189, -2), (key13, -2), (key158, -2), (key10, -2), (key93, -2), (key158, -2), (key13, -2), (key96, -2)]

def rawRow10385 : Integer.Sparse Key := [(key163, 2), (key158, 2), (key96, 2), (key192, 2), (key158, 2), (key13, 2), (key192, 2), (key170, 2), (key163, 2), (key15, 2), (key96, 2), (key13, 2), (key158, -2), (key96, -2), (key93, -2), (key189, -2), (key169, -2), (key158, -2), (key13, -2), (key93, -2), (key10, -2), (key158, -2), (key96, -2), (key13, -2)]

def rawRow10386 : Integer.Sparse Key := [(key170, 2), (key192, 2), (key192, 2), (key15, 2), (key163, 2), (key163, 2), (key13, 2), (key13, 2), (key96, 2), (key96, 2), (key158, 2), (key158, 2), (key169, -2), (key169, -2), (key189, -2), (key13, -2), (key13, -2), (key96, -2), (key96, -2), (key158, -2), (key158, -2), (key10, -2), (key93, -2), (key93, -2)]

def rawRow10387 : Integer.Sparse Key := [(key192, 2), (key170, 2), (key192, 2), (key163, 2), (key15, 2), (key163, 2), (key96, 2), (key158, 2), (key13, 2), (key158, 2), (key13, 2), (key96, 2), (key169, -2), (key189, -2), (key169, -2), (key96, -2), (key158, -2), (key13, -2), (key158, -2), (key13, -2), (key96, -2), (key93, -2), (key10, -2), (key93, -2)]

def rawRow10388 : Integer.Sparse Key := [(key192, 2), (key192, 2), (key170, 2), (key163, 2), (key163, 2), (key15, 2), (key158, 2), (key96, 2), (key158, 2), (key13, 2), (key96, 2), (key13, 2), (key189, -2), (key169, -2), (key169, -2), (key158, -2), (key96, -2), (key158, -2), (key13, -2), (key96, -2), (key13, -2), (key93, -2), (key93, -2), (key10, -2)]

def rawRow10389 : Integer.Sparse Key := [(key2420, 2), (key2427, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2495, 2), (key2427, 2), (key2427, 2), (key2495, 2), (key2495, 2), (key2504, 2), (key2504, 2), (key2427, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2504, -2)]

def rawRow10390 : Integer.Sparse Key := [(key2427, 2), (key2420, 2), (key2427, 2), (key2495, 2), (key2420, 2), (key2495, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2495, 2), (key2427, -2), (key2438, -2), (key2427, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2504, -2), (key2438, -2), (key2504, -2)]

def rawRow10391 : Integer.Sparse Key := [(key2427, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2495, 2), (key2420, 2), (key2504, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2495, 2), (key2427, 2), (key2438, -2), (key2427, -2), (key2427, -2), (key2504, -2), (key2495, -2), (key2504, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2504, -2), (key2504, -2), (key2438, -2)]

def rawRow10392 : Integer.Sparse Key := [(key2495, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2420, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2427, 2), (key2495, 2), (key2495, -2), (key2504, -2), (key2504, -2), (key2427, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2504, -2), (key2427, -2), (key2427, -2), (key2495, -2)]

def rawRow10393 : Integer.Sparse Key := [(key2495, 2), (key2504, 2), (key2495, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2420, 2), (key2495, 2), (key2420, 2), (key2495, 2), (key2427, 2), (key2504, -2), (key2495, -2), (key2504, -2), (key2438, -2), (key2427, -2), (key2504, -2), (key2427, -2), (key2504, -2), (key2438, -2), (key2427, -2), (key2495, -2), (key2427, -2)]

def rawRow10394 : Integer.Sparse Key := [(key2504, 2), (key2495, 2), (key2495, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2495, 2), (key2495, 2), (key2427, 2), (key2427, 2), (key2420, 2), (key2420, 2), (key2504, -2), (key2504, -2), (key2495, -2), (key2504, -2), (key2504, -2), (key2438, -2), (key2438, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2427, -2)]

def rawRow10395 : Integer.Sparse Key := [(key2427, 2), (key2427, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2438, 2), (key2427, 2), (key2504, 2), (key2438, 2), (key2504, 2), (key2420, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2495, -2)]

def rawRow10396 : Integer.Sparse Key := [(key2427, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2438, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2504, 2), (key2438, 2), (key2427, -2), (key2420, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2495, -2), (key2427, -2)]

def rawRow10397 : Integer.Sparse Key := [(key2438, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2427, 2), (key2427, 2), (key2504, 2), (key2504, 2), (key2438, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2427, -2), (key2427, -2), (key2420, -2), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2495, -2), (key2427, -2), (key2427, -2)]

def rawRow10398 : Integer.Sparse Key := [(key2504, 2), (key2504, 2), (key2504, 2), (key2438, 2), (key2438, 2), (key2438, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2427, 2), (key2495, -2), (key2495, -2), (key2495, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2427, -2), (key2420, -2), (key2420, -2), (key2420, -2)]

def rawRow10399 : Integer.Sparse Key := [(key1045, -24), (key1045, 6), (key1045, 6), (key1131, 6), (key1131, 6)]

def rawRow10400 : Integer.Sparse Key := [(key1045, -24), (key1045, 6), (key1131, 6), (key1045, 6), (key1131, 6)]

def rawRow10401 : Integer.Sparse Key := [(key1045, -24), (key1045, 6), (key1131, 6), (key1131, 6), (key1045, 6)]

def rawRow10402 : Integer.Sparse Key := [(key1045, -24), (key1131, 6), (key1045, 6), (key1045, 6), (key1131, 6)]

def rawRow10403 : Integer.Sparse Key := [(key1045, -24), (key1131, 6), (key1045, 6), (key1131, 6), (key1045, 6)]

def rawRow10404 : Integer.Sparse Key := [(key1045, -24), (key1131, 6), (key1131, 6), (key1045, 6), (key1045, 6)]

def rawRow10405 : Integer.Sparse Key := [(key1131, -24), (key1045, 6), (key1045, 6), (key1045, 6), (key1131, 6)]

def rawRow10406 : Integer.Sparse Key := [(key1131, -24), (key1045, 6), (key1045, 6), (key1131, 6), (key1045, 6)]

def rawRow10407 : Integer.Sparse Key := [(key1131, -24), (key1045, 6), (key1131, 6), (key1045, 6), (key1045, 6)]

def rawRow10408 : Integer.Sparse Key := [(key1131, -24), (key1131, 6), (key1045, 6), (key1045, 6), (key1045, 6)]

def rawRow10409 : Integer.Sparse Key := [(key1050, -6), (key1050, -6), (key1058, -6), (key1058, -6), (key1050, 2), (key1050, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1136, 2), (key1136, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1138, 2)]

def rawRow10410 : Integer.Sparse Key := [(key1050, -6), (key1058, -6), (key1050, -6), (key1058, -6), (key1050, 2), (key1058, 2), (key1050, 2), (key1136, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1138, 2), (key1058, 2), (key1138, 2)]

def rawRow10411 : Integer.Sparse Key := [(key1058, -6), (key1050, -6), (key1050, -6), (key1058, -6), (key1058, 2), (key1050, 2), (key1050, 2), (key1138, 2), (key1136, 2), (key1138, 2), (key1050, 2), (key1136, 2), (key1050, 2), (key1138, 2), (key1138, 2), (key1058, 2)]

def rawRow10412 : Integer.Sparse Key := [(key1050, -6), (key1058, -6), (key1058, -6), (key1050, -6), (key1136, 2), (key1138, 2), (key1138, 2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1050, 2), (key1050, 2), (key1136, 2)]

def rawRow10413 : Integer.Sparse Key := [(key1058, -6), (key1050, -6), (key1058, -6), (key1050, -6), (key1138, 2), (key1136, 2), (key1138, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1050, 2), (key1136, 2), (key1050, 2)]

def rawRow10414 : Integer.Sparse Key := [(key1058, -6), (key1058, -6), (key1050, -6), (key1050, -6), (key1138, 2), (key1138, 2), (key1136, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1136, 2), (key1050, 2), (key1050, 2)]

def rawRow10415 : Integer.Sparse Key := [(key1136, -6), (key1138, -6), (key1138, -6), (key1138, -6), (key1050, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1138, 2)]

def rawRow10416 : Integer.Sparse Key := [(key1138, -6), (key1136, -6), (key1138, -6), (key1138, -6), (key1058, 2), (key1050, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1138, 2), (key1058, 2)]

def rawRow10417 : Integer.Sparse Key := [(key1138, -6), (key1138, -6), (key1136, -6), (key1138, -6), (key1058, 2), (key1058, 2), (key1050, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1138, 2), (key1058, 2), (key1058, 2)]

def rawRow10418 : Integer.Sparse Key := [(key1138, -6), (key1138, -6), (key1138, -6), (key1136, -6), (key1138, 2), (key1138, 2), (key1138, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1058, 2), (key1050, 2), (key1050, 2), (key1050, 2)]

def rawRow10419 : Integer.Sparse Key := [(key2677, -6), (key3045, -6), (key3094, -6), (key3094, -6), (key3045, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3122, 2)]

def rawRow10420 : Integer.Sparse Key := [(key2677, -6), (key3094, -6), (key3045, -6), (key3094, -6), (key3059, 2), (key3045, 2), (key3059, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3122, 2), (key3059, 2), (key3094, 2)]

def rawRow10421 : Integer.Sparse Key := [(key2677, -6), (key3094, -6), (key3094, -6), (key3045, -6), (key3059, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3045, 2), (key3122, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3094, 2), (key3059, 2)]

def rawRow10422 : Integer.Sparse Key := [(key2811, -6), (key2677, -6), (key3045, -6), (key3094, -6), (key3094, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3059, 2), (key3122, 2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

def rawRow10423 : Integer.Sparse Key := [(key2811, -6), (key2677, -6), (key3094, -6), (key3045, -6), (key3094, 2), (key3122, 2), (key3094, 2), (key3059, 2), (key3122, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

def rawRow10424 : Integer.Sparse Key := [(key2811, -6), (key2811, -6), (key2677, -6), (key3045, -6), (key3122, 2), (key3094, 2), (key3094, 2), (key3122, 2), (key3059, 2), (key3059, 2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

def rawRow10425 : Integer.Sparse Key := [(key2708, -6), (key2708, -6), (key2708, -6), (key2861, -6), (key2677, 2), (key2677, 2), (key2708, 2), (key2677, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3059, 2), (key3094, 2)]

def rawRow10426 : Integer.Sparse Key := [(key2708, -6), (key2708, -6), (key2861, -6), (key2708, -6), (key2677, 2), (key2708, 2), (key2677, 2), (key2677, 2), (key3094, 2), (key3045, 2), (key3059, 2), (key3045, 2), (key3094, 2), (key3045, 2), (key3094, 2), (key3059, 2)]

def rawRow10427 : Integer.Sparse Key := [(key2708, -6), (key2861, -6), (key2708, -6), (key2708, -6), (key2708, 2), (key2677, 2), (key2677, 2), (key2811, 2), (key2677, 2), (key3045, 2), (key3094, 2), (key3094, 2), (key3059, 2), (key3059, 2), (key3045, 2), (key3045, 2)]

def rawRow10428 : Integer.Sparse Key := [(key2861, -6), (key2708, -6), (key2708, -6), (key2708, -6), (key2811, 2), (key2811, 2), (key2811, 2), (key2708, 2), (key2708, 2), (key2708, 2), (key2677, 2), (key2677, 2), (key2677, 2), (key3045, 2), (key3045, 2), (key3045, 2)]

def rawRow10429 : Integer.Sparse Key := [(key2416, -6), (key2416, -6), (key2423, -6), (key2423, -6), (key2416, 2), (key2416, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2489, 2), (key2489, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2491, 2)]

def rawRow10430 : Integer.Sparse Key := [(key2416, -6), (key2423, -6), (key2416, -6), (key2423, -6), (key2416, 2), (key2423, 2), (key2416, 2), (key2489, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2491, 2), (key2423, 2), (key2491, 2)]

def rawRow10431 : Integer.Sparse Key := [(key2423, -6), (key2416, -6), (key2416, -6), (key2423, -6), (key2423, 2), (key2416, 2), (key2416, 2), (key2491, 2), (key2489, 2), (key2491, 2), (key2416, 2), (key2489, 2), (key2416, 2), (key2491, 2), (key2491, 2), (key2423, 2)]

def rawRow10432 : Integer.Sparse Key := [(key2416, -6), (key2423, -6), (key2423, -6), (key2416, -6), (key2489, 2), (key2491, 2), (key2491, 2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2416, 2), (key2416, 2), (key2489, 2)]

def rawRow10433 : Integer.Sparse Key := [(key2423, -6), (key2416, -6), (key2423, -6), (key2416, -6), (key2491, 2), (key2489, 2), (key2491, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2416, 2), (key2489, 2), (key2416, 2)]

def rawRow10434 : Integer.Sparse Key := [(key2423, -6), (key2423, -6), (key2416, -6), (key2416, -6), (key2491, 2), (key2491, 2), (key2489, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2489, 2), (key2416, 2), (key2416, 2)]

def rawRow10435 : Integer.Sparse Key := [(key2489, -6), (key2491, -6), (key2491, -6), (key2491, -6), (key2416, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2491, 2)]

def rawRow10436 : Integer.Sparse Key := [(key2491, -6), (key2489, -6), (key2491, -6), (key2491, -6), (key2423, 2), (key2416, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2491, 2), (key2423, 2)]

def rawRow10437 : Integer.Sparse Key := [(key2491, -6), (key2491, -6), (key2489, -6), (key2491, -6), (key2423, 2), (key2423, 2), (key2416, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2491, 2), (key2423, 2), (key2423, 2)]

def rawRow10438 : Integer.Sparse Key := [(key2491, -6), (key2491, -6), (key2491, -6), (key2489, -6), (key2491, 2), (key2491, 2), (key2491, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2423, 2), (key2416, 2), (key2416, 2), (key2416, 2)]

def rawRow10439 : Integer.Sparse Key := [(key2681, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2815, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2681, 1), (key2681, 1), (key2712, 1), (key2712, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2817, 1), (key2817, 1), (key2712, 1), (key2712, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2817, 1), (key2817, 1), (key2863, 1), (key2863, 1)]

def rawRow10440 : Integer.Sparse Key := [(key2681, -2), (key2688, -2), (key2681, -2), (key2815, -2), (key2817, -2), (key2681, -2), (key2817, -2), (key2681, -2), (key2815, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2712, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2714, 1), (key2817, 1)]

def rawRow10441 : Integer.Sparse Key := [(key2688, -2), (key2681, -2), (key2681, -2), (key2817, -2), (key2815, -2), (key2817, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2714, 1), (key2712, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2817, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2712, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2817, 1), (key2714, 1)]

def rawRow10442 : Integer.Sparse Key := [(key2815, -2), (key2817, -2), (key2817, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2815, 1), (key2817, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2712, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2712, 1), (key2815, 1)]

def rawRow10443 : Integer.Sparse Key := [(key2817, -2), (key2815, -2), (key2817, -2), (key2688, -2), (key2681, -2), (key2817, -2), (key2681, -2), (key2817, -2), (key2688, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2817, 1), (key2815, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2815, 1), (key2712, 1)]

def rawRow10444 : Integer.Sparse Key := [(key2817, -2), (key2817, -2), (key2815, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2681, -2), (key2863, 1), (key2863, 1), (key2817, 1), (key2817, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2712, 1), (key2712, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2712, 1), (key2712, 1), (key2681, 1), (key2681, 1)]

def rawRow10445 : Integer.Sparse Key := [(key2712, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2714, -2), (key2712, -2), (key2863, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2863, -2), (key2681, 1), (key2688, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2714, 1), (key2817, 1)]

def rawRow10446 : Integer.Sparse Key := [(key2714, -2), (key2712, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2863, -2), (key2712, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2688, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2714, 1)]

def rawRow10447 : Integer.Sparse Key := [(key2714, -2), (key2714, -2), (key2712, -2), (key2863, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2712, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1)]

def rawRow10448 : Integer.Sparse Key := [(key2863, -2), (key2863, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2714, -2), (key2712, -2), (key2712, -2), (key2712, -2), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1)]

def rawRow10449 : Integer.Sparse Key := [(key2412, -24), (key3031, 6), (key3031, 6), (key3118, 6), (key3118, 6)]

def rawRow10450 : Integer.Sparse Key := [(key2412, -24), (key3031, 6), (key3118, 6), (key3031, 6), (key3118, 6)]

def rawRow10451 : Integer.Sparse Key := [(key2412, -24), (key3031, 6), (key3118, 6), (key3118, 6), (key3031, 6)]

def rawRow10452 : Integer.Sparse Key := [(key2412, -24), (key3118, 6), (key3031, 6), (key3031, 6), (key3118, 6)]

def rawRow10453 : Integer.Sparse Key := [(key2412, -24), (key3118, 6), (key3031, 6), (key3118, 6), (key3031, 6)]

def rawRow10454 : Integer.Sparse Key := [(key2412, -24), (key3118, 6), (key3118, 6), (key3031, 6), (key3031, 6)]

def rawRow10455 : Integer.Sparse Key := [(key2485, -24), (key2412, 6), (key3031, 6), (key3031, 6), (key3118, 6)]

def rawRow10456 : Integer.Sparse Key := [(key2485, -24), (key2412, 6), (key3031, 6), (key3118, 6), (key3031, 6)]

def rawRow10457 : Integer.Sparse Key := [(key2485, -24), (key2412, 6), (key3118, 6), (key3031, 6), (key3031, 6)]

def rawRow10458 : Integer.Sparse Key := [(key2485, -24), (key2485, 6), (key2412, 6), (key3031, 6), (key3031, 6)]

def rawRow10459 : Integer.Sparse Key := [(key2681, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2712, -2), (key2712, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2714, -2), (key2714, -2), (key2681, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2817, 2)]

def rawRow10460 : Integer.Sparse Key := [(key2681, -2), (key2688, -2), (key2681, -2), (key2712, -2), (key2714, -2), (key2681, -2), (key2714, -2), (key2681, -2), (key2712, -2), (key2714, -2), (key2688, -2), (key2714, -2), (key2681, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2817, 2)]

def rawRow10461 : Integer.Sparse Key := [(key2688, -2), (key2681, -2), (key2681, -2), (key2714, -2), (key2712, -2), (key2714, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2688, 2), (key2681, 2), (key2681, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2817, 2), (key2817, 2), (key2688, 2)]

def rawRow10462 : Integer.Sparse Key := [(key2712, -2), (key2714, -2), (key2714, -2), (key2681, -2), (key2688, -2), (key2681, -2), (key2714, -2), (key2688, -2), (key2714, -2), (key2681, -2), (key2681, -2), (key2712, -2), (key2815, 2), (key2817, 2), (key2817, 2), (key2681, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2817, 2), (key2681, 2), (key2681, 2), (key2815, 2)]

def rawRow10463 : Integer.Sparse Key := [(key2714, -2), (key2712, -2), (key2714, -2), (key2688, -2), (key2681, -2), (key2714, -2), (key2681, -2), (key2714, -2), (key2688, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2817, 2), (key2815, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2817, 2), (key2681, 2), (key2817, 2), (key2688, 2), (key2681, 2), (key2815, 2), (key2681, 2)]

def rawRow10464 : Integer.Sparse Key := [(key2714, -2), (key2714, -2), (key2712, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2688, -2), (key2681, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2817, 2), (key2817, 2), (key2815, 2), (key2817, 2), (key2817, 2), (key2688, 2), (key2688, 2), (key2681, 2), (key2681, 2), (key2815, 2), (key2681, 2), (key2681, 2)]

def rawRow10465 : Integer.Sparse Key := [(key2815, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2817, -2), (key2815, -2), (key2863, -2), (key2817, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2)]

def rawRow10466 : Integer.Sparse Key := [(key2817, -2), (key2815, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2863, -2), (key2815, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2817, -2), (key2714, 2), (key2712, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2863, 2), (key2714, 2)]

def rawRow10467 : Integer.Sparse Key := [(key2817, -2), (key2817, -2), (key2815, -2), (key2863, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2815, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2714, 2), (key2714, 2), (key2712, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2863, 2), (key2714, 2), (key2714, 2)]

def rawRow10468 : Integer.Sparse Key := [(key2863, -2), (key2863, -2), (key2863, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2817, -2), (key2815, -2), (key2815, -2), (key2815, -2), (key2863, 2), (key2863, 2), (key2863, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2714, 2), (key2712, 2), (key2712, 2), (key2712, 2)]

def rawRow10469 : Integer.Sparse Key := [(key1407, -2), (key1407, -2), (key1411, -2), (key1407, -2), (key1407, -2), (key1584, -2), (key1584, -2), (key1585, -2), (key1585, -2), (key1411, -2), (key1585, -2), (key1585, -2), (key1407, 1), (key1407, 1), (key1435, 1), (key1435, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1407, 1), (key1584, 1), (key1584, 1), (key1585, 1), (key1585, 1), (key1435, 1), (key1435, 1), (key1584, 1), (key1584, 1), (key1628, 1), (key1628, 1), (key1436, 1), (key1436, 1), (key1585, 1), (key1585, 1), (key1628, 1), (key1628, 1)]

def rawRow10470 : Integer.Sparse Key := [(key1407, -2), (key1411, -2), (key1407, -2), (key1584, -2), (key1585, -2), (key1407, -2), (key1585, -2), (key1407, -2), (key1584, -2), (key1585, -2), (key1411, -2), (key1585, -2), (key1435, 1), (key1436, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1435, 1), (key1584, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1584, 1), (key1584, 1), (key1628, 1), (key1435, 1), (key1628, 1), (key1435, 1), (key1584, 1), (key1585, 1), (key1628, 1), (key1436, 1), (key1628, 1), (key1436, 1), (key1585, 1)]

def rawRow10471 : Integer.Sparse Key := [(key1411, -2), (key1407, -2), (key1407, -2), (key1585, -2), (key1584, -2), (key1585, -2), (key1407, -2), (key1584, -2), (key1407, -2), (key1585, -2), (key1585, -2), (key1411, -2), (key1436, 1), (key1435, 1), (key1436, 1), (key1407, 1), (key1435, 1), (key1407, 1), (key1585, 1), (key1584, 1), (key1585, 1), (key1407, 1), (key1584, 1), (key1407, 1), (key1628, 1), (key1584, 1), (key1628, 1), (key1435, 1), (key1584, 1), (key1435, 1), (key1628, 1), (key1585, 1), (key1628, 1), (key1436, 1), (key1585, 1), (key1436, 1)]

def rawRow10472 : Integer.Sparse Key := [(key1584, -2), (key1585, -2), (key1585, -2), (key1407, -2), (key1411, -2), (key1407, -2), (key1585, -2), (key1411, -2), (key1585, -2), (key1407, -2), (key1407, -2), (key1584, -2), (key1584, 1), (key1585, 1), (key1584, 1), (key1628, 1), (key1585, 1), (key1628, 1), (key1435, 1), (key1436, 1), (key1435, 1), (key1628, 1), (key1436, 1), (key1628, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1585, 1), (key1407, 1), (key1435, 1), (key1407, 1), (key1584, 1), (key1435, 1), (key1584, 1)]

def rawRow10473 : Integer.Sparse Key := [(key1585, -2), (key1584, -2), (key1585, -2), (key1411, -2), (key1407, -2), (key1585, -2), (key1407, -2), (key1585, -2), (key1411, -2), (key1407, -2), (key1584, -2), (key1407, -2), (key1585, 1), (key1584, 1), (key1628, 1), (key1584, 1), (key1628, 1), (key1585, 1), (key1436, 1), (key1435, 1), (key1628, 1), (key1435, 1), (key1628, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1435, 1), (key1407, 1), (key1584, 1), (key1407, 1), (key1584, 1), (key1435, 1)]

def rawRow10474 : Integer.Sparse Key := [(key1585, -2), (key1585, -2), (key1584, -2), (key1585, -2), (key1585, -2), (key1411, -2), (key1411, -2), (key1407, -2), (key1407, -2), (key1584, -2), (key1407, -2), (key1407, -2), (key1628, 1), (key1628, 1), (key1585, 1), (key1585, 1), (key1584, 1), (key1584, 1), (key1628, 1), (key1628, 1), (key1436, 1), (key1436, 1), (key1435, 1), (key1435, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1407, 1), (key1584, 1), (key1584, 1), (key1435, 1), (key1435, 1), (key1407, 1), (key1407, 1)]

def rawRow10475 : Integer.Sparse Key := [(key1435, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1436, -2), (key1435, -2), (key1628, -2), (key1436, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1628, -2), (key1407, 1), (key1411, 1), (key1407, 1), (key1436, 1), (key1411, 1), (key1436, 1), (key1407, 1), (key1411, 1), (key1407, 1), (key1585, 1), (key1411, 1), (key1585, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1585, 1), (key1411, 1), (key1436, 1), (key1411, 1), (key1585, 1), (key1436, 1), (key1585, 1)]

def rawRow10476 : Integer.Sparse Key := [(key1436, -2), (key1435, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1628, -2), (key1435, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1628, -2), (key1436, -2), (key1411, 1), (key1407, 1), (key1436, 1), (key1407, 1), (key1436, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1411, 1), (key1436, 1), (key1407, 1), (key1585, 1), (key1407, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1411, 1), (key1585, 1), (key1411, 1), (key1585, 1), (key1436, 1)]

def rawRow10477 : Integer.Sparse Key := [(key1436, -2), (key1436, -2), (key1435, -2), (key1628, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1435, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1436, 1), (key1436, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1407, 1), (key1585, 1), (key1585, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1407, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1407, 1), (key1407, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1411, 1), (key1411, 1)]

def rawRow10478 : Integer.Sparse Key := [(key1628, -2), (key1628, -2), (key1628, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1436, -2), (key1435, -2), (key1435, -2), (key1435, -2), (key1585, 1), (key1585, 1), (key1585, 1), (key1585, 1), (key1585, 1), (key1585, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1436, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1411, 1), (key1407, 1), (key1407, 1), (key1407, 1), (key1407, 1), (key1407, 1), (key1407, 1)]

def rawRow10479 : Integer.Sparse Key := [(key2681, 1), (key2681, 1), (key2712, 1), (key2712, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2817, 1), (key2817, 1), (key2712, 1), (key2712, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2817, 1), (key2817, 1), (key2863, 1), (key2863, 1), (key2688, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2714, -2), (key2714, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2863, -2)]

def rawRow10480 : Integer.Sparse Key := [(key2712, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2714, 1), (key2817, 1), (key2714, -2), (key2688, -2), (key2714, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2817, -2)]

def rawRow10481 : Integer.Sparse Key := [(key2714, 1), (key2712, 1), (key2714, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2817, 1), (key2815, 1), (key2817, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2712, 1), (key2815, 1), (key2712, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2714, 1), (key2817, 1), (key2714, 1), (key2714, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2817, -2), (key2688, -2), (key2863, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2817, -2), (key2714, -2)]

def rawRow10482 : Integer.Sparse Key := [(key2815, 1), (key2817, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2863, 1), (key2712, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2863, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2681, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2712, 1), (key2815, 1), (key2817, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2863, -2), (key2688, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2714, -2), (key2817, -2)]

def rawRow10483 : Integer.Sparse Key := [(key2817, 1), (key2815, 1), (key2863, 1), (key2815, 1), (key2863, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2863, 1), (key2712, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2712, 1), (key2681, 1), (key2815, 1), (key2681, 1), (key2815, 1), (key2712, 1), (key2817, -2), (key2863, -2), (key2817, -2), (key2714, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2817, -2), (key2688, -2), (key2817, -2), (key2714, -2)]

def rawRow10484 : Integer.Sparse Key := [(key2863, 1), (key2863, 1), (key2817, 1), (key2817, 1), (key2815, 1), (key2815, 1), (key2863, 1), (key2863, 1), (key2714, 1), (key2714, 1), (key2712, 1), (key2712, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2815, 1), (key2815, 1), (key2712, 1), (key2712, 1), (key2681, 1), (key2681, 1), (key2863, -2), (key2817, -2), (key2817, -2), (key2863, -2), (key2714, -2), (key2714, -2), (key2817, -2), (key2817, -2), (key2714, -2), (key2714, -2), (key2688, -2), (key2688, -2)]

def rawRow10485 : Integer.Sparse Key := [(key2681, 1), (key2688, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2714, 1), (key2817, 1), (key2681, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2815, -2), (key2712, -2), (key2815, -2)]

def rawRow10486 : Integer.Sparse Key := [(key2688, 1), (key2681, 1), (key2714, 1), (key2681, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2688, 1), (key2714, 1), (key2681, 1), (key2817, 1), (key2681, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2817, 1), (key2688, 1), (key2817, 1), (key2714, 1), (key2681, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2712, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2815, -2), (key2712, -2)]

def rawRow10487 : Integer.Sparse Key := [(key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2681, 1), (key2681, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2712, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2681, -2), (key2681, -2), (key2815, -2), (key2815, -2), (key2712, -2), (key2712, -2), (key2681, -2), (key2681, -2)]

def rawRow10488 : Integer.Sparse Key := [(key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2817, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2714, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2688, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2681, 1), (key2815, -2), (key2815, -2), (key2815, -2), (key2712, -2), (key2712, -2), (key2712, -2), (key2681, -2), (key2681, -2), (key2681, -2), (key2681, -2), (key2681, -2), (key2681, -2)]

def rawRow10489 : Integer.Sparse Key := [(key1402, -6), (key1402, -6), (key1579, -6), (key1579, -6), (key1402, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1579, 2), (key1579, 2), (key1627, 2), (key1627, 2)]

def rawRow10490 : Integer.Sparse Key := [(key1402, -6), (key1579, -6), (key1402, -6), (key1579, -6), (key1430, 2), (key1402, 2), (key1430, 2), (key1579, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1627, 2), (key1430, 2), (key1579, 2)]

def rawRow10491 : Integer.Sparse Key := [(key1402, -6), (key1579, -6), (key1579, -6), (key1402, -6), (key1430, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1402, 2), (key1627, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1579, 2), (key1430, 2)]

def rawRow10492 : Integer.Sparse Key := [(key1579, -6), (key1402, -6), (key1402, -6), (key1579, -6), (key1579, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1430, 2), (key1627, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1430, 2), (key1579, 2)]

def rawRow10493 : Integer.Sparse Key := [(key1579, -6), (key1402, -6), (key1579, -6), (key1402, -6), (key1579, 2), (key1627, 2), (key1579, 2), (key1430, 2), (key1627, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1579, 2), (key1430, 2)]

def rawRow10494 : Integer.Sparse Key := [(key1579, -6), (key1579, -6), (key1402, -6), (key1402, -6), (key1627, 2), (key1579, 2), (key1579, 2), (key1627, 2), (key1430, 2), (key1430, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1402, 2)]

def rawRow10495 : Integer.Sparse Key := [(key1430, -6), (key1430, -6), (key1430, -6), (key1627, -6), (key1402, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1430, 2), (key1579, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10496 : Integer.Sparse Key := [(key1430, -6), (key1430, -6), (key1627, -6), (key1430, -6), (key1402, 2), (key1430, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1430, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1579, 2), (key1430, 2)]

def rawRow10497 : Integer.Sparse Key := [(key1430, -6), (key1627, -6), (key1430, -6), (key1430, -6), (key1430, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1402, 2), (key1402, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1402, 2)]

def rawRow10498 : Integer.Sparse Key := [(key1627, -6), (key1430, -6), (key1430, -6), (key1430, -6), (key1579, 2), (key1579, 2), (key1579, 2), (key1430, 2), (key1430, 2), (key1430, 2), (key1402, 2), (key1402, 2), (key1402, 2), (key1402, 2), (key1402, 2), (key1402, 2)]

def rawRow10499 : Integer.Sparse Key := [(key2413, 6), (key2413, 6), (key2422, 6), (key2422, 6), (key2422, -6), (key2422, -6), (key2490, -6), (key2490, -6)]

def rawRow10500 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2413, 6), (key2422, 6), (key2422, -6), (key2490, -6), (key2422, -6), (key2490, -6)]

def rawRow10501 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2413, 6), (key2422, 6), (key2422, -6), (key2490, -6), (key2490, -6), (key2422, -6)]

def rawRow10502 : Integer.Sparse Key := [(key2413, 6), (key2422, 6), (key2422, 6), (key2413, 6), (key2490, -6), (key2422, -6), (key2422, -6), (key2490, -6)]

def rawRow10503 : Integer.Sparse Key := [(key2422, 6), (key2413, 6), (key2422, 6), (key2413, 6), (key2490, -6), (key2422, -6), (key2490, -6), (key2422, -6)]

def rawRow10504 : Integer.Sparse Key := [(key2422, 6), (key2422, 6), (key2413, 6), (key2413, 6), (key2490, -6), (key2490, -6), (key2422, -6), (key2422, -6)]

def rawRow10505 : Integer.Sparse Key := [(key2486, 6), (key2490, 6), (key2490, 6), (key2490, 6), (key2413, -6), (key2413, -6), (key2413, -6), (key2486, -6)]

def rawRow10506 : Integer.Sparse Key := [(key2490, 6), (key2486, 6), (key2490, 6), (key2490, 6), (key2413, -6), (key2413, -6), (key2486, -6), (key2413, -6)]

def rawRow10507 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2486, 6), (key2490, 6), (key2413, -6), (key2486, -6), (key2413, -6), (key2413, -6)]

def rawRow10508 : Integer.Sparse Key := [(key2490, 6), (key2490, 6), (key2490, 6), (key2486, 6), (key2486, -6), (key2413, -6), (key2413, -6), (key2413, -6)]

def rawRow10509 : Integer.Sparse Key := [(key2416, 6), (key2416, 6), (key2423, 6), (key2423, 6), (key2423, -6), (key2423, -6), (key2491, -6), (key2491, -6)]

def rawRow10510 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2416, 6), (key2423, 6), (key2423, -6), (key2491, -6), (key2423, -6), (key2491, -6)]

def rawRow10511 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2416, 6), (key2423, 6), (key2423, -6), (key2491, -6), (key2491, -6), (key2423, -6)]

def rawRow10512 : Integer.Sparse Key := [(key2416, 6), (key2423, 6), (key2423, 6), (key2416, 6), (key2491, -6), (key2423, -6), (key2423, -6), (key2491, -6)]

def rawRow10513 : Integer.Sparse Key := [(key2423, 6), (key2416, 6), (key2423, 6), (key2416, 6), (key2491, -6), (key2423, -6), (key2491, -6), (key2423, -6)]

def rawRow10514 : Integer.Sparse Key := [(key2423, 6), (key2423, 6), (key2416, 6), (key2416, 6), (key2491, -6), (key2491, -6), (key2423, -6), (key2423, -6)]

def rawRow10515 : Integer.Sparse Key := [(key2489, 6), (key2491, 6), (key2491, 6), (key2491, 6), (key2416, -6), (key2416, -6), (key2416, -6), (key2489, -6)]

def rawRow10516 : Integer.Sparse Key := [(key2491, 6), (key2489, 6), (key2491, 6), (key2491, 6), (key2416, -6), (key2416, -6), (key2489, -6), (key2416, -6)]

def rawRow10517 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2489, 6), (key2491, 6), (key2416, -6), (key2489, -6), (key2416, -6), (key2416, -6)]

def rawRow10518 : Integer.Sparse Key := [(key2491, 6), (key2491, 6), (key2491, 6), (key2489, 6), (key2489, -6), (key2416, -6), (key2416, -6), (key2416, -6)]

def rawRow10519 : Integer.Sparse Key := [(key2204, -6), (key2204, -6), (key2205, -6), (key2205, -6), (key2204, 2), (key2204, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2319, 2), (key2319, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2320, 2), (key2320, 2)]

def rawRow10520 : Integer.Sparse Key := [(key2204, -6), (key2205, -6), (key2204, -6), (key2205, -6), (key2204, 2), (key2205, 2), (key2204, 2), (key2319, 2), (key2320, 2), (key2204, 2), (key2320, 2), (key2204, 2), (key2319, 2), (key2320, 2), (key2205, 2), (key2320, 2)]

def rawRow10521 : Integer.Sparse Key := [(key2205, -6), (key2204, -6), (key2204, -6), (key2205, -6), (key2205, 2), (key2204, 2), (key2204, 2), (key2320, 2), (key2319, 2), (key2320, 2), (key2204, 2), (key2319, 2), (key2204, 2), (key2320, 2), (key2320, 2), (key2205, 2)]

def rawRow10522 : Integer.Sparse Key := [(key2204, -6), (key2205, -6), (key2205, -6), (key2204, -6), (key2319, 2), (key2320, 2), (key2320, 2), (key2204, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2320, 2), (key2204, 2), (key2204, 2), (key2319, 2)]

def rawRow10523 : Integer.Sparse Key := [(key2205, -6), (key2204, -6), (key2205, -6), (key2204, -6), (key2320, 2), (key2319, 2), (key2320, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2204, 2), (key2319, 2), (key2204, 2)]

def rawRow10524 : Integer.Sparse Key := [(key2205, -6), (key2205, -6), (key2204, -6), (key2204, -6), (key2320, 2), (key2320, 2), (key2319, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2319, 2), (key2204, 2), (key2204, 2)]

def rawRow10525 : Integer.Sparse Key := [(key2319, -6), (key2320, -6), (key2320, -6), (key2320, -6), (key2204, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2320, 2)]

def rawRow10526 : Integer.Sparse Key := [(key2320, -6), (key2319, -6), (key2320, -6), (key2320, -6), (key2205, 2), (key2204, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2320, 2), (key2205, 2)]

def rawRow10527 : Integer.Sparse Key := [(key2320, -6), (key2320, -6), (key2319, -6), (key2320, -6), (key2205, 2), (key2205, 2), (key2204, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2320, 2), (key2205, 2), (key2205, 2)]

def rawRow10528 : Integer.Sparse Key := [(key2320, -6), (key2320, -6), (key2320, -6), (key2319, -6), (key2320, 2), (key2320, 2), (key2320, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2205, 2), (key2204, 2), (key2204, 2), (key2204, 2)]

def rawRow10529 : Integer.Sparse Key := [(key1050, 6), (key1050, 6), (key1058, 6), (key1058, 6), (key1058, -6), (key1058, -6), (key1138, -6), (key1138, -6)]

def rawRow10530 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1050, 6), (key1058, 6), (key1058, -6), (key1138, -6), (key1058, -6), (key1138, -6)]

def rawRow10531 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1050, 6), (key1058, 6), (key1058, -6), (key1138, -6), (key1138, -6), (key1058, -6)]

def rawRow10532 : Integer.Sparse Key := [(key1050, 6), (key1058, 6), (key1058, 6), (key1050, 6), (key1138, -6), (key1058, -6), (key1058, -6), (key1138, -6)]

def rawRow10533 : Integer.Sparse Key := [(key1058, 6), (key1050, 6), (key1058, 6), (key1050, 6), (key1138, -6), (key1058, -6), (key1138, -6), (key1058, -6)]

def rawRow10534 : Integer.Sparse Key := [(key1058, 6), (key1058, 6), (key1050, 6), (key1050, 6), (key1138, -6), (key1138, -6), (key1058, -6), (key1058, -6)]

def rawRow10535 : Integer.Sparse Key := [(key1136, 6), (key1138, 6), (key1138, 6), (key1138, 6), (key1050, -6), (key1050, -6), (key1050, -6), (key1136, -6)]

def rawRow10536 : Integer.Sparse Key := [(key1138, 6), (key1136, 6), (key1138, 6), (key1138, 6), (key1050, -6), (key1050, -6), (key1136, -6), (key1050, -6)]

def rawRow10537 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1136, 6), (key1138, 6), (key1050, -6), (key1136, -6), (key1050, -6), (key1050, -6)]

def rawRow10538 : Integer.Sparse Key := [(key1138, 6), (key1138, 6), (key1138, 6), (key1136, 6), (key1136, -6), (key1050, -6), (key1050, -6), (key1050, -6)]

def rawRow10539 : Integer.Sparse Key := [(key2413, -6), (key2413, -6), (key2422, -6), (key2422, -6), (key2413, 2), (key2413, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2486, 2), (key2486, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2490, 2), (key2490, 2)]

def rawRow10540 : Integer.Sparse Key := [(key2413, -6), (key2422, -6), (key2413, -6), (key2422, -6), (key2413, 2), (key2422, 2), (key2413, 2), (key2486, 2), (key2490, 2), (key2413, 2), (key2490, 2), (key2413, 2), (key2486, 2), (key2490, 2), (key2422, 2), (key2490, 2)]

def rawRow10541 : Integer.Sparse Key := [(key2422, -6), (key2413, -6), (key2413, -6), (key2422, -6), (key2422, 2), (key2413, 2), (key2413, 2), (key2490, 2), (key2486, 2), (key2490, 2), (key2413, 2), (key2486, 2), (key2413, 2), (key2490, 2), (key2490, 2), (key2422, 2)]

def rawRow10542 : Integer.Sparse Key := [(key2413, -6), (key2422, -6), (key2422, -6), (key2413, -6), (key2486, 2), (key2490, 2), (key2490, 2), (key2413, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2490, 2), (key2413, 2), (key2413, 2), (key2486, 2)]

def rawRow10543 : Integer.Sparse Key := [(key2422, -6), (key2413, -6), (key2422, -6), (key2413, -6), (key2490, 2), (key2486, 2), (key2490, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2413, 2), (key2486, 2), (key2413, 2)]

def rawRow10544 : Integer.Sparse Key := [(key2422, -6), (key2422, -6), (key2413, -6), (key2413, -6), (key2490, 2), (key2490, 2), (key2486, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2486, 2), (key2413, 2), (key2413, 2)]

def rawRow10545 : Integer.Sparse Key := [(key2486, -6), (key2490, -6), (key2490, -6), (key2490, -6), (key2413, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2490, 2)]

def rawRow10546 : Integer.Sparse Key := [(key2490, -6), (key2486, -6), (key2490, -6), (key2490, -6), (key2422, 2), (key2413, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2490, 2), (key2422, 2)]

def rawRow10547 : Integer.Sparse Key := [(key2490, -6), (key2490, -6), (key2486, -6), (key2490, -6), (key2422, 2), (key2422, 2), (key2413, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2490, 2), (key2422, 2), (key2422, 2)]

def rawRow10548 : Integer.Sparse Key := [(key2490, -6), (key2490, -6), (key2490, -6), (key2486, -6), (key2490, 2), (key2490, 2), (key2490, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2422, 2), (key2413, 2), (key2413, 2), (key2413, 2)]

def rawRow10549 : Integer.Sparse Key := [(key2677, -6), (key2677, -6), (key2708, -6), (key2708, -6), (key2677, 6), (key3045, 6), (key3094, 6), (key3094, 6)]

def rawRow10550 : Integer.Sparse Key := [(key2677, -6), (key2708, -6), (key2677, -6), (key2708, -6), (key2677, 6), (key3094, 6), (key3045, 6), (key3094, 6)]

def rawRow10551 : Integer.Sparse Key := [(key2677, -6), (key2708, -6), (key2708, -6), (key2677, -6), (key2677, 6), (key3094, 6), (key3094, 6), (key3045, 6)]

def rawRow10552 : Integer.Sparse Key := [(key2708, -6), (key2677, -6), (key2677, -6), (key2708, -6), (key2811, 6), (key2677, 6), (key3045, 6), (key3094, 6)]

def rawRow10553 : Integer.Sparse Key := [(key2708, -6), (key2677, -6), (key2708, -6), (key2677, -6), (key2811, 6), (key2677, 6), (key3094, 6), (key3045, 6)]

def rawRow10554 : Integer.Sparse Key := [(key2708, -6), (key2708, -6), (key2677, -6), (key2677, -6), (key2811, 6), (key2811, 6), (key2677, 6), (key3045, 6)]

def rawRow10555 : Integer.Sparse Key := [(key2811, -6), (key2811, -6), (key2811, -6), (key2861, -6), (key2708, 6), (key2708, 6), (key2708, 6), (key2861, 6)]

def rawRow10556 : Integer.Sparse Key := [(key2811, -6), (key2811, -6), (key2861, -6), (key2811, -6), (key2708, 6), (key2708, 6), (key2861, 6), (key2708, 6)]

def rawRow10557 : Integer.Sparse Key := [(key2811, -6), (key2861, -6), (key2811, -6), (key2811, -6), (key2708, 6), (key2861, 6), (key2708, 6), (key2708, 6)]

def rawRow10558 : Integer.Sparse Key := [(key2861, -6), (key2811, -6), (key2811, -6), (key2811, -6), (key2861, 6), (key2708, 6), (key2708, 6), (key2708, 6)]

def rawRow10559 : Integer.Sparse Key := [(key2685, -2), (key2692, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2821, -2), (key2692, -2), (key2692, -2), (key2821, -2), (key2821, -2), (key2830, -2), (key2830, -2), (key2685, 2), (key2718, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2821, 2), (key2718, 2), (key2718, 2), (key2821, 2), (key2821, 2), (key2871, 2), (key2871, 2)]

def rawRow10560 : Integer.Sparse Key := [(key2692, -2), (key2685, -2), (key2692, -2), (key2821, -2), (key2685, -2), (key2821, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2830, -2), (key2692, -2), (key2821, -2), (key2718, 2), (key2685, 2), (key2718, 2), (key2821, 2), (key2685, 2), (key2821, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2871, 2), (key2718, 2), (key2821, 2)]

def rawRow10561 : Integer.Sparse Key := [(key2692, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2821, -2), (key2685, -2), (key2830, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2821, -2), (key2692, -2), (key2718, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2821, 2), (key2685, 2), (key2871, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2821, 2), (key2718, 2)]

def rawRow10562 : Integer.Sparse Key := [(key2821, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2692, -2), (key2830, -2), (key2685, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2692, -2), (key2821, -2), (key2821, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2718, 2), (key2871, 2), (key2685, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2718, 2), (key2821, 2)]

def rawRow10563 : Integer.Sparse Key := [(key2821, -2), (key2830, -2), (key2821, -2), (key2692, -2), (key2830, -2), (key2692, -2), (key2692, -2), (key2685, -2), (key2821, -2), (key2685, -2), (key2821, -2), (key2692, -2), (key2821, 2), (key2871, 2), (key2821, 2), (key2718, 2), (key2871, 2), (key2718, 2), (key2718, 2), (key2685, 2), (key2821, 2), (key2685, 2), (key2821, 2), (key2718, 2)]

def rawRow10564 : Integer.Sparse Key := [(key2830, -2), (key2821, -2), (key2821, -2), (key2830, -2), (key2692, -2), (key2692, -2), (key2821, -2), (key2821, -2), (key2692, -2), (key2692, -2), (key2685, -2), (key2685, -2), (key2871, 2), (key2821, 2), (key2821, 2), (key2871, 2), (key2718, 2), (key2718, 2), (key2821, 2), (key2821, 2), (key2718, 2), (key2718, 2), (key2685, 2), (key2685, 2)]

def rawRow10565 : Integer.Sparse Key := [(key2718, -2), (key2718, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2727, -2), (key2718, -2), (key2871, -2), (key2727, -2), (key2871, -2), (key2692, 2), (key2692, 2), (key2727, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2727, 2), (key2692, 2), (key2830, 2), (key2727, 2), (key2830, 2)]

def rawRow10566 : Integer.Sparse Key := [(key2718, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2727, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2871, -2), (key2727, -2), (key2692, 2), (key2727, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2727, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2830, 2), (key2727, 2)]

def rawRow10567 : Integer.Sparse Key := [(key2727, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2718, -2), (key2718, -2), (key2871, -2), (key2871, -2), (key2727, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2727, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2692, 2), (key2692, 2), (key2830, 2), (key2830, 2), (key2727, 2), (key2727, 2), (key2692, 2), (key2692, 2)]

def rawRow10568 : Integer.Sparse Key := [(key2871, -2), (key2871, -2), (key2871, -2), (key2727, -2), (key2727, -2), (key2727, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2718, -2), (key2830, 2), (key2830, 2), (key2830, 2), (key2727, 2), (key2727, 2), (key2727, 2), (key2692, 2), (key2692, 2), (key2692, 2), (key2692, 2), (key2692, 2), (key2692, 2)]

def rawRow10569 : Integer.Sparse Key := [(key1055, 2), (key1063, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1143, 2), (key1063, 2), (key1063, 2), (key1143, 2), (key1143, 2), (key1153, 2), (key1153, 2), (key1063, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1153, -2)]

def rawRow10570 : Integer.Sparse Key := [(key1063, 2), (key1055, 2), (key1063, 2), (key1143, 2), (key1055, 2), (key1143, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1143, 2), (key1063, -2), (key1074, -2), (key1063, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1153, -2), (key1074, -2), (key1153, -2)]

def rawRow10571 : Integer.Sparse Key := [(key1063, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1143, 2), (key1055, 2), (key1153, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1143, 2), (key1063, 2), (key1074, -2), (key1063, -2), (key1063, -2), (key1153, -2), (key1143, -2), (key1153, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1153, -2), (key1153, -2), (key1074, -2)]

def rawRow10572 : Integer.Sparse Key := [(key1143, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1055, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1063, 2), (key1143, 2), (key1143, -2), (key1153, -2), (key1153, -2), (key1063, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1153, -2), (key1063, -2), (key1063, -2), (key1143, -2)]

def rawRow10573 : Integer.Sparse Key := [(key1143, 2), (key1153, 2), (key1143, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1055, 2), (key1143, 2), (key1055, 2), (key1143, 2), (key1063, 2), (key1153, -2), (key1143, -2), (key1153, -2), (key1074, -2), (key1063, -2), (key1153, -2), (key1063, -2), (key1153, -2), (key1074, -2), (key1063, -2), (key1143, -2), (key1063, -2)]

def rawRow10574 : Integer.Sparse Key := [(key1153, 2), (key1143, 2), (key1143, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1143, 2), (key1143, 2), (key1063, 2), (key1063, 2), (key1055, 2), (key1055, 2), (key1153, -2), (key1153, -2), (key1143, -2), (key1153, -2), (key1153, -2), (key1074, -2), (key1074, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1063, -2)]

def rawRow10575 : Integer.Sparse Key := [(key1063, 2), (key1063, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1074, 2), (key1063, 2), (key1153, 2), (key1074, 2), (key1153, 2), (key1055, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1143, -2)]

def rawRow10576 : Integer.Sparse Key := [(key1063, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1074, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1153, 2), (key1074, 2), (key1063, -2), (key1055, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1143, -2), (key1063, -2)]

def rawRow10577 : Integer.Sparse Key := [(key1074, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1063, 2), (key1063, 2), (key1153, 2), (key1153, 2), (key1074, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1063, -2), (key1063, -2), (key1055, -2), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1143, -2), (key1063, -2), (key1063, -2)]

def rawRow10578 : Integer.Sparse Key := [(key1153, 2), (key1153, 2), (key1153, 2), (key1074, 2), (key1074, 2), (key1074, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1063, 2), (key1143, -2), (key1143, -2), (key1143, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1063, -2), (key1055, -2), (key1055, -2), (key1055, -2)]

def rawRow10579 : Integer.Sparse Key := [(key3079, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, 6), (key3084, 6), (key3099, 6), (key3099, 6)]

def rawRow10580 : Integer.Sparse Key := [(key3084, -4), (key3079, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3084, 6), (key3099, 6), (key3084, 6), (key3099, 6)]

def rawRow10581 : Integer.Sparse Key := [(key3084, -4), (key3084, -4), (key3079, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3099, 6), (key3084, 6), (key3084, 6), (key3099, 6)]

def rawRow10582 : Integer.Sparse Key := [(key3084, -4), (key3084, -4), (key3099, -4), (key3079, -4), (key3084, -4), (key3084, -4), (key3084, 6), (key3099, 6), (key3099, 6), (key3084, 6)]

def rawRow10583 : Integer.Sparse Key := [(key3084, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3079, -4), (key3084, -4), (key3099, 6), (key3084, 6), (key3099, 6), (key3084, 6)]

def rawRow10584 : Integer.Sparse Key := [(key3099, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3079, -4), (key3099, 6), (key3099, 6), (key3084, 6), (key3084, 6)]

def rawRow10585 : Integer.Sparse Key := [(key3084, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3099, -4), (key3079, 6), (key3084, 6), (key3084, 6), (key3084, 6)]

def rawRow10586 : Integer.Sparse Key := [(key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, -4), (key3099, -4), (key3084, 6), (key3079, 6), (key3084, 6), (key3084, 6)]

def rawRow10587 : Integer.Sparse Key := [(key3099, -4), (key3084, -4), (key3084, -4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, 6), (key3084, 6), (key3079, 6), (key3084, 6)]

def rawRow10588 : Integer.Sparse Key := [(key3099, -4), (key3099, -4), (key3099, -4), (key3084, -4), (key3084, -4), (key3084, -4), (key3084, 6), (key3084, 6), (key3084, 6), (key3079, 6)]

def rawRow10589 : Integer.Sparse Key := [(key1851, 2), (key1851, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1855, 2), (key1851, 2), (key1886, 2), (key1855, 2), (key1886, 2), (key1851, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1886, -2)]

def rawRow10590 : Integer.Sparse Key := [(key1851, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1855, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1886, 2), (key1855, 2), (key1855, -2), (key1851, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1886, -2), (key1855, -2)]

def rawRow10591 : Integer.Sparse Key := [(key1855, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1851, 2), (key1851, 2), (key1886, 2), (key1886, 2), (key1855, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1855, -2), (key1855, -2), (key1851, -2), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1886, -2), (key1855, -2), (key1855, -2)]

def rawRow10592 : Integer.Sparse Key := [(key1886, 2), (key1886, 2), (key1886, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1851, 2), (key1886, -2), (key1886, -2), (key1886, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1855, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

def rawRow10593 : Integer.Sparse Key := [(key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1855, 2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2), (key1851, -2)]

def rawRow10594 : Integer.Sparse Key := [(key685, -24), (key685, 6), (key685, 6), (key685, 6), (key692, 6)]

def rawRow10595 : Integer.Sparse Key := [(key685, -24), (key685, 6), (key685, 6), (key692, 6), (key685, 6)]

def rawRow10596 : Integer.Sparse Key := [(key685, -24), (key685, 6), (key692, 6), (key685, 6), (key685, 6)]

def rawRow10597 : Integer.Sparse Key := [(key685, -24), (key692, 6), (key685, 6), (key685, 6), (key685, 6)]

def rawRow10598 : Integer.Sparse Key := [(key692, -24), (key685, 6), (key685, 6), (key685, 6), (key685, 6)]

def rawRow10599 : Integer.Sparse Key := [(key617, -6), (key619, -6), (key619, -6), (key619, -6), (key617, 2), (key619, 2), (key619, 2), (key617, 2), (key619, 2), (key617, 2), (key645, 2), (key619, 2), (key645, 2), (key619, 2), (key619, 2), (key645, 2)]

def rawRow10600 : Integer.Sparse Key := [(key619, -6), (key617, -6), (key619, -6), (key619, -6), (key619, 2), (key617, 2), (key619, 2), (key619, 2), (key617, 2), (key645, 2), (key617, 2), (key645, 2), (key619, 2), (key619, 2), (key645, 2), (key619, 2)]

def rawRow10601 : Integer.Sparse Key := [(key619, -6), (key619, -6), (key617, -6), (key619, -6), (key619, 2), (key619, 2), (key617, 2), (key645, 2), (key645, 2), (key619, 2), (key619, 2), (key617, 2), (key617, 2), (key645, 2), (key619, 2), (key619, 2)]

def rawRow10602 : Integer.Sparse Key := [(key619, -6), (key619, -6), (key619, -6), (key617, -6), (key645, 2), (key645, 2), (key645, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key617, 2), (key617, 2), (key617, 2)]

def rawRow10603 : Integer.Sparse Key := [(key645, -6), (key645, -6), (key645, -6), (key645, -6), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2), (key619, 2)]

def rawRow10604 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1958, -6), (key1966, -6), (key1958, 2), (key1958, 2), (key1960, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1960, 2), (key1958, 2), (key1966, 2), (key1960, 2), (key1966, 2)]

def rawRow10605 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1966, -6), (key1958, -6), (key1958, 2), (key1960, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1960, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1966, 2), (key1960, 2)]

def rawRow10606 : Integer.Sparse Key := [(key1958, -6), (key1966, -6), (key1958, -6), (key1958, -6), (key1960, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1958, 2), (key1958, 2), (key1966, 2), (key1966, 2), (key1960, 2), (key1960, 2), (key1958, 2), (key1958, 2)]

def rawRow10607 : Integer.Sparse Key := [(key1966, -6), (key1958, -6), (key1958, -6), (key1958, -6), (key1966, 2), (key1966, 2), (key1966, 2), (key1960, 2), (key1960, 2), (key1960, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2)]

def rawRow10608 : Integer.Sparse Key := [(key1960, -6), (key1960, -6), (key1960, -6), (key1960, -6), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2), (key1958, 2)]

def rawRow10609 : Integer.Sparse Key := [(key1850, -6), (key1852, -6), (key1852, -6), (key1852, -6), (key1850, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1852, 2), (key1850, 2), (key1884, 2), (key1852, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1884, 2)]

def rawRow10610 : Integer.Sparse Key := [(key1852, -6), (key1850, -6), (key1852, -6), (key1852, -6), (key1852, 2), (key1850, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1884, 2), (key1850, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1884, 2), (key1852, 2)]

def rawRow10611 : Integer.Sparse Key := [(key1852, -6), (key1852, -6), (key1850, -6), (key1852, -6), (key1852, 2), (key1852, 2), (key1850, 2), (key1884, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1850, 2), (key1884, 2), (key1852, 2), (key1852, 2)]

def rawRow10612 : Integer.Sparse Key := [(key1852, -6), (key1852, -6), (key1852, -6), (key1850, -6), (key1884, 2), (key1884, 2), (key1884, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1850, 2), (key1850, 2), (key1850, 2)]

def rawRow10613 : Integer.Sparse Key := [(key1884, -6), (key1884, -6), (key1884, -6), (key1884, -6), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2), (key1852, 2)]

def rawRow10614 : Integer.Sparse Key := [(key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1861, -2), (key1859, -2), (key1877, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1859, 1), (key1861, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1867, 1), (key1877, 1)]

def rawRow10615 : Integer.Sparse Key := [(key1861, -2), (key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1877, -2), (key1859, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1861, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1867, 1)]

def rawRow10616 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1859, -2), (key1877, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1)]

def rawRow10617 : Integer.Sparse Key := [(key1877, -2), (key1877, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1)]

def rawRow10618 : Integer.Sparse Key := [(key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1)]

def rawRow10619 : Integer.Sparse Key := [(key1957, -24), (key1957, 6), (key1957, 6), (key1957, 6), (key1969, 6)]

def rawRow10620 : Integer.Sparse Key := [(key1957, -24), (key1957, 6), (key1957, 6), (key1969, 6), (key1957, 6)]

def rawRow10621 : Integer.Sparse Key := [(key1957, -24), (key1957, 6), (key1969, 6), (key1957, 6), (key1957, 6)]

def rawRow10622 : Integer.Sparse Key := [(key1957, -24), (key1969, 6), (key1957, 6), (key1957, 6), (key1957, 6)]

def rawRow10623 : Integer.Sparse Key := [(key1969, -24), (key1957, 6), (key1957, 6), (key1957, 6), (key1957, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10624 : Integer.Sparse Key := [(key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1861, -2), (key1859, -2), (key1867, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1867, -2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2)]

def rawRow10625 : Integer.Sparse Key := [(key1861, -2), (key1859, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1867, -2), (key1859, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, 2), (key1859, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1877, 2), (key1861, 2)]

def rawRow10626 : Integer.Sparse Key := [(key1861, -2), (key1861, -2), (key1859, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1861, 2), (key1861, 2), (key1859, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1877, 2), (key1861, 2), (key1861, 2)]

def rawRow10627 : Integer.Sparse Key := [(key1867, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1877, 2), (key1877, 2), (key1877, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1861, 2), (key1859, 2), (key1859, 2), (key1859, 2)]

def rawRow10628 : Integer.Sparse Key := [(key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1877, -2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2), (key1867, 2)]

def rawRow10629 : Integer.Sparse Key := [(key626, -2), (key627, -2), (key627, -2), (key626, -2), (key627, -2), (key626, -2), (key640, -2), (key627, -2), (key640, -2), (key627, -2), (key627, -2), (key640, -2), (key626, 1), (key627, 1), (key626, 1), (key629, 1), (key627, 1), (key629, 1), (key626, 1), (key627, 1), (key626, 1), (key640, 1), (key627, 1), (key640, 1), (key626, 1), (key629, 1), (key626, 1), (key640, 1), (key629, 1), (key640, 1), (key627, 1), (key629, 1), (key627, 1), (key640, 1), (key629, 1), (key640, 1)]

def rawRow10630 : Integer.Sparse Key := [(key627, -2), (key626, -2), (key627, -2), (key627, -2), (key626, -2), (key640, -2), (key626, -2), (key640, -2), (key627, -2), (key627, -2), (key640, -2), (key627, -2), (key627, 1), (key626, 1), (key629, 1), (key626, 1), (key629, 1), (key627, 1), (key627, 1), (key626, 1), (key640, 1), (key626, 1), (key640, 1), (key627, 1), (key629, 1), (key626, 1), (key640, 1), (key626, 1), (key640, 1), (key629, 1), (key629, 1), (key627, 1), (key640, 1), (key627, 1), (key640, 1), (key629, 1)]

def rawRow10631 : Integer.Sparse Key := [(key627, -2), (key627, -2), (key626, -2), (key640, -2), (key640, -2), (key627, -2), (key627, -2), (key626, -2), (key626, -2), (key640, -2), (key627, -2), (key627, -2), (key629, 1), (key629, 1), (key627, 1), (key627, 1), (key626, 1), (key626, 1), (key640, 1), (key640, 1), (key627, 1), (key627, 1), (key626, 1), (key626, 1), (key640, 1), (key640, 1), (key629, 1), (key629, 1), (key626, 1), (key626, 1), (key640, 1), (key640, 1), (key629, 1), (key629, 1), (key627, 1), (key627, 1)]

def rawRow10632 : Integer.Sparse Key := [(key640, -2), (key640, -2), (key640, -2), (key627, -2), (key627, -2), (key627, -2), (key627, -2), (key627, -2), (key627, -2), (key626, -2), (key626, -2), (key626, -2), (key640, 1), (key640, 1), (key640, 1), (key640, 1), (key640, 1), (key640, 1), (key629, 1), (key629, 1), (key629, 1), (key629, 1), (key629, 1), (key629, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key626, 1), (key626, 1), (key626, 1), (key626, 1), (key626, 1), (key626, 1)]

def rawRow10633 : Integer.Sparse Key := [(key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key629, -2), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1), (key627, 1)]

def rawRow10634 : Integer.Sparse Key := [(key1859, 1), (key1861, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1867, 1), (key1877, 1), (key1861, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1877, -2), (key1867, -2), (key1877, -2)]

def rawRow10635 : Integer.Sparse Key := [(key1861, 1), (key1859, 1), (key1867, 1), (key1859, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1861, 1), (key1867, 1), (key1859, 1), (key1877, 1), (key1859, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1877, 1), (key1861, 1), (key1877, 1), (key1867, 1), (key1861, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1867, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1877, -2), (key1867, -2)]

def rawRow10636 : Integer.Sparse Key := [(key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1859, 1), (key1859, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1867, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1861, -2), (key1861, -2), (key1877, -2), (key1877, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2)]

def rawRow10637 : Integer.Sparse Key := [(key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1877, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1867, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1859, 1), (key1877, -2), (key1877, -2), (key1877, -2), (key1867, -2), (key1867, -2), (key1867, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2), (key1861, -2)]

def rawRow10638 : Integer.Sparse Key := [(key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1861, 1), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2), (key1859, -2)]

def rawRow10639 : Integer.Sparse Key := [(key686, -6), (key686, -6), (key686, -6), (key690, -6), (key686, 2), (key686, 2), (key687, 2), (key686, 2), (key686, 2), (key690, 2), (key686, 2), (key687, 2), (key686, 2), (key690, 2), (key687, 2), (key690, 2)]

def rawRow10640 : Integer.Sparse Key := [(key686, -6), (key686, -6), (key690, -6), (key686, -6), (key686, 2), (key687, 2), (key686, 2), (key686, 2), (key690, 2), (key686, 2), (key687, 2), (key686, 2), (key690, 2), (key686, 2), (key690, 2), (key687, 2)]

def rawRow10641 : Integer.Sparse Key := [(key686, -6), (key690, -6), (key686, -6), (key686, -6), (key687, 2), (key686, 2), (key686, 2), (key690, 2), (key686, 2), (key686, 2), (key690, 2), (key690, 2), (key687, 2), (key687, 2), (key686, 2), (key686, 2)]

def rawRow10642 : Integer.Sparse Key := [(key690, -6), (key686, -6), (key686, -6), (key686, -6), (key690, 2), (key690, 2), (key690, 2), (key687, 2), (key687, 2), (key687, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2)]

def rawRow10643 : Integer.Sparse Key := [(key687, -6), (key687, -6), (key687, -6), (key687, -6), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2), (key686, 2)]

def rawRow10644 : Integer.Sparse Key := [(key1932, 6), (key1933, 6), (key1933, 6), (key1933, 6), (key1933, -6), (key1933, -6), (key1933, -6), (key1953, -6)]

def rawRow10645 : Integer.Sparse Key := [(key1933, 6), (key1932, 6), (key1933, 6), (key1933, 6), (key1933, -6), (key1933, -6), (key1953, -6), (key1933, -6)]

def rawRow10646 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1932, 6), (key1933, 6), (key1933, -6), (key1953, -6), (key1933, -6), (key1933, -6)]

def rawRow10647 : Integer.Sparse Key := [(key1933, 6), (key1933, 6), (key1933, 6), (key1932, 6), (key1953, -6), (key1933, -6), (key1933, -6), (key1933, -6)]

def rawRow10648 : Integer.Sparse Key := [(key1953, 6), (key1953, 6), (key1953, 6), (key1953, 6), (key1932, -6), (key1932, -6), (key1932, -6), (key1932, -6)]

def rawRow10649 : Integer.Sparse Key := [(key1850, 6), (key1852, 6), (key1852, 6), (key1852, 6), (key1852, -6), (key1852, -6), (key1852, -6), (key1884, -6)]

def rawRow10650 : Integer.Sparse Key := [(key1852, 6), (key1850, 6), (key1852, 6), (key1852, 6), (key1852, -6), (key1852, -6), (key1884, -6), (key1852, -6)]

def rawRow10651 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1850, 6), (key1852, 6), (key1852, -6), (key1884, -6), (key1852, -6), (key1852, -6)]

def rawRow10652 : Integer.Sparse Key := [(key1852, 6), (key1852, 6), (key1852, 6), (key1850, 6), (key1884, -6), (key1852, -6), (key1852, -6), (key1852, -6)]

def rawRow10653 : Integer.Sparse Key := [(key1884, 6), (key1884, 6), (key1884, 6), (key1884, 6), (key1850, -6), (key1850, -6), (key1850, -6), (key1850, -6)]

def rawRow10654 : Integer.Sparse Key := [(key360, -6), (key362, -6), (key362, -6), (key362, -6), (key360, 2), (key362, 2), (key362, 2), (key360, 2), (key362, 2), (key360, 2), (key366, 2), (key362, 2), (key366, 2), (key362, 2), (key362, 2), (key366, 2)]

def rawRow10655 : Integer.Sparse Key := [(key362, -6), (key360, -6), (key362, -6), (key362, -6), (key362, 2), (key360, 2), (key362, 2), (key362, 2), (key360, 2), (key366, 2), (key360, 2), (key366, 2), (key362, 2), (key362, 2), (key366, 2), (key362, 2)]

def rawRow10656 : Integer.Sparse Key := [(key362, -6), (key362, -6), (key360, -6), (key362, -6), (key362, 2), (key362, 2), (key360, 2), (key366, 2), (key366, 2), (key362, 2), (key362, 2), (key360, 2), (key360, 2), (key366, 2), (key362, 2), (key362, 2)]

def rawRow10657 : Integer.Sparse Key := [(key362, -6), (key362, -6), (key362, -6), (key360, -6), (key366, 2), (key366, 2), (key366, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key360, 2), (key360, 2), (key360, 2)]

def rawRow10658 : Integer.Sparse Key := [(key366, -6), (key366, -6), (key366, -6), (key366, -6), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2), (key362, 2)]

def rawRow10659 : Integer.Sparse Key := [(key617, 6), (key619, 6), (key619, 6), (key619, 6), (key619, -6), (key619, -6), (key619, -6), (key645, -6)]

def rawRow10660 : Integer.Sparse Key := [(key619, 6), (key617, 6), (key619, 6), (key619, 6), (key619, -6), (key619, -6), (key645, -6), (key619, -6)]

def rawRow10661 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key617, 6), (key619, 6), (key619, -6), (key645, -6), (key619, -6), (key619, -6)]

def rawRow10662 : Integer.Sparse Key := [(key619, 6), (key619, 6), (key619, 6), (key617, 6), (key645, -6), (key619, -6), (key619, -6), (key619, -6)]

def rawRow10663 : Integer.Sparse Key := [(key645, 6), (key645, 6), (key645, 6), (key645, 6), (key617, -6), (key617, -6), (key617, -6), (key617, -6)]

def rawRow10664 : Integer.Sparse Key := [(key1932, -6), (key1933, -6), (key1933, -6), (key1933, -6), (key1932, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1933, 2), (key1932, 2), (key1953, 2), (key1933, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1953, 2)]

def rawRow10665 : Integer.Sparse Key := [(key1933, -6), (key1932, -6), (key1933, -6), (key1933, -6), (key1933, 2), (key1932, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1953, 2), (key1932, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1953, 2), (key1933, 2)]

def rawRow10666 : Integer.Sparse Key := [(key1933, -6), (key1933, -6), (key1932, -6), (key1933, -6), (key1933, 2), (key1933, 2), (key1932, 2), (key1953, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1932, 2), (key1953, 2), (key1933, 2), (key1933, 2)]

def rawRow10667 : Integer.Sparse Key := [(key1933, -6), (key1933, -6), (key1933, -6), (key1932, -6), (key1953, 2), (key1953, 2), (key1953, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1932, 2), (key1932, 2), (key1932, 2)]

def rawRow10668 : Integer.Sparse Key := [(key1953, -6), (key1953, -6), (key1953, -6), (key1953, -6), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2), (key1933, 2)]

def rawRow10669 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1958, -6), (key1960, -6), (key1958, 6), (key1958, 6), (key1958, 6), (key1966, 6)]

def rawRow10670 : Integer.Sparse Key := [(key1958, -6), (key1958, -6), (key1960, -6), (key1958, -6), (key1958, 6), (key1958, 6), (key1966, 6), (key1958, 6)]

def rawRow10671 : Integer.Sparse Key := [(key1958, -6), (key1960, -6), (key1958, -6), (key1958, -6), (key1958, 6), (key1966, 6), (key1958, 6), (key1958, 6)]

def rawRow10672 : Integer.Sparse Key := [(key1960, -6), (key1958, -6), (key1958, -6), (key1958, -6), (key1966, 6), (key1958, 6), (key1958, 6), (key1958, 6)]

def rawRow10673 : Integer.Sparse Key := [(key1966, -6), (key1966, -6), (key1966, -6), (key1966, -6), (key1960, 6), (key1960, 6), (key1960, 6), (key1960, 6)]

def rawRow10674 : Integer.Sparse Key := [(key1860, -2), (key1860, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1864, -2), (key1860, -2), (key1879, -2), (key1864, -2), (key1879, -2), (key1860, 2), (key1860, 2), (key1869, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1869, 2), (key1860, 2), (key1879, 2), (key1869, 2), (key1879, 2)]

def rawRow10675 : Integer.Sparse Key := [(key1860, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1864, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1879, -2), (key1864, -2), (key1860, 2), (key1869, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1869, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1879, 2), (key1869, 2)]

def rawRow10676 : Integer.Sparse Key := [(key1864, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1860, -2), (key1860, -2), (key1879, -2), (key1879, -2), (key1864, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1869, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1860, 2), (key1860, 2), (key1879, 2), (key1879, 2), (key1869, 2), (key1869, 2), (key1860, 2), (key1860, 2)]

def rawRow10677 : Integer.Sparse Key := [(key1879, -2), (key1879, -2), (key1879, -2), (key1864, -2), (key1864, -2), (key1864, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1860, -2), (key1879, 2), (key1879, 2), (key1879, 2), (key1869, 2), (key1869, 2), (key1869, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2), (key1860, 2)]

def rawRow10678 : Integer.Sparse Key := [(key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1869, -2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2), (key1864, 2)]

def rawRow10679 : Integer.Sparse Key := [(key618, 2), (key618, 2), (key622, 2), (key618, 2), (key618, 2), (key648, 2), (key618, 2), (key622, 2), (key618, 2), (key648, 2), (key622, 2), (key648, 2), (key618, -2), (key622, -2), (key622, -2), (key618, -2), (key622, -2), (key618, -2), (key648, -2), (key622, -2), (key648, -2), (key622, -2), (key622, -2), (key648, -2)]

def rawRow10680 : Integer.Sparse Key := [(key618, 2), (key622, 2), (key618, 2), (key618, 2), (key648, 2), (key618, 2), (key622, 2), (key618, 2), (key648, 2), (key618, 2), (key648, 2), (key622, 2), (key622, -2), (key618, -2), (key622, -2), (key622, -2), (key618, -2), (key648, -2), (key618, -2), (key648, -2), (key622, -2), (key622, -2), (key648, -2), (key622, -2)]

def rawRow10681 : Integer.Sparse Key := [(key622, 2), (key618, 2), (key618, 2), (key648, 2), (key618, 2), (key618, 2), (key648, 2), (key648, 2), (key622, 2), (key622, 2), (key618, 2), (key618, 2), (key622, -2), (key622, -2), (key618, -2), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key648, -2), (key622, -2), (key622, -2)]

def rawRow10682 : Integer.Sparse Key := [(key648, 2), (key648, 2), (key648, 2), (key622, 2), (key622, 2), (key622, 2), (key618, 2), (key618, 2), (key618, 2), (key618, 2), (key618, 2), (key618, 2), (key648, -2), (key648, -2), (key648, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key622, -2), (key618, -2), (key618, -2), (key618, -2)]

def rawRow10683 : Integer.Sparse Key := [(key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key622, 2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2), (key618, -2)]

def rawRow10684 : Integer.Sparse Key := [(key1962, -4), (key1962, -4), (key1964, -4), (key1962, -4), (key1964, -4), (key1964, -4), (key1962, 6), (key1964, 6), (key1964, 6), (key1964, 6)]

def rawRow10685 : Integer.Sparse Key := [(key1962, -4), (key1964, -4), (key1962, -4), (key1964, -4), (key1962, -4), (key1964, -4), (key1964, 6), (key1962, 6), (key1964, 6), (key1964, 6)]

def rawRow10686 : Integer.Sparse Key := [(key1964, -4), (key1962, -4), (key1962, -4), (key1964, -4), (key1964, -4), (key1962, -4), (key1964, 6), (key1964, 6), (key1962, 6), (key1964, 6)]

def rawRow10687 : Integer.Sparse Key := [(key1964, -4), (key1964, -4), (key1964, -4), (key1962, -4), (key1962, -4), (key1962, -4), (key1964, 6), (key1964, 6), (key1964, 6), (key1962, 6)]

def rawRow10688 : Integer.Sparse Key := [(key1964, -4), (key1964, -4), (key1964, -4), (key1964, -4), (key1964, -4), (key1964, -4), (key1962, 6), (key1962, 6), (key1962, 6), (key1962, 6)]

def rawRow10689 : Integer.Sparse Key := [(key288, 6), (key289, 6), (key289, 6), (key289, 6), (key289, -24)]

def rawRow10690 : Integer.Sparse Key := [(key289, 6), (key288, 6), (key289, 6), (key289, 6), (key289, -24)]

def rawRow10691 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key288, 6), (key289, 6), (key289, -24)]

def rawRow10692 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key289, 6), (key288, 6), (key289, -24)]

def rawRow10693 : Integer.Sparse Key := [(key289, 6), (key289, 6), (key289, 6), (key289, 6), (key288, -24)]

def rawRow10694 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2392, 2), (key2406, 2), (key2480, 2), (key2543, 2), (key2437, 2), (key2440, 2), (key2503, 2), (key2554, 2), (key2522, 2), (key2563, 2), (key2378, -2), (key2381, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2440, -2), (key2506, -2), (key2554, -2)]

def rawRow10695 : Integer.Sparse Key := [(key2378, 2), (key2392, 2), (key2390, 2), (key2406, 2), (key2543, 2), (key2480, 2), (key2440, 2), (key2437, 2), (key2554, 2), (key2503, 2), (key2563, 2), (key2522, 2), (key2381, -2), (key2378, -2), (key2392, -2), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, -2), (key2554, -2), (key2506, -2)]

def rawRow10696 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2392, 2), (key2480, 2), (key2406, 2), (key2543, 2), (key2503, 2), (key2522, 2), (key2437, 2), (key2563, 2), (key2440, 2), (key2554, 2), (key2378, -2), (key2392, -2), (key2381, -2), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2506, -2), (key2440, -2), (key2554, -2)]

def rawRow10697 : Integer.Sparse Key := [(key2390, 2), (key2392, 2), (key2378, 2), (key2480, 2), (key2543, 2), (key2406, 2), (key2522, 2), (key2503, 2), (key2563, 2), (key2437, 2), (key2554, 2), (key2440, 2), (key2392, -2), (key2378, -2), (key2381, -2), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2506, -2), (key2554, -2), (key2440, -2)]

def rawRow10698 : Integer.Sparse Key := [(key2392, 2), (key2378, 2), (key2390, 2), (key2543, 2), (key2406, 2), (key2480, 2), (key2554, 2), (key2563, 2), (key2440, 2), (key2522, 2), (key2437, 2), (key2503, 2), (key2381, -2), (key2392, -2), (key2378, -2), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, -2), (key2440, -2), (key2506, -2)]

def rawRow10699 : Integer.Sparse Key := [(key2392, 2), (key2390, 2), (key2378, 2), (key2543, 2), (key2480, 2), (key2406, 2), (key2563, 2), (key2554, 2), (key2522, 2), (key2440, 2), (key2503, 2), (key2437, 2), (key2392, -2), (key2381, -2), (key2378, -2), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2554, -2), (key2506, -2), (key2440, -2)]

def rawRow10700 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2440, 2), (key2378, 2), (key2503, 2), (key2554, 2), (key2390, 2), (key2392, 2), (key2480, 2), (key2543, 2), (key2522, 2), (key2563, 2), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2392, -2), (key2482, -2), (key2543, -2)]

def rawRow10701 : Integer.Sparse Key := [(key2406, 2), (key2440, 2), (key2437, 2), (key2378, 2), (key2554, 2), (key2503, 2), (key2392, 2), (key2390, 2), (key2543, 2), (key2480, 2), (key2563, 2), (key2522, 2), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, -2), (key2543, -2), (key2482, -2)]

def rawRow10702 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2440, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2480, 2), (key2522, 2), (key2390, 2), (key2563, 2), (key2392, 2), (key2543, 2), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2482, -2), (key2392, -2), (key2543, -2)]

def rawRow10703 : Integer.Sparse Key := [(key2437, 2), (key2440, 2), (key2406, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2522, 2), (key2480, 2), (key2563, 2), (key2390, 2), (key2543, 2), (key2392, 2), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2482, -2), (key2543, -2), (key2392, -2)]

def rawRow10704 : Integer.Sparse Key := [(key2440, 2), (key2406, 2), (key2437, 2), (key2554, 2), (key2378, 2), (key2503, 2), (key2543, 2), (key2563, 2), (key2392, 2), (key2522, 2), (key2390, 2), (key2480, 2), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, -2), (key2392, -2), (key2482, -2)]

def rawRow10705 : Integer.Sparse Key := [(key2440, 2), (key2437, 2), (key2406, 2), (key2554, 2), (key2503, 2), (key2378, 2), (key2563, 2), (key2543, 2), (key2522, 2), (key2392, 2), (key2480, 2), (key2390, 2), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2543, -2), (key2482, -2), (key2392, -2)]

def rawRow10706 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2522, 2), (key2390, 2), (key2437, 2), (key2563, 2), (key2378, 2), (key2392, 2), (key2406, 2), (key2543, 2), (key2440, 2), (key2554, 2), (key2472, -2), (key2482, -2), (key2506, -2), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2381, -2), (key2409, -2), (key2538, -2)]

def rawRow10707 : Integer.Sparse Key := [(key2480, 2), (key2522, 2), (key2503, 2), (key2390, 2), (key2563, 2), (key2437, 2), (key2392, 2), (key2378, 2), (key2543, 2), (key2406, 2), (key2554, 2), (key2440, 2), (key2482, -2), (key2472, -2), (key2506, -2), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2381, -2), (key2538, -2), (key2409, -2)]

def rawRow10708 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2522, 2), (key2437, 2), (key2390, 2), (key2563, 2), (key2406, 2), (key2440, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2472, -2), (key2506, -2), (key2482, -2), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2409, -2), (key2381, -2), (key2538, -2)]

def rawRow10709 : Integer.Sparse Key := [(key2503, 2), (key2522, 2), (key2480, 2), (key2437, 2), (key2563, 2), (key2390, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2543, 2), (key2392, 2), (key2506, -2), (key2472, -2), (key2482, -2), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2409, -2), (key2538, -2), (key2381, -2)]

def rawRow10710 : Integer.Sparse Key := [(key2522, 2), (key2480, 2), (key2503, 2), (key2563, 2), (key2390, 2), (key2437, 2), (key2543, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2378, 2), (key2406, 2), (key2482, -2), (key2506, -2), (key2472, -2), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2538, -2), (key2381, -2), (key2409, -2)]

def rawRow10711 : Integer.Sparse Key := [(key2522, 2), (key2503, 2), (key2480, 2), (key2563, 2), (key2437, 2), (key2390, 2), (key2554, 2), (key2543, 2), (key2440, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2506, -2), (key2482, -2), (key2472, -2), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2538, -2), (key2409, -2), (key2381, -2)]

def rawRow10712 : Integer.Sparse Key := [(key2543, 2), (key2554, 2), (key2563, 2), (key2392, 2), (key2440, 2), (key2522, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2480, 2), (key2437, 2), (key2503, 2), (key2538, -2), (key2543, -2), (key2554, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

def rawRow10713 : Integer.Sparse Key := [(key2543, 2), (key2563, 2), (key2554, 2), (key2392, 2), (key2522, 2), (key2440, 2), (key2390, 2), (key2378, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2437, 2), (key2543, -2), (key2538, -2), (key2554, -2), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

def rawRow10714 : Integer.Sparse Key := [(key2554, 2), (key2543, 2), (key2563, 2), (key2440, 2), (key2392, 2), (key2522, 2), (key2406, 2), (key2437, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2538, -2), (key2554, -2), (key2543, -2), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

def rawRow10715 : Integer.Sparse Key := [(key2554, 2), (key2563, 2), (key2543, 2), (key2440, 2), (key2522, 2), (key2392, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2480, 2), (key2390, 2), (key2554, -2), (key2538, -2), (key2543, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

def rawRow10716 : Integer.Sparse Key := [(key2563, 2), (key2543, 2), (key2554, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2480, 2), (key2503, 2), (key2390, 2), (key2437, 2), (key2378, 2), (key2406, 2), (key2543, -2), (key2554, -2), (key2538, -2), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

def rawRow10717 : Integer.Sparse Key := [(key2563, 2), (key2554, 2), (key2543, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2503, 2), (key2480, 2), (key2437, 2), (key2390, 2), (key2406, 2), (key2378, 2), (key2554, -2), (key2543, -2), (key2538, -2), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

def rawRow10718 : Integer.Sparse Key := [(key2381, 2), (key2392, 2), (key2392, 2), (key2409, 2), (key2482, 2), (key2482, 2), (key2440, 2), (key2440, 2), (key2506, 2), (key2506, 2), (key2522, 2), (key2522, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2503, -2)]

def rawRow10719 : Integer.Sparse Key := [(key2392, 2), (key2381, 2), (key2392, 2), (key2482, 2), (key2409, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2440, 2), (key2522, 2), (key2440, 2), (key2506, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2437, -2), (key2503, -2)]

def rawRow10720 : Integer.Sparse Key := [(key2392, 2), (key2392, 2), (key2381, 2), (key2482, 2), (key2482, 2), (key2409, 2), (key2522, 2), (key2506, 2), (key2522, 2), (key2440, 2), (key2506, 2), (key2440, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, -2), (key2503, -2), (key2437, -2)]

def rawRow10721 : Integer.Sparse Key := [(key2409, 2), (key2440, 2), (key2440, 2), (key2381, 2), (key2506, 2), (key2506, 2), (key2392, 2), (key2392, 2), (key2482, 2), (key2482, 2), (key2522, 2), (key2522, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

def rawRow10722 : Integer.Sparse Key := [(key2440, 2), (key2409, 2), (key2440, 2), (key2506, 2), (key2381, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2392, 2), (key2522, 2), (key2392, 2), (key2482, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

def rawRow10723 : Integer.Sparse Key := [(key2440, 2), (key2440, 2), (key2409, 2), (key2506, 2), (key2506, 2), (key2381, 2), (key2522, 2), (key2482, 2), (key2522, 2), (key2392, 2), (key2482, 2), (key2392, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

def rawRow10724 : Integer.Sparse Key := [(key2482, 2), (key2506, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2522, 2), (key2381, 2), (key2392, 2), (key2409, 2), (key2482, 2), (key2440, 2), (key2506, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

def rawRow10725 : Integer.Sparse Key := [(key2482, 2), (key2522, 2), (key2506, 2), (key2392, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2381, 2), (key2482, 2), (key2409, 2), (key2506, 2), (key2440, 2), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

def rawRow10726 : Integer.Sparse Key := [(key2506, 2), (key2482, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2522, 2), (key2409, 2), (key2440, 2), (key2381, 2), (key2506, 2), (key2392, 2), (key2482, 2), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

def rawRow10727 : Integer.Sparse Key := [(key2506, 2), (key2522, 2), (key2482, 2), (key2440, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2409, 2), (key2506, 2), (key2381, 2), (key2482, 2), (key2392, 2), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

def rawRow10728 : Integer.Sparse Key := [(key2522, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2482, 2), (key2506, 2), (key2392, 2), (key2440, 2), (key2381, 2), (key2409, 2), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

def rawRow10729 : Integer.Sparse Key := [(key2522, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2506, 2), (key2482, 2), (key2440, 2), (key2392, 2), (key2409, 2), (key2381, 2), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

def rawRow10730 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1025, 6), (key1103, 6), (key1187, 6)]

def rawRow10731 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1025, 6), (key1187, 6), (key1103, 6)]

def rawRow10732 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1103, 6), (key1025, 6), (key1187, 6)]

def rawRow10733 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1103, 6), (key1187, 6), (key1025, 6)]

def rawRow10734 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1187, 6), (key1025, 6), (key1103, 6)]

def rawRow10735 : Integer.Sparse Key := [(key1103, -24), (key990, 6), (key1187, 6), (key1103, 6), (key1025, 6)]

def rawRow10736 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key990, 6), (key1103, 6), (key1187, 6)]

def rawRow10737 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key990, 6), (key1187, 6), (key1103, 6)]

def rawRow10738 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1103, 6), (key990, 6), (key1187, 6)]

def rawRow10739 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1103, 6), (key1187, 6), (key990, 6)]

def rawRow10740 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1187, 6), (key990, 6), (key1103, 6)]

def rawRow10741 : Integer.Sparse Key := [(key1103, -24), (key1025, 6), (key1187, 6), (key1103, 6), (key990, 6)]

def rawRow10742 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key990, 6), (key1025, 6), (key1187, 6)]

def rawRow10743 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key990, 6), (key1187, 6), (key1025, 6)]

def rawRow10744 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1025, 6), (key990, 6), (key1187, 6)]

def rawRow10745 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1025, 6), (key1187, 6), (key990, 6)]

def rawRow10746 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1187, 6), (key990, 6), (key1025, 6)]

def rawRow10747 : Integer.Sparse Key := [(key1103, -24), (key1103, 6), (key1187, 6), (key1025, 6), (key990, 6)]

def rawRow10748 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key990, 6), (key1025, 6), (key1103, 6)]

def rawRow10749 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key990, 6), (key1103, 6), (key1025, 6)]

def rawRow10750 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1025, 6), (key990, 6), (key1103, 6)]

def rawRow10751 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1025, 6), (key1103, 6), (key990, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10752 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1103, 6), (key990, 6), (key1025, 6)]

def rawRow10753 : Integer.Sparse Key := [(key1103, -24), (key1187, 6), (key1103, 6), (key1025, 6), (key990, 6)]

def rawRow10754 : Integer.Sparse Key := [(key1187, -24), (key990, 6), (key1025, 6), (key1103, 6), (key1103, 6)]

def rawRow10755 : Integer.Sparse Key := [(key1187, -24), (key990, 6), (key1103, 6), (key1025, 6), (key1103, 6)]

def rawRow10756 : Integer.Sparse Key := [(key1187, -24), (key990, 6), (key1103, 6), (key1103, 6), (key1025, 6)]

def rawRow10757 : Integer.Sparse Key := [(key1187, -24), (key1025, 6), (key990, 6), (key1103, 6), (key1103, 6)]

def rawRow10758 : Integer.Sparse Key := [(key1187, -24), (key1025, 6), (key1103, 6), (key990, 6), (key1103, 6)]

def rawRow10759 : Integer.Sparse Key := [(key1187, -24), (key1025, 6), (key1103, 6), (key1103, 6), (key990, 6)]

def rawRow10760 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key990, 6), (key1025, 6), (key1103, 6)]

def rawRow10761 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key990, 6), (key1103, 6), (key1025, 6)]

def rawRow10762 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1025, 6), (key990, 6), (key1103, 6)]

def rawRow10763 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1025, 6), (key1103, 6), (key990, 6)]

def rawRow10764 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1103, 6), (key990, 6), (key1025, 6)]

def rawRow10765 : Integer.Sparse Key := [(key1187, -24), (key1103, 6), (key1103, 6), (key1025, 6), (key990, 6)]

def rawRow10766 : Integer.Sparse Key := [(key1107, -6), (key1112, -6), (key1121, -6), (key1148, -6), (key994, 2), (key999, 2), (key1013, 2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1069, 2), (key1148, 2), (key1210, 2)]

def rawRow10767 : Integer.Sparse Key := [(key1112, -6), (key1107, -6), (key1121, -6), (key1148, -6), (key999, 2), (key994, 2), (key1013, 2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1069, 2), (key1210, 2), (key1148, 2)]

def rawRow10768 : Integer.Sparse Key := [(key1107, -6), (key1121, -6), (key1112, -6), (key1148, -6), (key994, 2), (key1013, 2), (key999, 2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1148, 2), (key1069, 2), (key1210, 2)]

def rawRow10769 : Integer.Sparse Key := [(key1121, -6), (key1107, -6), (key1112, -6), (key1148, -6), (key1013, 2), (key994, 2), (key999, 2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1148, 2), (key1210, 2), (key1069, 2)]

def rawRow10770 : Integer.Sparse Key := [(key1112, -6), (key1121, -6), (key1107, -6), (key1148, -6), (key999, 2), (key1013, 2), (key994, 2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1210, 2), (key1069, 2), (key1148, 2)]

def rawRow10771 : Integer.Sparse Key := [(key1121, -6), (key1112, -6), (key1107, -6), (key1148, -6), (key1013, 2), (key999, 2), (key994, 2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1210, 2), (key1148, 2), (key1069, 2)]

def rawRow10772 : Integer.Sparse Key := [(key1107, -6), (key1112, -6), (key1148, -6), (key1121, -6), (key1029, 2), (key1034, 2), (key1069, 2), (key994, 2), (key999, 2), (key1107, 2), (key1191, 2), (key1148, 2), (key1210, 2), (key1013, 2), (key1121, 2), (key1197, 2)]

def rawRow10773 : Integer.Sparse Key := [(key1112, -6), (key1107, -6), (key1148, -6), (key1121, -6), (key1034, 2), (key1029, 2), (key1069, 2), (key999, 2), (key994, 2), (key1191, 2), (key1107, 2), (key1210, 2), (key1148, 2), (key1013, 2), (key1197, 2), (key1121, 2)]

def rawRow10774 : Integer.Sparse Key := [(key1107, -6), (key1148, -6), (key1112, -6), (key1121, -6), (key1029, 2), (key1069, 2), (key1034, 2), (key1107, 2), (key1148, 2), (key994, 2), (key1210, 2), (key999, 2), (key1191, 2), (key1121, 2), (key1013, 2), (key1197, 2)]

def rawRow10775 : Integer.Sparse Key := [(key1148, -6), (key1107, -6), (key1112, -6), (key1121, -6), (key1069, 2), (key1029, 2), (key1034, 2), (key1148, 2), (key1107, 2), (key1210, 2), (key994, 2), (key1191, 2), (key999, 2), (key1121, 2), (key1197, 2), (key1013, 2)]

def rawRow10776 : Integer.Sparse Key := [(key1112, -6), (key1148, -6), (key1107, -6), (key1121, -6), (key1034, 2), (key1069, 2), (key1029, 2), (key1191, 2), (key1210, 2), (key999, 2), (key1148, 2), (key994, 2), (key1107, 2), (key1197, 2), (key1013, 2), (key1121, 2)]

def rawRow10777 : Integer.Sparse Key := [(key1148, -6), (key1112, -6), (key1107, -6), (key1121, -6), (key1069, 2), (key1034, 2), (key1029, 2), (key1210, 2), (key1191, 2), (key1148, 2), (key999, 2), (key1107, 2), (key994, 2), (key1197, 2), (key1121, 2), (key1013, 2)]

def rawRow10778 : Integer.Sparse Key := [(key1107, -6), (key1121, -6), (key1148, -6), (key1112, -6), (key1107, 2), (key1121, 2), (key1148, 2), (key994, 2), (key1013, 2), (key1029, 2), (key1197, 2), (key1069, 2), (key1210, 2), (key999, 2), (key1034, 2), (key1191, 2)]

def rawRow10779 : Integer.Sparse Key := [(key1121, -6), (key1107, -6), (key1148, -6), (key1112, -6), (key1121, 2), (key1107, 2), (key1148, 2), (key1013, 2), (key994, 2), (key1197, 2), (key1029, 2), (key1210, 2), (key1069, 2), (key999, 2), (key1191, 2), (key1034, 2)]

def rawRow10780 : Integer.Sparse Key := [(key1107, -6), (key1148, -6), (key1121, -6), (key1112, -6), (key1107, 2), (key1148, 2), (key1121, 2), (key1029, 2), (key1069, 2), (key994, 2), (key1210, 2), (key1013, 2), (key1197, 2), (key1034, 2), (key999, 2), (key1191, 2)]

def rawRow10781 : Integer.Sparse Key := [(key1148, -6), (key1107, -6), (key1121, -6), (key1112, -6), (key1148, 2), (key1107, 2), (key1121, 2), (key1069, 2), (key1029, 2), (key1210, 2), (key994, 2), (key1197, 2), (key1013, 2), (key1034, 2), (key1191, 2), (key999, 2)]

def rawRow10782 : Integer.Sparse Key := [(key1121, -6), (key1148, -6), (key1107, -6), (key1112, -6), (key1121, 2), (key1148, 2), (key1107, 2), (key1197, 2), (key1210, 2), (key1013, 2), (key1069, 2), (key994, 2), (key1029, 2), (key1191, 2), (key999, 2), (key1034, 2)]

def rawRow10783 : Integer.Sparse Key := [(key1148, -6), (key1121, -6), (key1107, -6), (key1112, -6), (key1148, 2), (key1121, 2), (key1107, 2), (key1210, 2), (key1197, 2), (key1069, 2), (key1013, 2), (key1029, 2), (key994, 2), (key1191, 2), (key1034, 2), (key999, 2)]

def rawRow10784 : Integer.Sparse Key := [(key1112, -6), (key1121, -6), (key1148, -6), (key1107, -6), (key1191, 2), (key1197, 2), (key1210, 2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key994, 2), (key1029, 2), (key1107, 2)]

def rawRow10785 : Integer.Sparse Key := [(key1121, -6), (key1112, -6), (key1148, -6), (key1107, -6), (key1197, 2), (key1191, 2), (key1210, 2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key994, 2), (key1107, 2), (key1029, 2)]

def rawRow10786 : Integer.Sparse Key := [(key1112, -6), (key1148, -6), (key1121, -6), (key1107, -6), (key1191, 2), (key1210, 2), (key1197, 2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1029, 2), (key994, 2), (key1107, 2)]

def rawRow10787 : Integer.Sparse Key := [(key1148, -6), (key1112, -6), (key1121, -6), (key1107, -6), (key1210, 2), (key1191, 2), (key1197, 2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1029, 2), (key1107, 2), (key994, 2)]

def rawRow10788 : Integer.Sparse Key := [(key1121, -6), (key1148, -6), (key1112, -6), (key1107, -6), (key1197, 2), (key1210, 2), (key1191, 2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1107, 2), (key994, 2), (key1029, 2)]

def rawRow10789 : Integer.Sparse Key := [(key1148, -6), (key1121, -6), (key1112, -6), (key1107, -6), (key1210, 2), (key1197, 2), (key1191, 2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1107, 2), (key1029, 2), (key994, 2)]

def rawRow10790 : Integer.Sparse Key := [(key1191, -6), (key1191, -6), (key1197, -6), (key1210, -6), (key999, 2), (key999, 2), (key1013, 2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key1148, 2)]

def rawRow10791 : Integer.Sparse Key := [(key1191, -6), (key1197, -6), (key1191, -6), (key1210, -6), (key999, 2), (key1013, 2), (key999, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1148, 2), (key1069, 2), (key1148, 2)]

def rawRow10792 : Integer.Sparse Key := [(key1197, -6), (key1191, -6), (key1191, -6), (key1210, -6), (key1013, 2), (key999, 2), (key999, 2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1148, 2), (key1148, 2), (key1069, 2)]

def rawRow10793 : Integer.Sparse Key := [(key1191, -6), (key1191, -6), (key1210, -6), (key1197, -6), (key1034, 2), (key1034, 2), (key1069, 2), (key999, 2), (key999, 2), (key1112, 2), (key1112, 2), (key1148, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1121, 2)]

def rawRow10794 : Integer.Sparse Key := [(key1191, -6), (key1210, -6), (key1191, -6), (key1197, -6), (key1034, 2), (key1069, 2), (key1034, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1148, 2), (key999, 2), (key1112, 2), (key1121, 2), (key1013, 2), (key1121, 2)]

def rawRow10795 : Integer.Sparse Key := [(key1210, -6), (key1191, -6), (key1191, -6), (key1197, -6), (key1069, 2), (key1034, 2), (key1034, 2), (key1148, 2), (key1112, 2), (key1148, 2), (key999, 2), (key1112, 2), (key999, 2), (key1121, 2), (key1121, 2), (key1013, 2)]

def rawRow10796 : Integer.Sparse Key := [(key1191, -6), (key1197, -6), (key1210, -6), (key1191, -6), (key1112, 2), (key1121, 2), (key1148, 2), (key999, 2), (key1013, 2), (key1034, 2), (key1121, 2), (key1069, 2), (key1148, 2), (key999, 2), (key1034, 2), (key1112, 2)]

def rawRow10797 : Integer.Sparse Key := [(key1197, -6), (key1191, -6), (key1210, -6), (key1191, -6), (key1121, 2), (key1112, 2), (key1148, 2), (key1013, 2), (key999, 2), (key1121, 2), (key1034, 2), (key1148, 2), (key1069, 2), (key999, 2), (key1112, 2), (key1034, 2)]

def rawRow10798 : Integer.Sparse Key := [(key1191, -6), (key1210, -6), (key1197, -6), (key1191, -6), (key1112, 2), (key1148, 2), (key1121, 2), (key1034, 2), (key1069, 2), (key999, 2), (key1148, 2), (key1013, 2), (key1121, 2), (key1034, 2), (key999, 2), (key1112, 2)]

def rawRow10799 : Integer.Sparse Key := [(key1210, -6), (key1191, -6), (key1197, -6), (key1191, -6), (key1148, 2), (key1112, 2), (key1121, 2), (key1069, 2), (key1034, 2), (key1148, 2), (key999, 2), (key1121, 2), (key1013, 2), (key1034, 2), (key1112, 2), (key999, 2)]

def rawRow10800 : Integer.Sparse Key := [(key1197, -6), (key1210, -6), (key1191, -6), (key1191, -6), (key1121, 2), (key1148, 2), (key1112, 2), (key1121, 2), (key1148, 2), (key1013, 2), (key1069, 2), (key999, 2), (key1034, 2), (key1112, 2), (key999, 2), (key1034, 2)]

def rawRow10801 : Integer.Sparse Key := [(key1210, -6), (key1197, -6), (key1191, -6), (key1191, -6), (key1148, 2), (key1121, 2), (key1112, 2), (key1148, 2), (key1121, 2), (key1069, 2), (key1013, 2), (key1034, 2), (key999, 2), (key1112, 2), (key1034, 2), (key999, 2)]

def rawRow10802 : Integer.Sparse Key := [(key2623, -6), (key2777, -6), (key2850, -6), (key2864, -6), (key2607, 2), (key2623, 2), (key2634, 2), (key2662, 2), (key2697, 2), (key2720, 2), (key2777, 2), (key2788, 2), (key2800, 2), (key2823, 2), (key2854, 2), (key2864, 2)]

def rawRow10803 : Integer.Sparse Key := [(key2623, -6), (key2777, -6), (key2864, -6), (key2850, -6), (key2607, 2), (key2634, 2), (key2623, 2), (key2662, 2), (key2720, 2), (key2697, 2), (key2788, 2), (key2777, 2), (key2823, 2), (key2800, 2), (key2864, 2), (key2854, 2)]

def rawRow10804 : Integer.Sparse Key := [(key2623, -6), (key2850, -6), (key2777, -6), (key2864, -6), (key2623, 2), (key2607, 2), (key2634, 2), (key2697, 2), (key2662, 2), (key2720, 2), (key2800, 2), (key2854, 2), (key2777, 2), (key2864, 2), (key2788, 2), (key2823, 2)]

def rawRow10805 : Integer.Sparse Key := [(key2623, -6), (key2850, -6), (key2864, -6), (key2777, -6), (key2623, 2), (key2634, 2), (key2607, 2), (key2697, 2), (key2720, 2), (key2662, 2), (key2854, 2), (key2800, 2), (key2864, 2), (key2777, 2), (key2823, 2), (key2788, 2)]

def rawRow10806 : Integer.Sparse Key := [(key2623, -6), (key2864, -6), (key2777, -6), (key2850, -6), (key2634, 2), (key2607, 2), (key2623, 2), (key2720, 2), (key2662, 2), (key2697, 2), (key2823, 2), (key2864, 2), (key2788, 2), (key2854, 2), (key2777, 2), (key2800, 2)]

def rawRow10807 : Integer.Sparse Key := [(key2623, -6), (key2864, -6), (key2850, -6), (key2777, -6), (key2634, 2), (key2623, 2), (key2607, 2), (key2720, 2), (key2697, 2), (key2662, 2), (key2864, 2), (key2823, 2), (key2854, 2), (key2788, 2), (key2800, 2), (key2777, 2)]

def rawRow10808 : Integer.Sparse Key := [(key2777, -6), (key2623, -6), (key2850, -6), (key2864, -6), (key2662, 2), (key2777, 2), (key2788, 2), (key2607, 2), (key2800, 2), (key2823, 2), (key2623, 2), (key2634, 2), (key2697, 2), (key2720, 2), (key2854, 2), (key2864, 2)]

def rawRow10809 : Integer.Sparse Key := [(key2777, -6), (key2623, -6), (key2864, -6), (key2850, -6), (key2662, 2), (key2788, 2), (key2777, 2), (key2607, 2), (key2823, 2), (key2800, 2), (key2634, 2), (key2623, 2), (key2720, 2), (key2697, 2), (key2864, 2), (key2854, 2)]

def rawRow10810 : Integer.Sparse Key := [(key2777, -6), (key2850, -6), (key2623, -6), (key2864, -6), (key2777, 2), (key2662, 2), (key2788, 2), (key2800, 2), (key2607, 2), (key2823, 2), (key2697, 2), (key2854, 2), (key2623, 2), (key2864, 2), (key2634, 2), (key2720, 2)]

def rawRow10811 : Integer.Sparse Key := [(key2777, -6), (key2850, -6), (key2864, -6), (key2623, -6), (key2777, 2), (key2788, 2), (key2662, 2), (key2800, 2), (key2823, 2), (key2607, 2), (key2854, 2), (key2697, 2), (key2864, 2), (key2623, 2), (key2720, 2), (key2634, 2)]

def rawRow10812 : Integer.Sparse Key := [(key2777, -6), (key2864, -6), (key2623, -6), (key2850, -6), (key2788, 2), (key2662, 2), (key2777, 2), (key2823, 2), (key2607, 2), (key2800, 2), (key2720, 2), (key2864, 2), (key2634, 2), (key2854, 2), (key2623, 2), (key2697, 2)]

def rawRow10813 : Integer.Sparse Key := [(key2777, -6), (key2864, -6), (key2850, -6), (key2623, -6), (key2788, 2), (key2777, 2), (key2662, 2), (key2823, 2), (key2800, 2), (key2607, 2), (key2864, 2), (key2720, 2), (key2854, 2), (key2634, 2), (key2697, 2), (key2623, 2)]

def rawRow10814 : Integer.Sparse Key := [(key2850, -6), (key2623, -6), (key2777, -6), (key2864, -6), (key2697, 2), (key2800, 2), (key2854, 2), (key2623, 2), (key2777, 2), (key2864, 2), (key2607, 2), (key2634, 2), (key2662, 2), (key2720, 2), (key2788, 2), (key2823, 2)]

def rawRow10815 : Integer.Sparse Key := [(key2850, -6), (key2623, -6), (key2864, -6), (key2777, -6), (key2697, 2), (key2854, 2), (key2800, 2), (key2623, 2), (key2864, 2), (key2777, 2), (key2634, 2), (key2607, 2), (key2720, 2), (key2662, 2), (key2823, 2), (key2788, 2)]

def rawRow10816 : Integer.Sparse Key := [(key2850, -6), (key2777, -6), (key2623, -6), (key2864, -6), (key2800, 2), (key2697, 2), (key2854, 2), (key2777, 2), (key2623, 2), (key2864, 2), (key2662, 2), (key2788, 2), (key2607, 2), (key2823, 2), (key2634, 2), (key2720, 2)]

def rawRow10817 : Integer.Sparse Key := [(key2850, -6), (key2777, -6), (key2864, -6), (key2623, -6), (key2800, 2), (key2854, 2), (key2697, 2), (key2777, 2), (key2864, 2), (key2623, 2), (key2788, 2), (key2662, 2), (key2823, 2), (key2607, 2), (key2720, 2), (key2634, 2)]

def rawRow10818 : Integer.Sparse Key := [(key2850, -6), (key2864, -6), (key2623, -6), (key2777, -6), (key2854, 2), (key2697, 2), (key2800, 2), (key2864, 2), (key2623, 2), (key2777, 2), (key2720, 2), (key2823, 2), (key2634, 2), (key2788, 2), (key2607, 2), (key2662, 2)]

def rawRow10819 : Integer.Sparse Key := [(key2850, -6), (key2864, -6), (key2777, -6), (key2623, -6), (key2854, 2), (key2800, 2), (key2697, 2), (key2864, 2), (key2777, 2), (key2623, 2), (key2823, 2), (key2720, 2), (key2788, 2), (key2634, 2), (key2662, 2), (key2607, 2)]

def rawRow10820 : Integer.Sparse Key := [(key2864, -6), (key2623, -6), (key2777, -6), (key2850, -6), (key2720, 2), (key2823, 2), (key2864, 2), (key2634, 2), (key2788, 2), (key2854, 2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

def rawRow10821 : Integer.Sparse Key := [(key2864, -6), (key2623, -6), (key2850, -6), (key2777, -6), (key2720, 2), (key2864, 2), (key2823, 2), (key2634, 2), (key2854, 2), (key2788, 2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

def rawRow10822 : Integer.Sparse Key := [(key2864, -6), (key2777, -6), (key2623, -6), (key2850, -6), (key2823, 2), (key2720, 2), (key2864, 2), (key2788, 2), (key2634, 2), (key2854, 2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

def rawRow10823 : Integer.Sparse Key := [(key2864, -6), (key2777, -6), (key2850, -6), (key2623, -6), (key2823, 2), (key2864, 2), (key2720, 2), (key2788, 2), (key2854, 2), (key2634, 2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

def rawRow10824 : Integer.Sparse Key := [(key2864, -6), (key2850, -6), (key2623, -6), (key2777, -6), (key2864, 2), (key2720, 2), (key2823, 2), (key2854, 2), (key2634, 2), (key2788, 2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

def rawRow10825 : Integer.Sparse Key := [(key2864, -6), (key2850, -6), (key2777, -6), (key2623, -6), (key2864, 2), (key2823, 2), (key2720, 2), (key2854, 2), (key2788, 2), (key2634, 2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

def rawRow10826 : Integer.Sparse Key := [(key2634, -6), (key2788, -6), (key2854, -6), (key2854, -6), (key2607, 2), (key2623, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2697, 2), (key2777, 2), (key2777, 2), (key2800, 2), (key2800, 2), (key2850, 2), (key2850, 2)]

def rawRow10827 : Integer.Sparse Key := [(key2634, -6), (key2854, -6), (key2788, -6), (key2854, -6), (key2623, 2), (key2607, 2), (key2623, 2), (key2697, 2), (key2662, 2), (key2697, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2850, 2), (key2777, 2), (key2800, 2)]

def rawRow10828 : Integer.Sparse Key := [(key2634, -6), (key2854, -6), (key2854, -6), (key2788, -6), (key2623, 2), (key2623, 2), (key2607, 2), (key2697, 2), (key2697, 2), (key2662, 2), (key2850, 2), (key2800, 2), (key2850, 2), (key2777, 2), (key2800, 2), (key2777, 2)]

def rawRow10829 : Integer.Sparse Key := [(key2788, -6), (key2634, -6), (key2854, -6), (key2854, -6), (key2662, 2), (key2777, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2800, 2), (key2623, 2), (key2623, 2), (key2697, 2), (key2697, 2), (key2850, 2), (key2850, 2)]

def rawRow10830 : Integer.Sparse Key := [(key2788, -6), (key2854, -6), (key2634, -6), (key2854, -6), (key2777, 2), (key2662, 2), (key2777, 2), (key2800, 2), (key2607, 2), (key2800, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2850, 2), (key2623, 2), (key2697, 2)]

def rawRow10831 : Integer.Sparse Key := [(key2788, -6), (key2854, -6), (key2854, -6), (key2634, -6), (key2777, 2), (key2777, 2), (key2662, 2), (key2800, 2), (key2800, 2), (key2607, 2), (key2850, 2), (key2697, 2), (key2850, 2), (key2623, 2), (key2697, 2), (key2623, 2)]

def rawRow10832 : Integer.Sparse Key := [(key2854, -6), (key2634, -6), (key2788, -6), (key2854, -6), (key2697, 2), (key2800, 2), (key2850, 2), (key2623, 2), (key2777, 2), (key2850, 2), (key2607, 2), (key2623, 2), (key2662, 2), (key2697, 2), (key2777, 2), (key2800, 2)]

def rawRow10833 : Integer.Sparse Key := [(key2854, -6), (key2634, -6), (key2854, -6), (key2788, -6), (key2697, 2), (key2850, 2), (key2800, 2), (key2623, 2), (key2850, 2), (key2777, 2), (key2623, 2), (key2607, 2), (key2697, 2), (key2662, 2), (key2800, 2), (key2777, 2)]

def rawRow10834 : Integer.Sparse Key := [(key2854, -6), (key2788, -6), (key2634, -6), (key2854, -6), (key2800, 2), (key2697, 2), (key2850, 2), (key2777, 2), (key2623, 2), (key2850, 2), (key2662, 2), (key2777, 2), (key2607, 2), (key2800, 2), (key2623, 2), (key2697, 2)]

def rawRow10835 : Integer.Sparse Key := [(key2854, -6), (key2788, -6), (key2854, -6), (key2634, -6), (key2800, 2), (key2850, 2), (key2697, 2), (key2777, 2), (key2850, 2), (key2623, 2), (key2777, 2), (key2662, 2), (key2800, 2), (key2607, 2), (key2697, 2), (key2623, 2)]

def rawRow10836 : Integer.Sparse Key := [(key2854, -6), (key2854, -6), (key2634, -6), (key2788, -6), (key2850, 2), (key2697, 2), (key2800, 2), (key2850, 2), (key2623, 2), (key2777, 2), (key2697, 2), (key2800, 2), (key2623, 2), (key2777, 2), (key2607, 2), (key2662, 2)]

def rawRow10837 : Integer.Sparse Key := [(key2854, -6), (key2854, -6), (key2788, -6), (key2634, -6), (key2850, 2), (key2800, 2), (key2697, 2), (key2850, 2), (key2777, 2), (key2623, 2), (key2800, 2), (key2697, 2), (key2777, 2), (key2623, 2), (key2662, 2), (key2607, 2)]

def rawRow10838 : Integer.Sparse Key := [(key2465, -6), (key2469, -6), (key2477, -6), (key2500, -6), (key2371, 2), (key2375, 2), (key2387, 2), (key2399, 2), (key2403, 2), (key2465, 2), (key2536, 2), (key2477, 2), (key2541, 2), (key2434, 2), (key2500, 2), (key2552, 2)]

def rawRow10839 : Integer.Sparse Key := [(key2469, -6), (key2465, -6), (key2477, -6), (key2500, -6), (key2375, 2), (key2371, 2), (key2387, 2), (key2403, 2), (key2399, 2), (key2536, 2), (key2465, 2), (key2541, 2), (key2477, 2), (key2434, 2), (key2552, 2), (key2500, 2)]

def rawRow10840 : Integer.Sparse Key := [(key2465, -6), (key2477, -6), (key2469, -6), (key2500, -6), (key2371, 2), (key2387, 2), (key2375, 2), (key2465, 2), (key2477, 2), (key2399, 2), (key2541, 2), (key2403, 2), (key2536, 2), (key2500, 2), (key2434, 2), (key2552, 2)]

def rawRow10841 : Integer.Sparse Key := [(key2477, -6), (key2465, -6), (key2469, -6), (key2500, -6), (key2387, 2), (key2371, 2), (key2375, 2), (key2477, 2), (key2465, 2), (key2541, 2), (key2399, 2), (key2536, 2), (key2403, 2), (key2500, 2), (key2552, 2), (key2434, 2)]

def rawRow10842 : Integer.Sparse Key := [(key2469, -6), (key2477, -6), (key2465, -6), (key2500, -6), (key2375, 2), (key2387, 2), (key2371, 2), (key2536, 2), (key2541, 2), (key2403, 2), (key2477, 2), (key2399, 2), (key2465, 2), (key2552, 2), (key2434, 2), (key2500, 2)]

def rawRow10843 : Integer.Sparse Key := [(key2477, -6), (key2469, -6), (key2465, -6), (key2500, -6), (key2387, 2), (key2375, 2), (key2371, 2), (key2541, 2), (key2536, 2), (key2477, 2), (key2403, 2), (key2465, 2), (key2399, 2), (key2552, 2), (key2500, 2), (key2434, 2)]

def rawRow10844 : Integer.Sparse Key := [(key2465, -6), (key2469, -6), (key2500, -6), (key2477, -6), (key2399, 2), (key2403, 2), (key2434, 2), (key2371, 2), (key2375, 2), (key2465, 2), (key2536, 2), (key2500, 2), (key2552, 2), (key2387, 2), (key2477, 2), (key2541, 2)]

def rawRow10845 : Integer.Sparse Key := [(key2469, -6), (key2465, -6), (key2500, -6), (key2477, -6), (key2403, 2), (key2399, 2), (key2434, 2), (key2375, 2), (key2371, 2), (key2536, 2), (key2465, 2), (key2552, 2), (key2500, 2), (key2387, 2), (key2541, 2), (key2477, 2)]

def rawRow10846 : Integer.Sparse Key := [(key2465, -6), (key2500, -6), (key2469, -6), (key2477, -6), (key2399, 2), (key2434, 2), (key2403, 2), (key2465, 2), (key2500, 2), (key2371, 2), (key2552, 2), (key2375, 2), (key2536, 2), (key2477, 2), (key2387, 2), (key2541, 2)]

def rawRow10847 : Integer.Sparse Key := [(key2500, -6), (key2465, -6), (key2469, -6), (key2477, -6), (key2434, 2), (key2399, 2), (key2403, 2), (key2500, 2), (key2465, 2), (key2552, 2), (key2371, 2), (key2536, 2), (key2375, 2), (key2477, 2), (key2541, 2), (key2387, 2)]

def rawRow10848 : Integer.Sparse Key := [(key2469, -6), (key2500, -6), (key2465, -6), (key2477, -6), (key2403, 2), (key2434, 2), (key2399, 2), (key2536, 2), (key2552, 2), (key2375, 2), (key2500, 2), (key2371, 2), (key2465, 2), (key2541, 2), (key2387, 2), (key2477, 2)]

def rawRow10849 : Integer.Sparse Key := [(key2500, -6), (key2469, -6), (key2465, -6), (key2477, -6), (key2434, 2), (key2403, 2), (key2399, 2), (key2552, 2), (key2536, 2), (key2500, 2), (key2375, 2), (key2465, 2), (key2371, 2), (key2541, 2), (key2477, 2), (key2387, 2)]

def rawRow10850 : Integer.Sparse Key := [(key2465, -6), (key2477, -6), (key2500, -6), (key2469, -6), (key2465, 2), (key2477, 2), (key2500, 2), (key2371, 2), (key2387, 2), (key2399, 2), (key2541, 2), (key2434, 2), (key2552, 2), (key2375, 2), (key2403, 2), (key2536, 2)]

def rawRow10851 : Integer.Sparse Key := [(key2477, -6), (key2465, -6), (key2500, -6), (key2469, -6), (key2477, 2), (key2465, 2), (key2500, 2), (key2387, 2), (key2371, 2), (key2541, 2), (key2399, 2), (key2552, 2), (key2434, 2), (key2375, 2), (key2536, 2), (key2403, 2)]

def rawRow10852 : Integer.Sparse Key := [(key2465, -6), (key2500, -6), (key2477, -6), (key2469, -6), (key2465, 2), (key2500, 2), (key2477, 2), (key2399, 2), (key2434, 2), (key2371, 2), (key2552, 2), (key2387, 2), (key2541, 2), (key2403, 2), (key2375, 2), (key2536, 2)]

def rawRow10853 : Integer.Sparse Key := [(key2500, -6), (key2465, -6), (key2477, -6), (key2469, -6), (key2500, 2), (key2465, 2), (key2477, 2), (key2434, 2), (key2399, 2), (key2552, 2), (key2371, 2), (key2541, 2), (key2387, 2), (key2403, 2), (key2536, 2), (key2375, 2)]

def rawRow10854 : Integer.Sparse Key := [(key2477, -6), (key2500, -6), (key2465, -6), (key2469, -6), (key2477, 2), (key2500, 2), (key2465, 2), (key2541, 2), (key2552, 2), (key2387, 2), (key2434, 2), (key2371, 2), (key2399, 2), (key2536, 2), (key2375, 2), (key2403, 2)]

def rawRow10855 : Integer.Sparse Key := [(key2500, -6), (key2477, -6), (key2465, -6), (key2469, -6), (key2500, 2), (key2477, 2), (key2465, 2), (key2552, 2), (key2541, 2), (key2434, 2), (key2387, 2), (key2399, 2), (key2371, 2), (key2536, 2), (key2403, 2), (key2375, 2)]

def rawRow10856 : Integer.Sparse Key := [(key2469, -6), (key2477, -6), (key2500, -6), (key2465, -6), (key2536, 2), (key2541, 2), (key2552, 2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2371, 2), (key2399, 2), (key2465, 2)]

def rawRow10857 : Integer.Sparse Key := [(key2477, -6), (key2469, -6), (key2500, -6), (key2465, -6), (key2541, 2), (key2536, 2), (key2552, 2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2371, 2), (key2465, 2), (key2399, 2)]

def rawRow10858 : Integer.Sparse Key := [(key2469, -6), (key2500, -6), (key2477, -6), (key2465, -6), (key2536, 2), (key2552, 2), (key2541, 2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2399, 2), (key2371, 2), (key2465, 2)]

def rawRow10859 : Integer.Sparse Key := [(key2500, -6), (key2469, -6), (key2477, -6), (key2465, -6), (key2552, 2), (key2536, 2), (key2541, 2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2399, 2), (key2465, 2), (key2371, 2)]

def rawRow10860 : Integer.Sparse Key := [(key2477, -6), (key2500, -6), (key2469, -6), (key2465, -6), (key2541, 2), (key2552, 2), (key2536, 2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2465, 2), (key2371, 2), (key2399, 2)]

def rawRow10861 : Integer.Sparse Key := [(key2500, -6), (key2477, -6), (key2469, -6), (key2465, -6), (key2552, 2), (key2541, 2), (key2536, 2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2465, 2), (key2399, 2), (key2371, 2)]

def rawRow10862 : Integer.Sparse Key := [(key2536, -6), (key2536, -6), (key2541, -6), (key2552, -6), (key2375, 2), (key2375, 2), (key2387, 2), (key2403, 2), (key2403, 2), (key2469, 2), (key2469, 2), (key2477, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2500, 2)]

def rawRow10863 : Integer.Sparse Key := [(key2536, -6), (key2541, -6), (key2536, -6), (key2552, -6), (key2375, 2), (key2387, 2), (key2375, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2500, 2), (key2434, 2), (key2500, 2)]

def rawRow10864 : Integer.Sparse Key := [(key2541, -6), (key2536, -6), (key2536, -6), (key2552, -6), (key2387, 2), (key2375, 2), (key2375, 2), (key2477, 2), (key2469, 2), (key2477, 2), (key2403, 2), (key2469, 2), (key2403, 2), (key2500, 2), (key2500, 2), (key2434, 2)]

def rawRow10865 : Integer.Sparse Key := [(key2536, -6), (key2536, -6), (key2552, -6), (key2541, -6), (key2403, 2), (key2403, 2), (key2434, 2), (key2375, 2), (key2375, 2), (key2469, 2), (key2469, 2), (key2500, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2477, 2)]

def rawRow10866 : Integer.Sparse Key := [(key2536, -6), (key2552, -6), (key2536, -6), (key2541, -6), (key2403, 2), (key2434, 2), (key2403, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2477, 2), (key2387, 2), (key2477, 2)]

def rawRow10867 : Integer.Sparse Key := [(key2552, -6), (key2536, -6), (key2536, -6), (key2541, -6), (key2434, 2), (key2403, 2), (key2403, 2), (key2500, 2), (key2469, 2), (key2500, 2), (key2375, 2), (key2469, 2), (key2375, 2), (key2477, 2), (key2477, 2), (key2387, 2)]

def rawRow10868 : Integer.Sparse Key := [(key2536, -6), (key2541, -6), (key2552, -6), (key2536, -6), (key2469, 2), (key2477, 2), (key2500, 2), (key2375, 2), (key2387, 2), (key2403, 2), (key2477, 2), (key2434, 2), (key2500, 2), (key2375, 2), (key2403, 2), (key2469, 2)]

def rawRow10869 : Integer.Sparse Key := [(key2541, -6), (key2536, -6), (key2552, -6), (key2536, -6), (key2477, 2), (key2469, 2), (key2500, 2), (key2387, 2), (key2375, 2), (key2477, 2), (key2403, 2), (key2500, 2), (key2434, 2), (key2375, 2), (key2469, 2), (key2403, 2)]

def rawRow10870 : Integer.Sparse Key := [(key2536, -6), (key2552, -6), (key2541, -6), (key2536, -6), (key2469, 2), (key2500, 2), (key2477, 2), (key2403, 2), (key2434, 2), (key2375, 2), (key2500, 2), (key2387, 2), (key2477, 2), (key2403, 2), (key2375, 2), (key2469, 2)]

def rawRow10871 : Integer.Sparse Key := [(key2552, -6), (key2536, -6), (key2541, -6), (key2536, -6), (key2500, 2), (key2469, 2), (key2477, 2), (key2434, 2), (key2403, 2), (key2500, 2), (key2375, 2), (key2477, 2), (key2387, 2), (key2403, 2), (key2469, 2), (key2375, 2)]

def rawRow10872 : Integer.Sparse Key := [(key2541, -6), (key2552, -6), (key2536, -6), (key2536, -6), (key2477, 2), (key2500, 2), (key2469, 2), (key2477, 2), (key2500, 2), (key2387, 2), (key2434, 2), (key2375, 2), (key2403, 2), (key2469, 2), (key2375, 2), (key2403, 2)]

def rawRow10873 : Integer.Sparse Key := [(key2552, -6), (key2541, -6), (key2536, -6), (key2536, -6), (key2500, 2), (key2477, 2), (key2469, 2), (key2500, 2), (key2477, 2), (key2434, 2), (key2387, 2), (key2403, 2), (key2375, 2), (key2469, 2), (key2403, 2), (key2375, 2)]

def rawRow10874 : Integer.Sparse Key := [(key2625, -2), (key2629, -2), (key2637, -2), (key2699, -2), (key2703, -2), (key2852, -2), (key2973, -2), (key2857, -2), (key2975, -2), (key2723, -2), (key2867, -2), (key2982, -2), (key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2699, 1), (key2736, 1), (key2802, 1), (key2949, 1), (key2896, 1), (key2975, 1), (key2723, 1), (key2746, 1), (key2826, 1), (key2959, 1), (key2903, 1), (key2982, 1)]

def rawRow10875 : Integer.Sparse Key := [(key2629, -2), (key2625, -2), (key2637, -2), (key2703, -2), (key2699, -2), (key2973, -2), (key2852, -2), (key2975, -2), (key2857, -2), (key2723, -2), (key2982, -2), (key2867, -2), (key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2736, 1), (key2699, 1), (key2949, 1), (key2802, 1), (key2975, 1), (key2896, 1), (key2746, 1), (key2723, 1), (key2959, 1), (key2826, 1), (key2982, 1), (key2903, 1)]

def rawRow10876 : Integer.Sparse Key := [(key2625, -2), (key2637, -2), (key2629, -2), (key2852, -2), (key2857, -2), (key2699, -2), (key2975, -2), (key2703, -2), (key2973, -2), (key2867, -2), (key2723, -2), (key2982, -2), (key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2802, 1), (key2896, 1), (key2699, 1), (key2975, 1), (key2736, 1), (key2949, 1), (key2826, 1), (key2903, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2959, 1)]

def rawRow10877 : Integer.Sparse Key := [(key2637, -2), (key2625, -2), (key2629, -2), (key2857, -2), (key2852, -2), (key2975, -2), (key2699, -2), (key2973, -2), (key2703, -2), (key2867, -2), (key2982, -2), (key2723, -2), (key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2896, 1), (key2802, 1), (key2975, 1), (key2699, 1), (key2949, 1), (key2736, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2959, 1), (key2746, 1)]

def rawRow10878 : Integer.Sparse Key := [(key2629, -2), (key2637, -2), (key2625, -2), (key2973, -2), (key2975, -2), (key2703, -2), (key2857, -2), (key2699, -2), (key2852, -2), (key2982, -2), (key2723, -2), (key2867, -2), (key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2949, 1), (key2975, 1), (key2736, 1), (key2896, 1), (key2699, 1), (key2802, 1), (key2959, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2723, 1), (key2826, 1)]

def rawRow10879 : Integer.Sparse Key := [(key2637, -2), (key2629, -2), (key2625, -2), (key2975, -2), (key2973, -2), (key2857, -2), (key2703, -2), (key2852, -2), (key2699, -2), (key2982, -2), (key2867, -2), (key2723, -2), (key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2975, 1), (key2949, 1), (key2896, 1), (key2736, 1), (key2802, 1), (key2699, 1), (key2982, 1), (key2959, 1), (key2903, 1), (key2746, 1), (key2826, 1), (key2723, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10880 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2625, -2), (key2629, -2), (key2852, -2), (key2973, -2), (key2867, -2), (key2982, -2), (key2637, -2), (key2857, -2), (key2975, -2), (key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1)]

def rawRow10881 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2629, -2), (key2625, -2), (key2973, -2), (key2852, -2), (key2982, -2), (key2867, -2), (key2637, -2), (key2975, -2), (key2857, -2), (key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1)]

def rawRow10882 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2852, -2), (key2867, -2), (key2625, -2), (key2982, -2), (key2629, -2), (key2973, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1)]

def rawRow10883 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2867, -2), (key2852, -2), (key2982, -2), (key2625, -2), (key2973, -2), (key2629, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1)]

def rawRow10884 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2973, -2), (key2982, -2), (key2629, -2), (key2867, -2), (key2625, -2), (key2852, -2), (key2975, -2), (key2637, -2), (key2857, -2), (key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1)]

def rawRow10885 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2982, -2), (key2973, -2), (key2867, -2), (key2629, -2), (key2852, -2), (key2625, -2), (key2975, -2), (key2857, -2), (key2637, -2), (key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

def rawRow10886 : Integer.Sparse Key := [(key2852, -2), (key2857, -2), (key2867, -2), (key2625, -2), (key2637, -2), (key2699, -2), (key2975, -2), (key2723, -2), (key2982, -2), (key2629, -2), (key2703, -2), (key2973, -2), (key2779, 1), (key2791, 1), (key2802, 1), (key2896, 1), (key2826, 1), (key2903, 1), (key2625, 1), (key2637, 1), (key2699, 1), (key2975, 1), (key2723, 1), (key2982, 1), (key2609, 1), (key2652, 1), (key2664, 1), (key2942, 1), (key2746, 1), (key2959, 1), (key2613, 1), (key2647, 1), (key2668, 1), (key2937, 1), (key2736, 1), (key2949, 1)]

def rawRow10887 : Integer.Sparse Key := [(key2857, -2), (key2852, -2), (key2867, -2), (key2637, -2), (key2625, -2), (key2975, -2), (key2699, -2), (key2982, -2), (key2723, -2), (key2629, -2), (key2973, -2), (key2703, -2), (key2791, 1), (key2779, 1), (key2896, 1), (key2802, 1), (key2903, 1), (key2826, 1), (key2637, 1), (key2625, 1), (key2975, 1), (key2699, 1), (key2982, 1), (key2723, 1), (key2652, 1), (key2609, 1), (key2942, 1), (key2664, 1), (key2959, 1), (key2746, 1), (key2647, 1), (key2613, 1), (key2937, 1), (key2668, 1), (key2949, 1), (key2736, 1)]

def rawRow10888 : Integer.Sparse Key := [(key2852, -2), (key2867, -2), (key2857, -2), (key2699, -2), (key2723, -2), (key2625, -2), (key2982, -2), (key2637, -2), (key2975, -2), (key2703, -2), (key2629, -2), (key2973, -2), (key2802, 1), (key2826, 1), (key2779, 1), (key2903, 1), (key2791, 1), (key2896, 1), (key2699, 1), (key2723, 1), (key2625, 1), (key2982, 1), (key2637, 1), (key2975, 1), (key2664, 1), (key2746, 1), (key2609, 1), (key2959, 1), (key2652, 1), (key2942, 1), (key2668, 1), (key2736, 1), (key2613, 1), (key2949, 1), (key2647, 1), (key2937, 1)]

def rawRow10889 : Integer.Sparse Key := [(key2867, -2), (key2852, -2), (key2857, -2), (key2723, -2), (key2699, -2), (key2982, -2), (key2625, -2), (key2975, -2), (key2637, -2), (key2703, -2), (key2973, -2), (key2629, -2), (key2826, 1), (key2802, 1), (key2903, 1), (key2779, 1), (key2896, 1), (key2791, 1), (key2723, 1), (key2699, 1), (key2982, 1), (key2625, 1), (key2975, 1), (key2637, 1), (key2746, 1), (key2664, 1), (key2959, 1), (key2609, 1), (key2942, 1), (key2652, 1), (key2736, 1), (key2668, 1), (key2949, 1), (key2613, 1), (key2937, 1), (key2647, 1)]

def rawRow10890 : Integer.Sparse Key := [(key2857, -2), (key2867, -2), (key2852, -2), (key2975, -2), (key2982, -2), (key2637, -2), (key2723, -2), (key2625, -2), (key2699, -2), (key2973, -2), (key2629, -2), (key2703, -2), (key2896, 1), (key2903, 1), (key2791, 1), (key2826, 1), (key2779, 1), (key2802, 1), (key2975, 1), (key2982, 1), (key2637, 1), (key2723, 1), (key2625, 1), (key2699, 1), (key2942, 1), (key2959, 1), (key2652, 1), (key2746, 1), (key2609, 1), (key2664, 1), (key2937, 1), (key2949, 1), (key2647, 1), (key2736, 1), (key2613, 1), (key2668, 1)]

def rawRow10891 : Integer.Sparse Key := [(key2867, -2), (key2857, -2), (key2852, -2), (key2982, -2), (key2975, -2), (key2723, -2), (key2637, -2), (key2699, -2), (key2625, -2), (key2973, -2), (key2703, -2), (key2629, -2), (key2903, 1), (key2896, 1), (key2826, 1), (key2791, 1), (key2802, 1), (key2779, 1), (key2982, 1), (key2975, 1), (key2723, 1), (key2637, 1), (key2699, 1), (key2625, 1), (key2959, 1), (key2942, 1), (key2746, 1), (key2652, 1), (key2664, 1), (key2609, 1), (key2949, 1), (key2937, 1), (key2736, 1), (key2647, 1), (key2668, 1), (key2613, 1)]

def rawRow10892 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2629, -2), (key2637, -2), (key2703, -2), (key2857, -2), (key2723, -2), (key2867, -2), (key2625, -2), (key2699, -2), (key2852, -2), (key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1)]

def rawRow10893 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2637, -2), (key2629, -2), (key2857, -2), (key2703, -2), (key2867, -2), (key2723, -2), (key2625, -2), (key2852, -2), (key2699, -2), (key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1)]

def rawRow10894 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2703, -2), (key2723, -2), (key2629, -2), (key2867, -2), (key2637, -2), (key2857, -2), (key2699, -2), (key2625, -2), (key2852, -2), (key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1)]

def rawRow10895 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2723, -2), (key2703, -2), (key2867, -2), (key2629, -2), (key2857, -2), (key2637, -2), (key2699, -2), (key2852, -2), (key2625, -2), (key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1)]

def rawRow10896 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2857, -2), (key2867, -2), (key2637, -2), (key2723, -2), (key2629, -2), (key2703, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1)]

def rawRow10897 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2867, -2), (key2857, -2), (key2723, -2), (key2637, -2), (key2703, -2), (key2629, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1)]

def rawRow10898 : Integer.Sparse Key := [(key2647, -2), (key2647, -2), (key2652, -2), (key2736, -2), (key2736, -2), (key2894, -2), (key2894, -2), (key2896, -2), (key2896, -2), (key2746, -2), (key2903, -2), (key2903, -2), (key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2703, 1), (key2703, 1), (key2806, 1), (key2806, 1), (key2857, 1), (key2857, 1), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1)]

def rawRow10899 : Integer.Sparse Key := [(key2647, -2), (key2652, -2), (key2647, -2), (key2894, -2), (key2896, -2), (key2736, -2), (key2896, -2), (key2736, -2), (key2894, -2), (key2903, -2), (key2746, -2), (key2903, -2), (key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1)]

def rawRow10900 : Integer.Sparse Key := [(key2652, -2), (key2647, -2), (key2647, -2), (key2896, -2), (key2894, -2), (key2896, -2), (key2736, -2), (key2894, -2), (key2736, -2), (key2903, -2), (key2903, -2), (key2746, -2), (key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2857, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2703, 1), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1)]

def rawRow10901 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2647, -2), (key2647, -2), (key2894, -2), (key2894, -2), (key2903, -2), (key2903, -2), (key2652, -2), (key2896, -2), (key2896, -2), (key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1)]

def rawRow10902 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2894, -2), (key2903, -2), (key2647, -2), (key2903, -2), (key2647, -2), (key2894, -2), (key2896, -2), (key2652, -2), (key2896, -2), (key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1)]

def rawRow10903 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2903, -2), (key2894, -2), (key2903, -2), (key2647, -2), (key2894, -2), (key2647, -2), (key2896, -2), (key2896, -2), (key2652, -2), (key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1)]

def rawRow10904 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2647, -2), (key2652, -2), (key2736, -2), (key2896, -2), (key2746, -2), (key2903, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1)]

def rawRow10905 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2652, -2), (key2647, -2), (key2896, -2), (key2736, -2), (key2903, -2), (key2746, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1)]

def rawRow10906 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2736, -2), (key2746, -2), (key2647, -2), (key2903, -2), (key2652, -2), (key2896, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1)]

def rawRow10907 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2746, -2), (key2736, -2), (key2903, -2), (key2647, -2), (key2896, -2), (key2652, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1)]

def rawRow10908 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2652, -2), (key2746, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2736, -2), (key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1)]

def rawRow10909 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2903, -2), (key2896, -2), (key2746, -2), (key2652, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2647, -2), (key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1)]

def rawRow10910 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2761, 6), (key2838, 6), (key2872, 6)]

def rawRow10911 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2761, 6), (key2872, 6), (key2838, 6)]

def rawRow10912 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2838, 6), (key2761, 6), (key2872, 6)]

def rawRow10913 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2838, 6), (key2872, 6), (key2761, 6)]

def rawRow10914 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2872, 6), (key2761, 6), (key2838, 6)]

def rawRow10915 : Integer.Sparse Key := [(key2838, -24), (key2582, 6), (key2872, 6), (key2838, 6), (key2761, 6)]

def rawRow10916 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2582, 6), (key2838, 6), (key2872, 6)]

def rawRow10917 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2582, 6), (key2872, 6), (key2838, 6)]

def rawRow10918 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2838, 6), (key2582, 6), (key2872, 6)]

def rawRow10919 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2838, 6), (key2872, 6), (key2582, 6)]

def rawRow10920 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2872, 6), (key2582, 6), (key2838, 6)]

def rawRow10921 : Integer.Sparse Key := [(key2838, -24), (key2761, 6), (key2872, 6), (key2838, 6), (key2582, 6)]

def rawRow10922 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2582, 6), (key2761, 6), (key2872, 6)]

def rawRow10923 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2582, 6), (key2872, 6), (key2761, 6)]

def rawRow10924 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2761, 6), (key2582, 6), (key2872, 6)]

def rawRow10925 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2761, 6), (key2872, 6), (key2582, 6)]

def rawRow10926 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2872, 6), (key2582, 6), (key2761, 6)]

def rawRow10927 : Integer.Sparse Key := [(key2838, -24), (key2838, 6), (key2872, 6), (key2761, 6), (key2582, 6)]

def rawRow10928 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2582, 6), (key2761, 6), (key2838, 6)]

def rawRow10929 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2582, 6), (key2838, 6), (key2761, 6)]

def rawRow10930 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2761, 6), (key2582, 6), (key2838, 6)]

def rawRow10931 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2761, 6), (key2838, 6), (key2582, 6)]

def rawRow10932 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2838, 6), (key2582, 6), (key2761, 6)]

def rawRow10933 : Integer.Sparse Key := [(key2838, -24), (key2872, 6), (key2838, 6), (key2761, 6), (key2582, 6)]

def rawRow10934 : Integer.Sparse Key := [(key2872, -24), (key2582, 6), (key2761, 6), (key2838, 6), (key2838, 6)]

def rawRow10935 : Integer.Sparse Key := [(key2872, -24), (key2582, 6), (key2838, 6), (key2761, 6), (key2838, 6)]

def rawRow10936 : Integer.Sparse Key := [(key2872, -24), (key2582, 6), (key2838, 6), (key2838, 6), (key2761, 6)]

def rawRow10937 : Integer.Sparse Key := [(key2872, -24), (key2761, 6), (key2582, 6), (key2838, 6), (key2838, 6)]

def rawRow10938 : Integer.Sparse Key := [(key2872, -24), (key2761, 6), (key2838, 6), (key2582, 6), (key2838, 6)]

def rawRow10939 : Integer.Sparse Key := [(key2872, -24), (key2761, 6), (key2838, 6), (key2838, 6), (key2582, 6)]

def rawRow10940 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2582, 6), (key2761, 6), (key2838, 6)]

def rawRow10941 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2582, 6), (key2838, 6), (key2761, 6)]

def rawRow10942 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2761, 6), (key2582, 6), (key2838, 6)]

def rawRow10943 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2761, 6), (key2838, 6), (key2582, 6)]

def rawRow10944 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2838, 6), (key2582, 6), (key2761, 6)]

def rawRow10945 : Integer.Sparse Key := [(key2872, -24), (key2838, 6), (key2838, 6), (key2761, 6), (key2582, 6)]

def rawRow10946 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2852, -2), (key2894, -2), (key2857, -2), (key2896, -2), (key2826, -2), (key2867, -2), (key2903, -2), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2852, 2), (key2973, 2), (key2857, 2), (key2975, 2), (key2723, 2), (key2867, 2), (key2982, 2)]

def rawRow10947 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2791, -2), (key2806, -2), (key2802, -2), (key2894, -2), (key2852, -2), (key2896, -2), (key2857, -2), (key2826, -2), (key2903, -2), (key2867, -2), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, 2), (key2699, 2), (key2973, 2), (key2852, 2), (key2975, 2), (key2857, 2), (key2723, 2), (key2982, 2), (key2867, 2)]

def rawRow10948 : Integer.Sparse Key := [(key2779, -2), (key2791, -2), (key2783, -2), (key2852, -2), (key2857, -2), (key2802, -2), (key2896, -2), (key2806, -2), (key2894, -2), (key2867, -2), (key2826, -2), (key2903, -2), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, 2), (key2857, 2), (key2699, 2), (key2975, 2), (key2703, 2), (key2973, 2), (key2867, 2), (key2723, 2), (key2982, 2)]

def rawRow10949 : Integer.Sparse Key := [(key2791, -2), (key2779, -2), (key2783, -2), (key2857, -2), (key2852, -2), (key2896, -2), (key2802, -2), (key2894, -2), (key2806, -2), (key2867, -2), (key2903, -2), (key2826, -2), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, 2), (key2852, 2), (key2975, 2), (key2699, 2), (key2973, 2), (key2703, 2), (key2867, 2), (key2982, 2), (key2723, 2)]

def rawRow10950 : Integer.Sparse Key := [(key2783, -2), (key2791, -2), (key2779, -2), (key2894, -2), (key2896, -2), (key2806, -2), (key2857, -2), (key2802, -2), (key2852, -2), (key2903, -2), (key2826, -2), (key2867, -2), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, 2), (key2975, 2), (key2703, 2), (key2857, 2), (key2699, 2), (key2852, 2), (key2982, 2), (key2723, 2), (key2867, 2)]

def rawRow10951 : Integer.Sparse Key := [(key2791, -2), (key2783, -2), (key2779, -2), (key2896, -2), (key2894, -2), (key2857, -2), (key2806, -2), (key2852, -2), (key2802, -2), (key2903, -2), (key2867, -2), (key2826, -2), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, 2), (key2973, 2), (key2857, 2), (key2703, 2), (key2852, 2), (key2699, 2), (key2982, 2), (key2867, 2), (key2723, 2)]

def rawRow10952 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2779, -2), (key2783, -2), (key2852, -2), (key2894, -2), (key2867, -2), (key2903, -2), (key2791, -2), (key2857, -2), (key2896, -2), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, 2), (key2629, 2), (key2852, 2), (key2973, 2), (key2867, 2), (key2982, 2), (key2637, 2), (key2857, 2), (key2975, 2)]

def rawRow10953 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2783, -2), (key2779, -2), (key2894, -2), (key2852, -2), (key2903, -2), (key2867, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, 2), (key2625, 2), (key2973, 2), (key2852, 2), (key2982, 2), (key2867, 2), (key2637, 2), (key2975, 2), (key2857, 2)]

def rawRow10954 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2852, -2), (key2867, -2), (key2779, -2), (key2903, -2), (key2783, -2), (key2894, -2), (key2857, -2), (key2791, -2), (key2896, -2), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, 2), (key2867, 2), (key2625, 2), (key2982, 2), (key2629, 2), (key2973, 2), (key2857, 2), (key2637, 2), (key2975, 2)]

def rawRow10955 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2867, -2), (key2852, -2), (key2903, -2), (key2779, -2), (key2894, -2), (key2783, -2), (key2857, -2), (key2896, -2), (key2791, -2), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, 2), (key2852, 2), (key2982, 2), (key2625, 2), (key2973, 2), (key2629, 2), (key2857, 2), (key2975, 2), (key2637, 2)]

def rawRow10956 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2894, -2), (key2903, -2), (key2783, -2), (key2867, -2), (key2779, -2), (key2852, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, 2), (key2982, 2), (key2629, 2), (key2867, 2), (key2625, 2), (key2852, 2), (key2975, 2), (key2637, 2), (key2857, 2)]

def rawRow10957 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2903, -2), (key2894, -2), (key2867, -2), (key2783, -2), (key2852, -2), (key2779, -2), (key2896, -2), (key2857, -2), (key2791, -2), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, 2), (key2973, 2), (key2867, 2), (key2629, 2), (key2852, 2), (key2625, 2), (key2975, 2), (key2857, 2), (key2637, 2)]

def rawRow10958 : Integer.Sparse Key := [(key2852, -2), (key2857, -2), (key2867, -2), (key2779, -2), (key2791, -2), (key2802, -2), (key2896, -2), (key2826, -2), (key2903, -2), (key2783, -2), (key2806, -2), (key2894, -2), (key2852, 2), (key2857, 2), (key2867, 2), (key2625, 2), (key2637, 2), (key2699, 2), (key2975, 2), (key2723, 2), (key2982, 2), (key2629, 2), (key2703, 2), (key2973, 2)]

def rawRow10959 : Integer.Sparse Key := [(key2857, -2), (key2852, -2), (key2867, -2), (key2791, -2), (key2779, -2), (key2896, -2), (key2802, -2), (key2903, -2), (key2826, -2), (key2783, -2), (key2894, -2), (key2806, -2), (key2857, 2), (key2852, 2), (key2867, 2), (key2637, 2), (key2625, 2), (key2975, 2), (key2699, 2), (key2982, 2), (key2723, 2), (key2629, 2), (key2973, 2), (key2703, 2)]

def rawRow10960 : Integer.Sparse Key := [(key2852, -2), (key2867, -2), (key2857, -2), (key2802, -2), (key2826, -2), (key2779, -2), (key2903, -2), (key2791, -2), (key2896, -2), (key2806, -2), (key2783, -2), (key2894, -2), (key2852, 2), (key2867, 2), (key2857, 2), (key2699, 2), (key2723, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2703, 2), (key2629, 2), (key2973, 2)]

def rawRow10961 : Integer.Sparse Key := [(key2867, -2), (key2852, -2), (key2857, -2), (key2826, -2), (key2802, -2), (key2903, -2), (key2779, -2), (key2896, -2), (key2791, -2), (key2806, -2), (key2894, -2), (key2783, -2), (key2867, 2), (key2852, 2), (key2857, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2975, 2), (key2637, 2), (key2703, 2), (key2973, 2), (key2629, 2)]

def rawRow10962 : Integer.Sparse Key := [(key2857, -2), (key2867, -2), (key2852, -2), (key2896, -2), (key2903, -2), (key2791, -2), (key2826, -2), (key2779, -2), (key2802, -2), (key2894, -2), (key2783, -2), (key2806, -2), (key2857, 2), (key2867, 2), (key2852, 2), (key2975, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2625, 2), (key2699, 2), (key2973, 2), (key2629, 2), (key2703, 2)]

def rawRow10963 : Integer.Sparse Key := [(key2867, -2), (key2857, -2), (key2852, -2), (key2903, -2), (key2896, -2), (key2826, -2), (key2791, -2), (key2802, -2), (key2779, -2), (key2894, -2), (key2806, -2), (key2783, -2), (key2867, 2), (key2857, 2), (key2852, 2), (key2982, 2), (key2975, 2), (key2723, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2973, 2), (key2703, 2), (key2629, 2)]

def rawRow10964 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2783, -2), (key2791, -2), (key2806, -2), (key2857, -2), (key2826, -2), (key2867, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2973, 2), (key2975, 2), (key2982, 2), (key2629, 2), (key2637, 2), (key2703, 2), (key2857, 2), (key2723, 2), (key2867, 2), (key2625, 2), (key2699, 2), (key2852, 2)]

def rawRow10965 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2791, -2), (key2783, -2), (key2857, -2), (key2806, -2), (key2867, -2), (key2826, -2), (key2779, -2), (key2852, -2), (key2802, -2), (key2975, 2), (key2973, 2), (key2982, 2), (key2637, 2), (key2629, 2), (key2857, 2), (key2703, 2), (key2867, 2), (key2723, 2), (key2625, 2), (key2852, 2), (key2699, 2)]

def rawRow10966 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2806, -2), (key2826, -2), (key2783, -2), (key2867, -2), (key2791, -2), (key2857, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2973, 2), (key2982, 2), (key2975, 2), (key2703, 2), (key2723, 2), (key2629, 2), (key2867, 2), (key2637, 2), (key2857, 2), (key2699, 2), (key2625, 2), (key2852, 2)]

def rawRow10967 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2826, -2), (key2806, -2), (key2867, -2), (key2783, -2), (key2857, -2), (key2791, -2), (key2802, -2), (key2852, -2), (key2779, -2), (key2982, 2), (key2973, 2), (key2975, 2), (key2723, 2), (key2703, 2), (key2867, 2), (key2629, 2), (key2857, 2), (key2637, 2), (key2699, 2), (key2852, 2), (key2625, 2)]

def rawRow10968 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2857, -2), (key2867, -2), (key2791, -2), (key2826, -2), (key2783, -2), (key2806, -2), (key2852, -2), (key2779, -2), (key2802, -2), (key2975, 2), (key2982, 2), (key2973, 2), (key2857, 2), (key2867, 2), (key2637, 2), (key2723, 2), (key2629, 2), (key2703, 2), (key2852, 2), (key2625, 2), (key2699, 2)]

def rawRow10969 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2867, -2), (key2857, -2), (key2826, -2), (key2791, -2), (key2806, -2), (key2783, -2), (key2852, -2), (key2802, -2), (key2779, -2), (key2982, 2), (key2975, 2), (key2973, 2), (key2867, 2), (key2857, 2), (key2723, 2), (key2637, 2), (key2703, 2), (key2629, 2), (key2852, 2), (key2699, 2), (key2625, 2)]

def rawRow10970 : Integer.Sparse Key := [(key2937, -2), (key2937, -2), (key2942, -2), (key2949, -2), (key2949, -2), (key2973, -2), (key2973, -2), (key2975, -2), (key2975, -2), (key2959, -2), (key2982, -2), (key2982, -2), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, 2), (key2736, 2), (key2894, 2), (key2894, 2), (key2896, 2), (key2896, 2), (key2746, 2), (key2903, 2), (key2903, 2)]

def rawRow10971 : Integer.Sparse Key := [(key2937, -2), (key2942, -2), (key2937, -2), (key2973, -2), (key2975, -2), (key2949, -2), (key2975, -2), (key2949, -2), (key2973, -2), (key2982, -2), (key2959, -2), (key2982, -2), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, 2), (key2896, 2), (key2736, 2), (key2896, 2), (key2736, 2), (key2894, 2), (key2903, 2), (key2746, 2), (key2903, 2)]

def rawRow10972 : Integer.Sparse Key := [(key2942, -2), (key2937, -2), (key2937, -2), (key2975, -2), (key2973, -2), (key2975, -2), (key2949, -2), (key2973, -2), (key2949, -2), (key2982, -2), (key2982, -2), (key2959, -2), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, 2), (key2894, 2), (key2896, 2), (key2736, 2), (key2894, 2), (key2736, 2), (key2903, 2), (key2903, 2), (key2746, 2)]

def rawRow10973 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2937, -2), (key2937, -2), (key2973, -2), (key2973, -2), (key2982, -2), (key2982, -2), (key2942, -2), (key2975, -2), (key2975, -2), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, 2), (key2647, 2), (key2894, 2), (key2894, 2), (key2903, 2), (key2903, 2), (key2652, 2), (key2896, 2), (key2896, 2)]

def rawRow10974 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2973, -2), (key2982, -2), (key2937, -2), (key2982, -2), (key2937, -2), (key2973, -2), (key2975, -2), (key2942, -2), (key2975, -2), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, 2), (key2903, 2), (key2647, 2), (key2903, 2), (key2647, 2), (key2894, 2), (key2896, 2), (key2652, 2), (key2896, 2)]

def rawRow10975 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2982, -2), (key2973, -2), (key2982, -2), (key2937, -2), (key2973, -2), (key2937, -2), (key2975, -2), (key2975, -2), (key2942, -2), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, 2), (key2894, 2), (key2903, 2), (key2647, 2), (key2894, 2), (key2647, 2), (key2896, 2), (key2896, 2), (key2652, 2)]

def rawRow10976 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2937, -2), (key2942, -2), (key2949, -2), (key2975, -2), (key2959, -2), (key2982, -2), (key2937, -2), (key2949, -2), (key2973, -2), (key2894, 2), (key2896, 2), (key2903, 2), (key2647, 2), (key2652, 2), (key2736, 2), (key2896, 2), (key2746, 2), (key2903, 2), (key2647, 2), (key2736, 2), (key2894, 2)]

def rawRow10977 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2942, -2), (key2937, -2), (key2975, -2), (key2949, -2), (key2982, -2), (key2959, -2), (key2937, -2), (key2973, -2), (key2949, -2), (key2896, 2), (key2894, 2), (key2903, 2), (key2652, 2), (key2647, 2), (key2896, 2), (key2736, 2), (key2903, 2), (key2746, 2), (key2647, 2), (key2894, 2), (key2736, 2)]

def rawRow10978 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2949, -2), (key2959, -2), (key2937, -2), (key2982, -2), (key2942, -2), (key2975, -2), (key2949, -2), (key2937, -2), (key2973, -2), (key2894, 2), (key2903, 2), (key2896, 2), (key2736, 2), (key2746, 2), (key2647, 2), (key2903, 2), (key2652, 2), (key2896, 2), (key2736, 2), (key2647, 2), (key2894, 2)]

def rawRow10979 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2959, -2), (key2949, -2), (key2982, -2), (key2937, -2), (key2975, -2), (key2942, -2), (key2949, -2), (key2973, -2), (key2937, -2), (key2903, 2), (key2894, 2), (key2896, 2), (key2746, 2), (key2736, 2), (key2903, 2), (key2647, 2), (key2896, 2), (key2652, 2), (key2736, 2), (key2894, 2), (key2647, 2)]

def rawRow10980 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2975, -2), (key2982, -2), (key2942, -2), (key2959, -2), (key2937, -2), (key2949, -2), (key2973, -2), (key2937, -2), (key2949, -2), (key2896, 2), (key2903, 2), (key2894, 2), (key2896, 2), (key2903, 2), (key2652, 2), (key2746, 2), (key2647, 2), (key2736, 2), (key2894, 2), (key2647, 2), (key2736, 2)]

def rawRow10981 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2982, -2), (key2975, -2), (key2959, -2), (key2942, -2), (key2949, -2), (key2937, -2), (key2973, -2), (key2949, -2), (key2937, -2), (key2903, 2), (key2896, 2), (key2894, 2), (key2903, 2), (key2896, 2), (key2746, 2), (key2652, 2), (key2736, 2), (key2647, 2), (key2894, 2), (key2736, 2), (key2647, 2)]

def rawRow10982 : Integer.Sparse Key := [(key1312, -2), (key1317, -2), (key1325, -2), (key1420, -2), (key1425, -2), (key1618, -2), (key1814, -2), (key1623, -2), (key1816, -2), (key1443, -2), (key1632, -2), (key1824, -2), (key1292, 1), (key1297, 1), (key1312, 1), (key1338, 1), (key1325, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1), (key1420, 1), (key1456, 1), (key1569, 1), (key1789, 1), (key1658, 1), (key1816, 1), (key1443, 1), (key1465, 1), (key1592, 1), (key1797, 1), (key1666, 1), (key1824, 1)]

def rawRow10983 : Integer.Sparse Key := [(key1317, -2), (key1312, -2), (key1325, -2), (key1425, -2), (key1420, -2), (key1814, -2), (key1618, -2), (key1816, -2), (key1623, -2), (key1443, -2), (key1824, -2), (key1632, -2), (key1297, 1), (key1292, 1), (key1338, 1), (key1312, 1), (key1344, 1), (key1325, 1), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1), (key1456, 1), (key1420, 1), (key1789, 1), (key1569, 1), (key1816, 1), (key1658, 1), (key1465, 1), (key1443, 1), (key1797, 1), (key1592, 1), (key1824, 1), (key1666, 1)]

def rawRow10984 : Integer.Sparse Key := [(key1312, -2), (key1325, -2), (key1317, -2), (key1618, -2), (key1623, -2), (key1420, -2), (key1816, -2), (key1425, -2), (key1814, -2), (key1632, -2), (key1443, -2), (key1824, -2), (key1312, 1), (key1325, 1), (key1292, 1), (key1344, 1), (key1297, 1), (key1338, 1), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1), (key1569, 1), (key1658, 1), (key1420, 1), (key1816, 1), (key1456, 1), (key1789, 1), (key1592, 1), (key1666, 1), (key1443, 1), (key1824, 1), (key1465, 1), (key1797, 1)]

def rawRow10985 : Integer.Sparse Key := [(key1325, -2), (key1312, -2), (key1317, -2), (key1623, -2), (key1618, -2), (key1816, -2), (key1420, -2), (key1814, -2), (key1425, -2), (key1632, -2), (key1824, -2), (key1443, -2), (key1325, 1), (key1312, 1), (key1344, 1), (key1292, 1), (key1338, 1), (key1297, 1), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1), (key1658, 1), (key1569, 1), (key1816, 1), (key1420, 1), (key1789, 1), (key1456, 1), (key1666, 1), (key1592, 1), (key1824, 1), (key1443, 1), (key1797, 1), (key1465, 1)]

def rawRow10986 : Integer.Sparse Key := [(key1317, -2), (key1325, -2), (key1312, -2), (key1814, -2), (key1816, -2), (key1425, -2), (key1623, -2), (key1420, -2), (key1618, -2), (key1824, -2), (key1443, -2), (key1632, -2), (key1338, 1), (key1344, 1), (key1297, 1), (key1325, 1), (key1292, 1), (key1312, 1), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1), (key1789, 1), (key1816, 1), (key1456, 1), (key1658, 1), (key1420, 1), (key1569, 1), (key1797, 1), (key1824, 1), (key1465, 1), (key1666, 1), (key1443, 1), (key1592, 1)]

def rawRow10987 : Integer.Sparse Key := [(key1325, -2), (key1317, -2), (key1312, -2), (key1816, -2), (key1814, -2), (key1623, -2), (key1425, -2), (key1618, -2), (key1420, -2), (key1824, -2), (key1632, -2), (key1443, -2), (key1344, 1), (key1338, 1), (key1325, 1), (key1297, 1), (key1312, 1), (key1292, 1), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1), (key1816, 1), (key1789, 1), (key1658, 1), (key1456, 1), (key1569, 1), (key1420, 1), (key1824, 1), (key1797, 1), (key1666, 1), (key1465, 1), (key1592, 1), (key1443, 1)]

def rawRow10988 : Integer.Sparse Key := [(key1420, -2), (key1425, -2), (key1443, -2), (key1312, -2), (key1317, -2), (key1618, -2), (key1814, -2), (key1632, -2), (key1824, -2), (key1325, -2), (key1623, -2), (key1816, -2), (key1387, 1), (key1392, 1), (key1420, 1), (key1456, 1), (key1443, 1), (key1465, 1), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1), (key1312, 1), (key1338, 1), (key1542, 1), (key1773, 1), (key1666, 1), (key1824, 1), (key1325, 1), (key1344, 1), (key1555, 1), (key1779, 1), (key1658, 1), (key1816, 1)]

def rawRow10989 : Integer.Sparse Key := [(key1425, -2), (key1420, -2), (key1443, -2), (key1317, -2), (key1312, -2), (key1814, -2), (key1618, -2), (key1824, -2), (key1632, -2), (key1325, -2), (key1816, -2), (key1623, -2), (key1392, 1), (key1387, 1), (key1456, 1), (key1420, 1), (key1465, 1), (key1443, 1), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1), (key1338, 1), (key1312, 1), (key1773, 1), (key1542, 1), (key1824, 1), (key1666, 1), (key1344, 1), (key1325, 1), (key1779, 1), (key1555, 1), (key1816, 1), (key1658, 1)]

def rawRow10990 : Integer.Sparse Key := [(key1420, -2), (key1443, -2), (key1425, -2), (key1618, -2), (key1632, -2), (key1312, -2), (key1824, -2), (key1317, -2), (key1814, -2), (key1623, -2), (key1325, -2), (key1816, -2), (key1420, 1), (key1443, 1), (key1387, 1), (key1465, 1), (key1392, 1), (key1456, 1), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1), (key1542, 1), (key1666, 1), (key1312, 1), (key1824, 1), (key1338, 1), (key1773, 1), (key1555, 1), (key1658, 1), (key1325, 1), (key1816, 1), (key1344, 1), (key1779, 1)]

def rawRow10991 : Integer.Sparse Key := [(key1443, -2), (key1420, -2), (key1425, -2), (key1632, -2), (key1618, -2), (key1824, -2), (key1312, -2), (key1814, -2), (key1317, -2), (key1623, -2), (key1816, -2), (key1325, -2), (key1443, 1), (key1420, 1), (key1465, 1), (key1387, 1), (key1456, 1), (key1392, 1), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1), (key1666, 1), (key1542, 1), (key1824, 1), (key1312, 1), (key1773, 1), (key1338, 1), (key1658, 1), (key1555, 1), (key1816, 1), (key1325, 1), (key1779, 1), (key1344, 1)]

def rawRow10992 : Integer.Sparse Key := [(key1425, -2), (key1443, -2), (key1420, -2), (key1814, -2), (key1824, -2), (key1317, -2), (key1632, -2), (key1312, -2), (key1618, -2), (key1816, -2), (key1325, -2), (key1623, -2), (key1456, 1), (key1465, 1), (key1392, 1), (key1443, 1), (key1387, 1), (key1420, 1), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1), (key1773, 1), (key1824, 1), (key1338, 1), (key1666, 1), (key1312, 1), (key1542, 1), (key1779, 1), (key1816, 1), (key1344, 1), (key1658, 1), (key1325, 1), (key1555, 1)]

def rawRow10993 : Integer.Sparse Key := [(key1443, -2), (key1425, -2), (key1420, -2), (key1824, -2), (key1814, -2), (key1632, -2), (key1317, -2), (key1618, -2), (key1312, -2), (key1816, -2), (key1623, -2), (key1325, -2), (key1465, 1), (key1456, 1), (key1443, 1), (key1392, 1), (key1420, 1), (key1387, 1), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1), (key1824, 1), (key1773, 1), (key1666, 1), (key1338, 1), (key1542, 1), (key1312, 1), (key1816, 1), (key1779, 1), (key1658, 1), (key1344, 1), (key1555, 1), (key1325, 1)]

def rawRow10994 : Integer.Sparse Key := [(key1618, -2), (key1623, -2), (key1632, -2), (key1312, -2), (key1325, -2), (key1420, -2), (key1816, -2), (key1443, -2), (key1824, -2), (key1317, -2), (key1425, -2), (key1814, -2), (key1542, 1), (key1555, 1), (key1569, 1), (key1658, 1), (key1592, 1), (key1666, 1), (key1312, 1), (key1325, 1), (key1420, 1), (key1816, 1), (key1443, 1), (key1824, 1), (key1292, 1), (key1344, 1), (key1387, 1), (key1779, 1), (key1465, 1), (key1797, 1), (key1297, 1), (key1338, 1), (key1392, 1), (key1773, 1), (key1456, 1), (key1789, 1)]

def rawRow10995 : Integer.Sparse Key := [(key1623, -2), (key1618, -2), (key1632, -2), (key1325, -2), (key1312, -2), (key1816, -2), (key1420, -2), (key1824, -2), (key1443, -2), (key1317, -2), (key1814, -2), (key1425, -2), (key1555, 1), (key1542, 1), (key1658, 1), (key1569, 1), (key1666, 1), (key1592, 1), (key1325, 1), (key1312, 1), (key1816, 1), (key1420, 1), (key1824, 1), (key1443, 1), (key1344, 1), (key1292, 1), (key1779, 1), (key1387, 1), (key1797, 1), (key1465, 1), (key1338, 1), (key1297, 1), (key1773, 1), (key1392, 1), (key1789, 1), (key1456, 1)]

def rawRow10996 : Integer.Sparse Key := [(key1618, -2), (key1632, -2), (key1623, -2), (key1420, -2), (key1443, -2), (key1312, -2), (key1824, -2), (key1325, -2), (key1816, -2), (key1425, -2), (key1317, -2), (key1814, -2), (key1569, 1), (key1592, 1), (key1542, 1), (key1666, 1), (key1555, 1), (key1658, 1), (key1420, 1), (key1443, 1), (key1312, 1), (key1824, 1), (key1325, 1), (key1816, 1), (key1387, 1), (key1465, 1), (key1292, 1), (key1797, 1), (key1344, 1), (key1779, 1), (key1392, 1), (key1456, 1), (key1297, 1), (key1789, 1), (key1338, 1), (key1773, 1)]

def rawRow10997 : Integer.Sparse Key := [(key1632, -2), (key1618, -2), (key1623, -2), (key1443, -2), (key1420, -2), (key1824, -2), (key1312, -2), (key1816, -2), (key1325, -2), (key1425, -2), (key1814, -2), (key1317, -2), (key1592, 1), (key1569, 1), (key1666, 1), (key1542, 1), (key1658, 1), (key1555, 1), (key1443, 1), (key1420, 1), (key1824, 1), (key1312, 1), (key1816, 1), (key1325, 1), (key1465, 1), (key1387, 1), (key1797, 1), (key1292, 1), (key1779, 1), (key1344, 1), (key1456, 1), (key1392, 1), (key1789, 1), (key1297, 1), (key1773, 1), (key1338, 1)]

def rawRow10998 : Integer.Sparse Key := [(key1623, -2), (key1632, -2), (key1618, -2), (key1816, -2), (key1824, -2), (key1325, -2), (key1443, -2), (key1312, -2), (key1420, -2), (key1814, -2), (key1317, -2), (key1425, -2), (key1658, 1), (key1666, 1), (key1555, 1), (key1592, 1), (key1542, 1), (key1569, 1), (key1816, 1), (key1824, 1), (key1325, 1), (key1443, 1), (key1312, 1), (key1420, 1), (key1779, 1), (key1797, 1), (key1344, 1), (key1465, 1), (key1292, 1), (key1387, 1), (key1773, 1), (key1789, 1), (key1338, 1), (key1456, 1), (key1297, 1), (key1392, 1)]

def rawRow10999 : Integer.Sparse Key := [(key1632, -2), (key1623, -2), (key1618, -2), (key1824, -2), (key1816, -2), (key1443, -2), (key1325, -2), (key1420, -2), (key1312, -2), (key1814, -2), (key1425, -2), (key1317, -2), (key1666, 1), (key1658, 1), (key1592, 1), (key1555, 1), (key1569, 1), (key1542, 1), (key1824, 1), (key1816, 1), (key1443, 1), (key1325, 1), (key1420, 1), (key1312, 1), (key1797, 1), (key1779, 1), (key1465, 1), (key1344, 1), (key1387, 1), (key1292, 1), (key1789, 1), (key1773, 1), (key1456, 1), (key1338, 1), (key1392, 1), (key1297, 1)]

def rawRow11000 : Integer.Sparse Key := [(key1814, -2), (key1816, -2), (key1824, -2), (key1317, -2), (key1325, -2), (key1425, -2), (key1623, -2), (key1443, -2), (key1632, -2), (key1312, -2), (key1420, -2), (key1618, -2), (key1773, 1), (key1779, 1), (key1789, 1), (key1816, 1), (key1797, 1), (key1824, 1), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1), (key1297, 1), (key1325, 1), (key1392, 1), (key1555, 1), (key1443, 1), (key1592, 1), (key1292, 1), (key1312, 1), (key1387, 1), (key1542, 1), (key1420, 1), (key1569, 1)]

def rawRow11001 : Integer.Sparse Key := [(key1816, -2), (key1814, -2), (key1824, -2), (key1325, -2), (key1317, -2), (key1623, -2), (key1425, -2), (key1632, -2), (key1443, -2), (key1312, -2), (key1618, -2), (key1420, -2), (key1779, 1), (key1773, 1), (key1816, 1), (key1789, 1), (key1824, 1), (key1797, 1), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1), (key1325, 1), (key1297, 1), (key1555, 1), (key1392, 1), (key1592, 1), (key1443, 1), (key1312, 1), (key1292, 1), (key1542, 1), (key1387, 1), (key1569, 1), (key1420, 1)]

def rawRow11002 : Integer.Sparse Key := [(key1814, -2), (key1824, -2), (key1816, -2), (key1425, -2), (key1443, -2), (key1317, -2), (key1632, -2), (key1325, -2), (key1623, -2), (key1420, -2), (key1312, -2), (key1618, -2), (key1789, 1), (key1797, 1), (key1773, 1), (key1824, 1), (key1779, 1), (key1816, 1), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1), (key1392, 1), (key1443, 1), (key1297, 1), (key1592, 1), (key1325, 1), (key1555, 1), (key1387, 1), (key1420, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1542, 1)]

def rawRow11003 : Integer.Sparse Key := [(key1824, -2), (key1814, -2), (key1816, -2), (key1443, -2), (key1425, -2), (key1632, -2), (key1317, -2), (key1623, -2), (key1325, -2), (key1420, -2), (key1618, -2), (key1312, -2), (key1797, 1), (key1789, 1), (key1824, 1), (key1773, 1), (key1816, 1), (key1779, 1), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1), (key1443, 1), (key1392, 1), (key1592, 1), (key1297, 1), (key1555, 1), (key1325, 1), (key1420, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1542, 1), (key1312, 1)]

def rawRow11004 : Integer.Sparse Key := [(key1816, -2), (key1824, -2), (key1814, -2), (key1623, -2), (key1632, -2), (key1325, -2), (key1443, -2), (key1317, -2), (key1425, -2), (key1618, -2), (key1312, -2), (key1420, -2), (key1816, 1), (key1824, 1), (key1779, 1), (key1797, 1), (key1773, 1), (key1789, 1), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1), (key1555, 1), (key1592, 1), (key1325, 1), (key1443, 1), (key1297, 1), (key1392, 1), (key1542, 1), (key1569, 1), (key1312, 1), (key1420, 1), (key1292, 1), (key1387, 1)]

def rawRow11005 : Integer.Sparse Key := [(key1824, -2), (key1816, -2), (key1814, -2), (key1632, -2), (key1623, -2), (key1443, -2), (key1325, -2), (key1425, -2), (key1317, -2), (key1618, -2), (key1420, -2), (key1312, -2), (key1824, 1), (key1816, 1), (key1797, 1), (key1779, 1), (key1789, 1), (key1773, 1), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1), (key1592, 1), (key1555, 1), (key1443, 1), (key1325, 1), (key1392, 1), (key1297, 1), (key1569, 1), (key1542, 1), (key1420, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

def rawRow11006 : Integer.Sparse Key := [(key1338, -2), (key1338, -2), (key1344, -2), (key1456, -2), (key1456, -2), (key1656, -2), (key1656, -2), (key1658, -2), (key1658, -2), (key1465, -2), (key1666, -2), (key1666, -2), (key1297, 1), (key1297, 1), (key1317, 1), (key1317, 1), (key1325, 1), (key1325, 1), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1), (key1425, 1), (key1425, 1), (key1574, 1), (key1574, 1), (key1623, 1), (key1623, 1), (key1443, 1), (key1443, 1), (key1592, 1), (key1592, 1), (key1632, 1), (key1632, 1)]

def rawRow11007 : Integer.Sparse Key := [(key1338, -2), (key1344, -2), (key1338, -2), (key1656, -2), (key1658, -2), (key1456, -2), (key1658, -2), (key1456, -2), (key1656, -2), (key1666, -2), (key1465, -2), (key1666, -2), (key1317, 1), (key1325, 1), (key1297, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1574, 1), (key1623, 1), (key1425, 1), (key1623, 1), (key1425, 1), (key1574, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1632, 1), (key1443, 1), (key1592, 1)]

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

def rawRow11008 : Integer.Sparse Key := [(key1344, -2), (key1338, -2), (key1338, -2), (key1658, -2), (key1656, -2), (key1658, -2), (key1456, -2), (key1656, -2), (key1456, -2), (key1666, -2), (key1666, -2), (key1465, -2), (key1325, 1), (key1317, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1297, 1), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1), (key1623, 1), (key1574, 1), (key1623, 1), (key1425, 1), (key1574, 1), (key1425, 1), (key1632, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1592, 1), (key1443, 1)]

def rawRow11009 : Integer.Sparse Key := [(key1456, -2), (key1456, -2), (key1465, -2), (key1338, -2), (key1338, -2), (key1656, -2), (key1656, -2), (key1666, -2), (key1666, -2), (key1344, -2), (key1658, -2), (key1658, -2), (key1392, 1), (key1392, 1), (key1425, 1), (key1425, 1), (key1443, 1), (key1443, 1), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1), (key1317, 1), (key1317, 1), (key1547, 1), (key1547, 1), (key1632, 1), (key1632, 1), (key1325, 1), (key1325, 1), (key1555, 1), (key1555, 1), (key1623, 1), (key1623, 1)]

def rawRow11010 : Integer.Sparse Key := [(key1456, -2), (key1465, -2), (key1456, -2), (key1656, -2), (key1666, -2), (key1338, -2), (key1666, -2), (key1338, -2), (key1656, -2), (key1658, -2), (key1344, -2), (key1658, -2), (key1425, 1), (key1443, 1), (key1392, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1623, 1), (key1325, 1), (key1555, 1)]

def rawRow11011 : Integer.Sparse Key := [(key1465, -2), (key1456, -2), (key1456, -2), (key1666, -2), (key1656, -2), (key1666, -2), (key1338, -2), (key1656, -2), (key1338, -2), (key1658, -2), (key1658, -2), (key1344, -2), (key1443, 1), (key1425, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1392, 1), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1), (key1632, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1317, 1), (key1623, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1555, 1), (key1325, 1)]

def rawRow11012 : Integer.Sparse Key := [(key1656, -2), (key1658, -2), (key1666, -2), (key1338, -2), (key1344, -2), (key1456, -2), (key1658, -2), (key1465, -2), (key1666, -2), (key1338, -2), (key1456, -2), (key1656, -2), (key1547, 1), (key1555, 1), (key1574, 1), (key1623, 1), (key1592, 1), (key1632, 1), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1), (key1297, 1), (key1325, 1), (key1392, 1), (key1555, 1), (key1443, 1), (key1592, 1), (key1297, 1), (key1317, 1), (key1392, 1), (key1547, 1), (key1425, 1), (key1574, 1)]

def rawRow11013 : Integer.Sparse Key := [(key1658, -2), (key1656, -2), (key1666, -2), (key1344, -2), (key1338, -2), (key1658, -2), (key1456, -2), (key1666, -2), (key1465, -2), (key1338, -2), (key1656, -2), (key1456, -2), (key1555, 1), (key1547, 1), (key1623, 1), (key1574, 1), (key1632, 1), (key1592, 1), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1), (key1325, 1), (key1297, 1), (key1555, 1), (key1392, 1), (key1592, 1), (key1443, 1), (key1317, 1), (key1297, 1), (key1547, 1), (key1392, 1), (key1574, 1), (key1425, 1)]

def rawRow11014 : Integer.Sparse Key := [(key1656, -2), (key1666, -2), (key1658, -2), (key1456, -2), (key1465, -2), (key1338, -2), (key1666, -2), (key1344, -2), (key1658, -2), (key1456, -2), (key1338, -2), (key1656, -2), (key1574, 1), (key1592, 1), (key1547, 1), (key1632, 1), (key1555, 1), (key1623, 1), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1), (key1392, 1), (key1443, 1), (key1297, 1), (key1592, 1), (key1325, 1), (key1555, 1), (key1392, 1), (key1425, 1), (key1297, 1), (key1574, 1), (key1317, 1), (key1547, 1)]

def rawRow11015 : Integer.Sparse Key := [(key1666, -2), (key1656, -2), (key1658, -2), (key1465, -2), (key1456, -2), (key1666, -2), (key1338, -2), (key1658, -2), (key1344, -2), (key1456, -2), (key1656, -2), (key1338, -2), (key1592, 1), (key1574, 1), (key1632, 1), (key1547, 1), (key1623, 1), (key1555, 1), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1), (key1443, 1), (key1392, 1), (key1592, 1), (key1297, 1), (key1555, 1), (key1325, 1), (key1425, 1), (key1392, 1), (key1574, 1), (key1297, 1), (key1547, 1), (key1317, 1)]

def rawRow11016 : Integer.Sparse Key := [(key1658, -2), (key1666, -2), (key1656, -2), (key1658, -2), (key1666, -2), (key1344, -2), (key1465, -2), (key1338, -2), (key1456, -2), (key1656, -2), (key1338, -2), (key1456, -2), (key1623, 1), (key1632, 1), (key1555, 1), (key1592, 1), (key1547, 1), (key1574, 1), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1), (key1555, 1), (key1592, 1), (key1325, 1), (key1443, 1), (key1297, 1), (key1392, 1), (key1547, 1), (key1574, 1), (key1317, 1), (key1425, 1), (key1297, 1), (key1392, 1)]

def rawRow11017 : Integer.Sparse Key := [(key1666, -2), (key1658, -2), (key1656, -2), (key1666, -2), (key1658, -2), (key1465, -2), (key1344, -2), (key1456, -2), (key1338, -2), (key1656, -2), (key1456, -2), (key1338, -2), (key1632, 1), (key1623, 1), (key1592, 1), (key1555, 1), (key1574, 1), (key1547, 1), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1), (key1592, 1), (key1555, 1), (key1443, 1), (key1325, 1), (key1392, 1), (key1297, 1), (key1574, 1), (key1547, 1), (key1425, 1), (key1317, 1), (key1392, 1), (key1297, 1)]

def rawRow11018 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2699, 1), (key2736, 1), (key2802, 1), (key2949, 1), (key2896, 1), (key2975, 1), (key2723, 1), (key2746, 1), (key2826, 1), (key2959, 1), (key2903, 1), (key2982, 1), (key2613, -2), (key2629, -2), (key2647, -2), (key2668, -2), (key2783, -2), (key2937, -2), (key2703, -2), (key2736, -2), (key2806, -2), (key2949, -2), (key2894, -2), (key2973, -2)]

def rawRow11019 : Integer.Sparse Key := [(key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2736, 1), (key2699, 1), (key2949, 1), (key2802, 1), (key2975, 1), (key2896, 1), (key2746, 1), (key2723, 1), (key2959, 1), (key2826, 1), (key2982, 1), (key2903, 1), (key2613, -2), (key2647, -2), (key2629, -2), (key2668, -2), (key2937, -2), (key2783, -2), (key2736, -2), (key2703, -2), (key2949, -2), (key2806, -2), (key2973, -2), (key2894, -2)]

def rawRow11020 : Integer.Sparse Key := [(key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2802, 1), (key2896, 1), (key2699, 1), (key2975, 1), (key2736, 1), (key2949, 1), (key2826, 1), (key2903, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2959, 1), (key2629, -2), (key2613, -2), (key2647, -2), (key2783, -2), (key2668, -2), (key2937, -2), (key2806, -2), (key2894, -2), (key2703, -2), (key2973, -2), (key2736, -2), (key2949, -2)]

def rawRow11021 : Integer.Sparse Key := [(key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2896, 1), (key2802, 1), (key2975, 1), (key2699, 1), (key2949, 1), (key2736, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2959, 1), (key2746, 1), (key2629, -2), (key2647, -2), (key2613, -2), (key2783, -2), (key2937, -2), (key2668, -2), (key2894, -2), (key2806, -2), (key2973, -2), (key2703, -2), (key2949, -2), (key2736, -2)]

def rawRow11022 : Integer.Sparse Key := [(key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2949, 1), (key2975, 1), (key2736, 1), (key2896, 1), (key2699, 1), (key2802, 1), (key2959, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2723, 1), (key2826, 1), (key2647, -2), (key2613, -2), (key2629, -2), (key2937, -2), (key2668, -2), (key2783, -2), (key2949, -2), (key2973, -2), (key2736, -2), (key2894, -2), (key2703, -2), (key2806, -2)]

def rawRow11023 : Integer.Sparse Key := [(key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2975, 1), (key2949, 1), (key2896, 1), (key2736, 1), (key2802, 1), (key2699, 1), (key2982, 1), (key2959, 1), (key2903, 1), (key2746, 1), (key2826, 1), (key2723, 1), (key2647, -2), (key2629, -2), (key2613, -2), (key2937, -2), (key2783, -2), (key2668, -2), (key2973, -2), (key2949, -2), (key2894, -2), (key2736, -2), (key2806, -2), (key2703, -2)]

def rawRow11024 : Integer.Sparse Key := [(key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1), (key2668, -2), (key2703, -2), (key2736, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2629, -2), (key2647, -2), (key2783, -2), (key2937, -2), (key2894, -2), (key2973, -2)]

def rawRow11025 : Integer.Sparse Key := [(key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1), (key2668, -2), (key2736, -2), (key2703, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2647, -2), (key2629, -2), (key2937, -2), (key2783, -2), (key2973, -2), (key2894, -2)]

def rawRow11026 : Integer.Sparse Key := [(key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1), (key2703, -2), (key2668, -2), (key2736, -2), (key2806, -2), (key2613, -2), (key2949, -2), (key2783, -2), (key2894, -2), (key2629, -2), (key2973, -2), (key2647, -2), (key2937, -2)]

def rawRow11027 : Integer.Sparse Key := [(key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1), (key2703, -2), (key2736, -2), (key2668, -2), (key2806, -2), (key2949, -2), (key2613, -2), (key2894, -2), (key2783, -2), (key2973, -2), (key2629, -2), (key2937, -2), (key2647, -2)]

def rawRow11028 : Integer.Sparse Key := [(key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1), (key2736, -2), (key2668, -2), (key2703, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2937, -2), (key2973, -2), (key2647, -2), (key2894, -2), (key2629, -2), (key2783, -2)]

def rawRow11029 : Integer.Sparse Key := [(key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1), (key2736, -2), (key2703, -2), (key2668, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2973, -2), (key2937, -2), (key2894, -2), (key2647, -2), (key2783, -2), (key2629, -2)]

def rawRow11030 : Integer.Sparse Key := [(key2779, 1), (key2791, 1), (key2802, 1), (key2896, 1), (key2826, 1), (key2903, 1), (key2625, 1), (key2637, 1), (key2699, 1), (key2975, 1), (key2723, 1), (key2982, 1), (key2609, 1), (key2652, 1), (key2664, 1), (key2942, 1), (key2746, 1), (key2959, 1), (key2613, 1), (key2647, 1), (key2668, 1), (key2937, 1), (key2736, 1), (key2949, 1), (key2783, -2), (key2806, -2), (key2894, -2), (key2629, -2), (key2703, -2), (key2973, -2), (key2613, -2), (key2647, -2), (key2668, -2), (key2937, -2), (key2736, -2), (key2949, -2)]

def rawRow11031 : Integer.Sparse Key := [(key2791, 1), (key2779, 1), (key2896, 1), (key2802, 1), (key2903, 1), (key2826, 1), (key2637, 1), (key2625, 1), (key2975, 1), (key2699, 1), (key2982, 1), (key2723, 1), (key2652, 1), (key2609, 1), (key2942, 1), (key2664, 1), (key2959, 1), (key2746, 1), (key2647, 1), (key2613, 1), (key2937, 1), (key2668, 1), (key2949, 1), (key2736, 1), (key2783, -2), (key2894, -2), (key2806, -2), (key2629, -2), (key2973, -2), (key2703, -2), (key2647, -2), (key2613, -2), (key2937, -2), (key2668, -2), (key2949, -2), (key2736, -2)]

def rawRow11032 : Integer.Sparse Key := [(key2802, 1), (key2826, 1), (key2779, 1), (key2903, 1), (key2791, 1), (key2896, 1), (key2699, 1), (key2723, 1), (key2625, 1), (key2982, 1), (key2637, 1), (key2975, 1), (key2664, 1), (key2746, 1), (key2609, 1), (key2959, 1), (key2652, 1), (key2942, 1), (key2668, 1), (key2736, 1), (key2613, 1), (key2949, 1), (key2647, 1), (key2937, 1), (key2806, -2), (key2783, -2), (key2894, -2), (key2703, -2), (key2629, -2), (key2973, -2), (key2668, -2), (key2736, -2), (key2613, -2), (key2949, -2), (key2647, -2), (key2937, -2)]

def rawRow11033 : Integer.Sparse Key := [(key2826, 1), (key2802, 1), (key2903, 1), (key2779, 1), (key2896, 1), (key2791, 1), (key2723, 1), (key2699, 1), (key2982, 1), (key2625, 1), (key2975, 1), (key2637, 1), (key2746, 1), (key2664, 1), (key2959, 1), (key2609, 1), (key2942, 1), (key2652, 1), (key2736, 1), (key2668, 1), (key2949, 1), (key2613, 1), (key2937, 1), (key2647, 1), (key2806, -2), (key2894, -2), (key2783, -2), (key2703, -2), (key2973, -2), (key2629, -2), (key2736, -2), (key2668, -2), (key2949, -2), (key2613, -2), (key2937, -2), (key2647, -2)]

def rawRow11034 : Integer.Sparse Key := [(key2896, 1), (key2903, 1), (key2791, 1), (key2826, 1), (key2779, 1), (key2802, 1), (key2975, 1), (key2982, 1), (key2637, 1), (key2723, 1), (key2625, 1), (key2699, 1), (key2942, 1), (key2959, 1), (key2652, 1), (key2746, 1), (key2609, 1), (key2664, 1), (key2937, 1), (key2949, 1), (key2647, 1), (key2736, 1), (key2613, 1), (key2668, 1), (key2894, -2), (key2783, -2), (key2806, -2), (key2973, -2), (key2629, -2), (key2703, -2), (key2937, -2), (key2949, -2), (key2647, -2), (key2736, -2), (key2613, -2), (key2668, -2)]

def rawRow11035 : Integer.Sparse Key := [(key2903, 1), (key2896, 1), (key2826, 1), (key2791, 1), (key2802, 1), (key2779, 1), (key2982, 1), (key2975, 1), (key2723, 1), (key2637, 1), (key2699, 1), (key2625, 1), (key2959, 1), (key2942, 1), (key2746, 1), (key2652, 1), (key2664, 1), (key2609, 1), (key2949, 1), (key2937, 1), (key2736, 1), (key2647, 1), (key2668, 1), (key2613, 1), (key2894, -2), (key2806, -2), (key2783, -2), (key2973, -2), (key2703, -2), (key2629, -2), (key2949, -2), (key2937, -2), (key2736, -2), (key2647, -2), (key2668, -2), (key2613, -2)]

def rawRow11036 : Integer.Sparse Key := [(key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1), (key2937, -2), (key2949, -2), (key2973, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2613, -2), (key2629, -2), (key2668, -2), (key2783, -2), (key2703, -2), (key2806, -2)]

def rawRow11037 : Integer.Sparse Key := [(key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1), (key2937, -2), (key2973, -2), (key2949, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2629, -2), (key2613, -2), (key2783, -2), (key2668, -2), (key2806, -2), (key2703, -2)]

def rawRow11038 : Integer.Sparse Key := [(key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1), (key2949, -2), (key2937, -2), (key2973, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2668, -2), (key2703, -2), (key2613, -2), (key2806, -2), (key2629, -2), (key2783, -2)]

def rawRow11039 : Integer.Sparse Key := [(key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1), (key2949, -2), (key2973, -2), (key2937, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2703, -2), (key2668, -2), (key2806, -2), (key2613, -2), (key2783, -2), (key2629, -2)]

def rawRow11040 : Integer.Sparse Key := [(key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1), (key2973, -2), (key2937, -2), (key2949, -2), (key2894, -2), (key2647, -2), (key2736, -2), (key2783, -2), (key2806, -2), (key2629, -2), (key2703, -2), (key2613, -2), (key2668, -2)]

def rawRow11041 : Integer.Sparse Key := [(key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1), (key2973, -2), (key2949, -2), (key2937, -2), (key2894, -2), (key2736, -2), (key2647, -2), (key2806, -2), (key2783, -2), (key2703, -2), (key2629, -2), (key2668, -2), (key2613, -2)]

def rawRow11042 : Integer.Sparse Key := [(key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2703, 1), (key2703, 1), (key2806, 1), (key2806, 1), (key2857, 1), (key2857, 1), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1), (key2609, -2), (key2625, -2), (key2625, -2), (key2664, -2), (key2779, -2), (key2779, -2), (key2699, -2), (key2699, -2), (key2802, -2), (key2802, -2), (key2852, -2), (key2852, -2)]

def rawRow11043 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2625, -2), (key2609, -2), (key2625, -2), (key2779, -2), (key2664, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2699, -2), (key2852, -2), (key2699, -2), (key2802, -2)]

def rawRow11044 : Integer.Sparse Key := [(key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2857, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2703, 1), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1), (key2625, -2), (key2625, -2), (key2609, -2), (key2779, -2), (key2779, -2), (key2664, -2), (key2852, -2), (key2802, -2), (key2852, -2), (key2699, -2), (key2802, -2), (key2699, -2)]

def rawRow11045 : Integer.Sparse Key := [(key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1), (key2664, -2), (key2699, -2), (key2699, -2), (key2609, -2), (key2802, -2), (key2802, -2), (key2625, -2), (key2625, -2), (key2779, -2), (key2779, -2), (key2852, -2), (key2852, -2)]

def rawRow11046 : Integer.Sparse Key := [(key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2699, -2), (key2664, -2), (key2699, -2), (key2802, -2), (key2609, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2625, -2), (key2852, -2), (key2625, -2), (key2779, -2)]

def rawRow11047 : Integer.Sparse Key := [(key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1), (key2699, -2), (key2699, -2), (key2664, -2), (key2802, -2), (key2802, -2), (key2609, -2), (key2852, -2), (key2779, -2), (key2852, -2), (key2625, -2), (key2779, -2), (key2625, -2)]

def rawRow11048 : Integer.Sparse Key := [(key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1), (key2779, -2), (key2802, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2852, -2), (key2609, -2), (key2625, -2), (key2664, -2), (key2779, -2), (key2699, -2), (key2802, -2)]

def rawRow11049 : Integer.Sparse Key := [(key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1), (key2779, -2), (key2852, -2), (key2802, -2), (key2625, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2609, -2), (key2779, -2), (key2664, -2), (key2802, -2), (key2699, -2)]

def rawRow11050 : Integer.Sparse Key := [(key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1), (key2802, -2), (key2779, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2852, -2), (key2664, -2), (key2699, -2), (key2609, -2), (key2802, -2), (key2625, -2), (key2779, -2)]

def rawRow11051 : Integer.Sparse Key := [(key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1), (key2802, -2), (key2852, -2), (key2779, -2), (key2699, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2664, -2), (key2802, -2), (key2609, -2), (key2779, -2), (key2625, -2)]

def rawRow11052 : Integer.Sparse Key := [(key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1), (key2852, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2779, -2), (key2802, -2), (key2625, -2), (key2699, -2), (key2609, -2), (key2664, -2)]

def rawRow11053 : Integer.Sparse Key := [(key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1), (key2852, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2802, -2), (key2779, -2), (key2699, -2), (key2625, -2), (key2664, -2), (key2609, -2)]

def rawRow11054 : Integer.Sparse Key := [(key1308, -6), (key1416, -6), (key1614, -6), (key1810, -6), (key1288, 2), (key1308, 2), (key1334, 2), (key1383, 2), (key1538, 2), (key1769, 2), (key1416, 2), (key1452, 2), (key1565, 2), (key1785, 2), (key1652, 2), (key1810, 2)]

def rawRow11055 : Integer.Sparse Key := [(key1308, -6), (key1416, -6), (key1810, -6), (key1614, -6), (key1288, 2), (key1334, 2), (key1308, 2), (key1383, 2), (key1769, 2), (key1538, 2), (key1452, 2), (key1416, 2), (key1785, 2), (key1565, 2), (key1810, 2), (key1652, 2)]

def rawRow11056 : Integer.Sparse Key := [(key1308, -6), (key1614, -6), (key1416, -6), (key1810, -6), (key1308, 2), (key1288, 2), (key1334, 2), (key1538, 2), (key1383, 2), (key1769, 2), (key1565, 2), (key1652, 2), (key1416, 2), (key1810, 2), (key1452, 2), (key1785, 2)]

def rawRow11057 : Integer.Sparse Key := [(key1308, -6), (key1614, -6), (key1810, -6), (key1416, -6), (key1308, 2), (key1334, 2), (key1288, 2), (key1538, 2), (key1769, 2), (key1383, 2), (key1652, 2), (key1565, 2), (key1810, 2), (key1416, 2), (key1785, 2), (key1452, 2)]

def rawRow11058 : Integer.Sparse Key := [(key1308, -6), (key1810, -6), (key1416, -6), (key1614, -6), (key1334, 2), (key1288, 2), (key1308, 2), (key1769, 2), (key1383, 2), (key1538, 2), (key1785, 2), (key1810, 2), (key1452, 2), (key1652, 2), (key1416, 2), (key1565, 2)]

def rawRow11059 : Integer.Sparse Key := [(key1308, -6), (key1810, -6), (key1614, -6), (key1416, -6), (key1334, 2), (key1308, 2), (key1288, 2), (key1769, 2), (key1538, 2), (key1383, 2), (key1810, 2), (key1785, 2), (key1652, 2), (key1452, 2), (key1565, 2), (key1416, 2)]

def rawRow11060 : Integer.Sparse Key := [(key1416, -6), (key1308, -6), (key1614, -6), (key1810, -6), (key1383, 2), (key1416, 2), (key1452, 2), (key1288, 2), (key1565, 2), (key1785, 2), (key1308, 2), (key1334, 2), (key1538, 2), (key1769, 2), (key1652, 2), (key1810, 2)]

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

def row18449 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18450 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18451 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18452 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18453 : Integer.Sparse Key := [(key970, 24), (key1084, 72), (key1226, 24)]

def row18454 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18455 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18456 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18457 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18458 : Integer.Sparse Key := [(key0, 24), (key83, 96)]

def row18459 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18460 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18461 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18462 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18463 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18464 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18465 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18466 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18467 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18468 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18469 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18470 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2762, 6), (key2768, 12), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3005, 6), (key3019, 12), (key3028, 6)]

def row18471 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18472 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18473 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18474 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18475 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18476 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18477 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18478 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18479 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18480 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18481 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18482 : Integer.Sparse Key := [(key2398, 6), (key2404, 12), (key2435, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2839, 12), (key2845, 12), (key2876, 12), (key2916, 12), (key2925, 6), (key3019, 12), (key3028, 6)]

def row18483 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18484 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18485 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18486 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18487 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18488 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2589, 6), (key2762, 6), (key2768, 12), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def row18489 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18490 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18491 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18492 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18493 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18494 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 12), (key2916, 6), (key2925, 6), (key3019, 6), (key3028, 6)]

def row18495 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3005, 6), (key3028, 6)]

def row18496 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3005, 6), (key3028, 6)]

def row18497 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3028, 6)]

def row18498 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2583, 6), (key2589, 12), (key2604, 6), (key2768, 12), (key2845, 6), (key2876, 12), (key2925, 6), (key3028, 6)]

def row18499 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2570, 6), (key2575, 6), (key2589, 12), (key2762, 6), (key2768, 12), (key2845, 6), (key2876, 12)]

def row18500 : Integer.Sparse Key := [(key2388, 6), (key2398, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 12), (key2768, 12), (key2845, 6), (key2876, 12)]

def row18501 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18502 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18503 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18504 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 6), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2876, 6)]

def row18505 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2589, 6), (key2762, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def row18506 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2464, 12), (key2470, 6), (key2478, 12), (key2501, 12), (key2568, 6), (key2570, 6), (key2575, 6), (key2583, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def row18507 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

def row18508 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

def row18509 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 12)]

def row18510 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

def row18511 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

def row18512 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 12)]

def row18513 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 6)]

def row18514 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6), (key2839, 6)]

def row18515 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 6)]

def row18516 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 6), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6), (key2839, 6)]

def row18517 : Integer.Sparse Key := [(key2370, 6), (key2376, 12), (key2388, 6), (key2404, 12), (key2435, 6), (key2464, 12), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2762, 6)]

def row18518 : Integer.Sparse Key := [(key2376, 12), (key2388, 6), (key2398, 6), (key2404, 12), (key2435, 6), (key2464, 12), (key2470, 12), (key2478, 12), (key2501, 12), (key2568, 12), (key2570, 6), (key2575, 6), (key2583, 6)]

def row18519 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18520 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18521 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18522 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18523 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18524 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18525 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18526 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18527 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18528 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18529 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18530 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18531 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18532 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18533 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18534 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18535 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18536 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18537 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18538 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18539 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18540 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18541 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18542 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18543 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18544 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18545 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18546 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18547 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18548 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18549 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18550 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18551 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18552 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18553 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18554 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18555 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18556 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18557 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18558 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18559 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

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

def row18560 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18561 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18562 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18563 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18564 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18565 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18566 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18567 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18568 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18569 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18570 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18571 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18572 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18573 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18574 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18575 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18576 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18577 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18578 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 48), (key1230, 24)]

def row18579 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18580 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18581 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18582 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18583 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18584 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18585 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18586 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18587 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18588 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18589 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18590 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18591 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18592 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18593 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18594 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18595 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18596 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18597 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18598 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18599 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18600 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18601 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18602 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18603 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18604 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18605 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18606 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18607 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18608 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18609 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18610 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18611 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18612 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18613 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18614 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18615 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18616 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18617 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 4), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18618 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 4), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18619 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18620 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18621 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18622 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18623 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18624 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18625 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18626 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18627 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18628 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18629 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18630 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18631 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18632 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18633 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18634 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18635 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18636 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18637 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18638 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18639 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18640 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18641 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18642 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18643 : Integer.Sparse Key := [(key2355, 24), (key2450, 72), (key2512, 24)]

def row18644 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18645 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18646 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18647 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18648 : Integer.Sparse Key := [(key968, 24), (key1082, 96)]

def row18649 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18650 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18651 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18652 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18653 : Integer.Sparse Key := [(key2585, 24), (key2764, 24), (key2841, 48), (key2873, 24)]

def row18654 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18655 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18656 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18657 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18658 : Integer.Sparse Key := [(key2351, 24), (key2446, 96)]

def row18659 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18660 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18661 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18662 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18663 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18664 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18665 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18666 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18667 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18668 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18669 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18670 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18671 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18672 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18673 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18674 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18675 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18676 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18677 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18678 : Integer.Sparse Key := [(key971, 6), (key979, 18), (key1085, 18), (key1093, 36), (key1164, 18), (key1228, 18), (key1245, 6)]

def row18679 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18680 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18681 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18682 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18683 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18684 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18685 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18686 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18687 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

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

def row18688 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18689 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18690 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18691 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18692 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18693 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18694 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18695 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18696 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18697 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18698 : Integer.Sparse Key := [(key3, 24), (key86, 72), (key147, 24)]

def row18699 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18700 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18701 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18702 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18703 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18704 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18705 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18706 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18707 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18708 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18709 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18710 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18711 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18712 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18713 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18714 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18715 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18716 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18717 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18718 : Integer.Sparse Key := [(key993, 6), (key1001, 12), (key1015, 6), (key1028, 6), (key1036, 12), (key1071, 6), (key1106, 12), (key1114, 12), (key1123, 12), (key1150, 12), (key1232, 12), (key1235, 6), (key1242, 6)]

def row18719 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18720 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18721 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18722 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18723 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18724 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18725 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18726 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18727 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18728 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18729 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18730 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18731 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18732 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18733 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18734 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18735 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18736 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18737 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18738 : Integer.Sparse Key := [(key973, 24), (key1087, 72), (key1160, 24)]

def row18739 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18740 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18741 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18742 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18743 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18744 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18745 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18746 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18747 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18748 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 36), (key202, 6)]

def row18749 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 36), (key202, 6)]

def row18750 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18751 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 30), (key193, 6), (key202, 6)]

def row18752 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18753 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18754 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 24), (key193, 12), (key202, 6)]

def row18755 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18756 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18757 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18758 : Integer.Sparse Key := [(key1, 6), (key7, 18), (key84, 18), (key90, 36), (key151, 18), (key193, 18), (key202, 6)]

def row18759 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18760 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18761 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18762 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18763 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18764 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2456, 24), (key2461, 12), (key2517, 12), (key2523, 24), (key2567, 12), (key2579, 12)]

def row18765 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

def row18766 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

def row18767 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 12), (key2456, 12), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 6), (key2523, 24), (key2567, 6), (key2579, 12)]

def row18768 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 12), (key2519, 12), (key2523, 24), (key2579, 12)]

def row18769 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 24), (key2528, 6), (key2560, 12)]

def row18770 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 12), (key2452, 24), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 24), (key2528, 6), (key2560, 12)]

def row18771 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18772 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18773 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18774 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18775 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18776 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 6), (key2366, 6), (key2452, 18), (key2456, 6), (key2458, 6), (key2461, 6), (key2517, 6), (key2519, 12), (key2523, 12), (key2528, 6), (key2530, 12), (key2560, 12)]

def row18777 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18778 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18779 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18780 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18781 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18782 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18783 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18784 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18785 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18786 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18787 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18788 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2363, 12), (key2452, 12), (key2456, 12), (key2458, 12), (key2517, 6), (key2519, 12), (key2528, 6), (key2530, 24), (key2560, 12)]

def row18789 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18790 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18791 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18792 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18793 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18794 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18795 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18796 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18797 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18798 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18799 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18800 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18801 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18802 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18803 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18804 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18805 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18806 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18807 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18808 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18809 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18810 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18811 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18812 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18813 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18814 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18815 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

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

def row18816 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18817 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18818 : Integer.Sparse Key := [(key974, 24), (key1088, 48), (key1178, 48)]

def row18819 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18820 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18821 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18822 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18823 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18824 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18825 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row18826 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row18827 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row18828 : Integer.Sparse Key := [(key2383, 2), (key2390, 4), (key2394, 8), (key2411, 2), (key2437, 4), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2580, 4), (key2587, 8), (key2593, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2966, 8), (key2968, 4), (key2989, 8)]

def row18829 : Integer.Sparse Key := [(key2383, 2), (key2390, 2), (key2394, 8), (key2411, 2), (key2437, 2), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2587, 8), (key2593, 2), (key2598, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2929, 2), (key2966, 8), (key2968, 4), (key2989, 8), (key3002, 4)]

def row18830 : Integer.Sparse Key := [(key2383, 2), (key2390, 2), (key2394, 8), (key2411, 2), (key2437, 2), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2587, 8), (key2593, 2), (key2598, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2929, 2), (key2966, 8), (key2968, 4), (key2989, 8), (key3002, 4)]

def row18831 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18832 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18833 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18834 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18835 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18836 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18837 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18838 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18839 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18840 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18841 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18842 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18843 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18844 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18845 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18846 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18847 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18848 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18849 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18850 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18851 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18852 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18853 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18854 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18855 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18856 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18857 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18858 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18859 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18860 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18861 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18862 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18863 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18864 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18865 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18866 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18867 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18868 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18869 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18870 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18871 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18872 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18873 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18874 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18875 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18876 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18877 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18878 : Integer.Sparse Key := [(key2360, 24), (key2455, 48), (key2516, 48)]

def row18879 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18880 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18881 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18882 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18883 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18884 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18885 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18886 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18887 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18888 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18889 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18890 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18891 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18892 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18893 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18894 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18895 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18896 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18897 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18898 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18899 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18900 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18901 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18902 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18903 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18904 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18905 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18906 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18907 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18908 : Integer.Sparse Key := [(key976, 12), (key984, 12), (key1090, 24), (key1098, 12), (key1169, 12), (key1180, 12), (key1183, 24), (key1220, 12)]

def row18909 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18910 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18911 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18912 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18913 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18914 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18915 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18916 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18917 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18918 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18919 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18920 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 32), (key2525, 12), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18921 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18922 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18923 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 28), (key2525, 12), (key2532, 4), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18924 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 28), (key2525, 12), (key2532, 4), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18925 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18926 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 12), (key2532, 8), (key2533, 4), (key2562, 8), (key2564, 16)]

def row18927 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18928 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18929 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18930 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18931 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18932 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 8), (key2532, 8), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18933 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 24), (key2525, 8), (key2532, 8), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18934 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18935 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 20), (key2525, 8), (key2532, 12), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18936 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18937 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18938 : Integer.Sparse Key := [(key2362, 4), (key2365, 16), (key2367, 4), (key2457, 8), (key2460, 16), (key2521, 16), (key2525, 8), (key2532, 16), (key2533, 8), (key2562, 8), (key2564, 16)]

def row18939 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18940 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18941 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18942 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18943 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

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

def row18944 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18945 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18946 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18947 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18948 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18949 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18950 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18951 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18952 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18953 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18954 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18955 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18956 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18957 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18958 : Integer.Sparse Key := [(key2354, 6), (key2358, 18), (key2449, 18), (key2453, 36), (key2514, 18), (key2529, 18), (key2559, 6)]

def row18959 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18960 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18961 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18962 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18963 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18964 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18965 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18966 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18967 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18968 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18969 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18970 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18971 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18972 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18973 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18974 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18975 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18976 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18977 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18978 : Integer.Sparse Key := [(key969, 24), (key1083, 72), (key1177, 24)]

def row18979 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18980 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18981 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18982 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18983 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18984 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18985 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18986 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18987 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18988 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18989 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18990 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18991 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18992 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18993 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18994 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18995 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18996 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18997 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18998 : Integer.Sparse Key := [(key2584, 6), (key2588, 12), (key2599, 6), (key2763, 6), (key2767, 12), (key2840, 12), (key2844, 12), (key2875, 12), (key2888, 12), (key2909, 6), (key2930, 6), (key2967, 12), (key2988, 6)]

def row18999 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19000 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19001 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19002 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19003 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19004 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19005 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19006 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19007 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19008 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19009 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19010 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19011 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19012 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19013 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19014 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19015 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19016 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19017 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19018 : Integer.Sparse Key := [(key2352, 24), (key2447, 72), (key2511, 24)]

def row19019 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19020 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19021 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19022 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19023 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19024 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19025 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19026 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19027 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19028 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19029 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19030 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19031 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19032 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19033 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19034 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19035 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19036 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19037 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19038 : Integer.Sparse Key := [(key972, 6), (key977, 18), (key1086, 18), (key1091, 36), (key1162, 18), (key1181, 18), (key1218, 6)]

def row19039 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19040 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19041 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19042 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19043 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19044 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19045 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19046 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19047 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19048 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19049 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19050 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19051 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19052 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19053 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19054 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19055 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19056 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19057 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19058 : Integer.Sparse Key := [(key2361, 12), (key2364, 12), (key2456, 24), (key2459, 12), (key2517, 12), (key2520, 24), (key2531, 12), (key2561, 12)]

def row19059 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19060 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19061 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19062 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19063 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19064 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19065 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19066 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

def row19067 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

def row19068 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 36), (key2558, 6)]

def row19069 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 36), (key2558, 6)]

def row19070 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

def row19071 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 30), (key2527, 6), (key2558, 6)]

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

def row19072 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19073 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19074 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 24), (key2527, 12), (key2558, 6)]

def row19075 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19076 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19077 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19078 : Integer.Sparse Key := [(key2353, 6), (key2356, 18), (key2448, 18), (key2451, 36), (key2513, 18), (key2527, 18), (key2558, 6)]

def row19079 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19080 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19081 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19082 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19083 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19084 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19085 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19086 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19087 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19088 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19089 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19090 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19091 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19092 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19093 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19094 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19095 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19096 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19097 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19098 : Integer.Sparse Key := [(key2372, 18), (key2385, 6), (key2400, 18), (key2432, 6), (key2466, 36), (key2475, 18), (key2498, 18)]

def row19099 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19100 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19101 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19102 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19103 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19104 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19105 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19106 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19107 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19108 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19109 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19110 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19111 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19112 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19113 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19114 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19115 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19116 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19117 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19118 : Integer.Sparse Key := [(key989, 24), (key1024, 24), (key1102, 72)]

def row19119 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19120 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19121 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19122 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19123 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19124 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19125 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19126 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19127 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19128 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19129 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19130 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19131 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19132 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19133 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19134 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19135 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19136 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19137 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19138 : Integer.Sparse Key := [(key2610, 6), (key2626, 12), (key2635, 6), (key2665, 6), (key2700, 12), (key2721, 6), (key2780, 12), (key2789, 6), (key2803, 12), (key2824, 6), (key2853, 12), (key2855, 12), (key2865, 12)]

def row19139 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19140 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19141 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19142 : Integer.Sparse Key := [(key2368, 24), (key2760, 24), (key2837, 72)]

def row19143 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19144 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19145 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19146 : Integer.Sparse Key := [(key2396, 24), (key2581, 24), (key2837, 72)]

def row19147 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

def row19148 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

def row19149 : Integer.Sparse Key := [(key2368, 24), (key2462, 24), (key2760, 24), (key2837, 48)]

def row19150 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

def row19151 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

def row19152 : Integer.Sparse Key := [(key2396, 24), (key2462, 24), (key2581, 24), (key2837, 48)]

def row19153 : Integer.Sparse Key := [(key2368, 24), (key2462, 48), (key2760, 24), (key2837, 24)]

def row19154 : Integer.Sparse Key := [(key2368, 24), (key2462, 48), (key2760, 24), (key2837, 24)]

def row19155 : Integer.Sparse Key := [(key2396, 24), (key2462, 48), (key2581, 24), (key2837, 24)]

def row19156 : Integer.Sparse Key := [(key2396, 24), (key2462, 48), (key2581, 24), (key2837, 24)]

def row19157 : Integer.Sparse Key := [(key2368, 24), (key2462, 72), (key2760, 24)]

def row19158 : Integer.Sparse Key := [(key2396, 24), (key2462, 72), (key2581, 24)]

def row19159 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19160 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19161 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19162 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19163 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19164 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19165 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19166 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19167 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19168 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19169 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19170 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19171 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19172 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19173 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19174 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19175 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19176 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19177 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19178 : Integer.Sparse Key := [(key995, 18), (key1011, 6), (key1030, 18), (key1067, 6), (key1108, 36), (key1119, 18), (key1146, 18)]

def row19179 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19180 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19181 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19182 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19183 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19184 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19185 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19186 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19187 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19188 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19189 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19190 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19191 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19192 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19193 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19194 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19195 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19196 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19197 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19198 : Integer.Sparse Key := [(key2377, 12), (key2389, 12), (key2405, 12), (key2436, 12), (key2471, 12), (key2479, 24), (key2502, 24), (key2518, 12)]

def row19199 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

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

def row19200 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19201 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19202 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19203 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19204 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19205 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19206 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19207 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19208 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19209 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19210 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19211 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19212 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19213 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19214 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19215 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19216 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19217 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19218 : Integer.Sparse Key := [(key2369, 18), (key2384, 6), (key2397, 18), (key2431, 6), (key2463, 36), (key2474, 18), (key2497, 18)]

def row19219 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19220 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19221 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19222 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19223 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19224 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19225 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19226 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 36), (key2799, 18), (key2849, 36)]

def row19227 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19228 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19229 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19230 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

def row19231 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

def row19232 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 30), (key2776, 6), (key2799, 18), (key2849, 36)]

def row19233 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19234 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19235 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 24), (key2776, 12), (key2799, 18), (key2849, 36)]

def row19236 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 24), (key2776, 12), (key2799, 18), (key2849, 36)]

def row19237 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19238 : Integer.Sparse Key := [(key2606, 6), (key2622, 18), (key2661, 6), (key2696, 18), (key2776, 18), (key2799, 18), (key2849, 36)]

def row19239 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19240 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19241 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19242 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19243 : Integer.Sparse Key := [(key1850, 24), (key1852, 72), (key1884, 24)]

def row19244 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19245 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19246 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19247 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19248 : Integer.Sparse Key := [(key685, 96), (key692, 24)]

def row19249 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19250 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19251 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19252 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19253 : Integer.Sparse Key := [(key1859, 24), (key1861, 48), (key1867, 24), (key1877, 24)]

def row19254 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19255 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19256 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19257 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19258 : Integer.Sparse Key := [(key1957, 96), (key1969, 24)]

def row19259 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19260 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19261 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19262 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19263 : Integer.Sparse Key := [(key617, 24), (key619, 72), (key645, 24)]

def row19264 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19265 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19266 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19267 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19268 : Integer.Sparse Key := [(key1851, 48), (key1855, 48), (key1886, 24)]

def row19269 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19270 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19271 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19272 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19273 : Integer.Sparse Key := [(key1932, 24), (key1933, 72), (key1953, 24)]

def row19274 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19275 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19276 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19277 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19278 : Integer.Sparse Key := [(key1958, 72), (key1960, 24), (key1966, 24)]

def row19279 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19280 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19281 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19282 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19283 : Integer.Sparse Key := [(key288, 24), (key289, 96)]

def row19284 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19285 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19286 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19287 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19288 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19289 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19290 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19291 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19292 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19293 : Integer.Sparse Key := [(key2416, 36), (key2423, 36), (key2489, 12), (key2491, 36)]

def row19294 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19295 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19296 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19297 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19298 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19299 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19300 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19301 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19302 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19303 : Integer.Sparse Key := [(key1045, 72), (key1131, 48)]

def row19304 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19305 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19306 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19307 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19308 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19309 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19310 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19311 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19312 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19313 : Integer.Sparse Key := [(key2681, 24), (key2688, 12), (key2712, 12), (key2714, 24), (key2815, 12), (key2817, 24), (key2863, 12)]

def row19314 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19315 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19316 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19317 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19318 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19319 : Integer.Sparse Key := [(key2412, 24), (key3031, 48), (key3118, 48)]

def row19320 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

def row19321 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

def row19322 : Integer.Sparse Key := [(key2412, 24), (key2485, 24), (key3031, 48), (key3118, 24)]

def row19323 : Integer.Sparse Key := [(key2412, 24), (key2485, 48), (key3031, 48)]

def row19324 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19325 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19326 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19327 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

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

def row19328 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19329 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19330 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19331 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19332 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19333 : Integer.Sparse Key := [(key1050, 36), (key1058, 36), (key1136, 12), (key1138, 36)]

def row19334 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19335 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19336 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19337 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19338 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19339 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19340 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19341 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19342 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19343 : Integer.Sparse Key := [(key2420, 12), (key2427, 48), (key2438, 12), (key2495, 24), (key2504, 24)]

def row19344 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19345 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19346 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19347 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19348 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19349 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19350 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19351 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19352 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19353 : Integer.Sparse Key := [(key2413, 36), (key2422, 36), (key2486, 12), (key2490, 36)]

def row19354 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

def row19355 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

def row19356 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key3045, 18), (key3059, 24), (key3094, 36), (key3122, 12)]

def row19357 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 6), (key3045, 18), (key3059, 24), (key3094, 30), (key3122, 12)]

def row19358 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 6), (key3045, 18), (key3059, 24), (key3094, 30), (key3122, 12)]

def row19359 : Integer.Sparse Key := [(key2677, 18), (key2708, 12), (key2811, 12), (key3045, 18), (key3059, 24), (key3094, 24), (key3122, 12)]

def row19360 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 18), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 18)]

def row19361 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 18), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 18)]

def row19362 : Integer.Sparse Key := [(key2677, 18), (key2708, 24), (key2811, 24), (key2861, 12), (key3045, 18), (key3059, 12), (key3094, 12)]

def row19363 : Integer.Sparse Key := [(key2677, 18), (key2708, 36), (key2811, 36), (key2861, 12), (key3045, 18)]

def row19364 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19365 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19366 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19367 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19368 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19369 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19370 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19371 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19372 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19373 : Integer.Sparse Key := [(key1962, 48), (key1964, 72)]

def row19374 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19375 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19376 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19377 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19378 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19379 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19380 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19381 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19382 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

def row19383 : Integer.Sparse Key := [(key3079, 12), (key3084, 72), (key3099, 36)]

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

def row19724 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19725 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19726 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19727 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19728 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19729 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19730 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19731 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19732 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19733 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19734 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19735 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19736 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19737 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19738 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19739 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19740 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19741 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19742 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19743 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19744 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19745 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19746 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19747 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19748 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19749 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19750 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19751 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19752 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19753 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19754 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19755 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19756 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19757 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19758 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19759 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19760 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19761 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19762 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19763 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19764 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19765 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19766 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19767 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19768 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19769 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19770 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19771 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19772 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19773 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19774 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19775 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19776 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19777 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19778 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19779 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19780 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19781 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19782 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19783 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, 4), (key1319, 4), (key1327, 4), (key1352, 4), (key1355, 2), (key1386, 2), (key1394, 4), (key1419, 4), (key1427, 4), (key1445, 4), (key1473, 4), (key1481, 2), (key1541, 4), (key1549, 4), (key1557, 4), (key1568, 4), (key1576, 4), (key1594, 4), (key1617, 4), (key1625, 4), (key1634, 4), (key1682, 4), (key1684, 4), (key1690, 4), (key1897, 4), (key1900, 2), (key1904, 4), (key1912, 2), (key1919, 4), (key1921, 4), (key1927, 4)]

def row19788 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19789 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19790 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19791 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19792 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19793 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19794 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19795 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19796 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19797 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19798 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19799 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19800 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19801 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19802 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19803 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19804 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19805 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19806 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19807 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19808 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19809 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19810 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19811 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19812 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19813 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19814 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19815 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19816 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19817 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19818 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19819 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19820 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19821 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19822 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19823 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19824 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19825 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19826 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19827 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19828 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19829 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19830 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19831 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19832 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19833 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19834 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19835 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19836 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19837 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19838 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19839 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

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

def row19840 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19841 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19842 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19843 : Integer.Sparse Key := [(key1253, 24), (key1528, 24), (key1606, 48), (key1636, 24)]

def row19844 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19845 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19846 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19847 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19848 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19849 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19850 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19851 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19852 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19853 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19854 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19855 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key375, 6), (key381, 12), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key654, 6), (key659, 12), (key663, 6)]

def row19856 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19857 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19858 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19859 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19860 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19861 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19862 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19863 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19864 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19865 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19866 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19867 : Integer.Sparse Key := [(key43, 6), (key48, 12), (key74, 6), (key206, 6), (key212, 12), (key218, 6), (key426, 12), (key432, 12), (key460, 12), (key486, 12), (key490, 6), (key659, 12), (key663, 6)]

def row19868 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19869 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19870 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19871 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19872 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19873 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key212, 6), (key375, 6), (key381, 12), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key654, 6), (key659, 6), (key663, 6)]

def row19874 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19875 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19876 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19877 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19878 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19879 : Integer.Sparse Key := [(key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 6), (key137, 6), (key206, 6), (key212, 12), (key218, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 12), (key486, 6), (key490, 6), (key659, 6), (key663, 6)]

def row19880 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key654, 6), (key663, 6)]

def row19881 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key654, 6), (key663, 6)]

def row19882 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key206, 6), (key212, 12), (key218, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key663, 6)]

def row19883 : Integer.Sparse Key := [(key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key206, 6), (key212, 12), (key218, 6), (key381, 12), (key432, 6), (key460, 12), (key490, 6), (key663, 6)]

def row19884 : Integer.Sparse Key := [(key18, 6), (key35, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key196, 6), (key200, 6), (key212, 12), (key375, 6), (key381, 12), (key432, 6), (key460, 12)]

def row19885 : Integer.Sparse Key := [(key35, 6), (key43, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key196, 6), (key200, 6), (key206, 6), (key212, 12), (key381, 12), (key432, 6), (key460, 12)]

def row19886 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19887 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19888 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19889 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 6), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key426, 6), (key432, 6), (key460, 6)]

def row19890 : Integer.Sparse Key := [(key18, 6), (key23, 6), (key35, 6), (key48, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key212, 6), (key375, 6), (key381, 6), (key432, 6), (key460, 6)]

def row19891 : Integer.Sparse Key := [(key23, 6), (key35, 6), (key43, 6), (key48, 6), (key74, 6), (key100, 12), (key105, 6), (key115, 12), (key137, 12), (key195, 6), (key196, 6), (key200, 6), (key206, 6), (key212, 6), (key381, 6), (key432, 6), (key460, 6)]

def row19892 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

def row19893 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

def row19894 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 12)]

def row19895 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

def row19896 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

def row19897 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 12)]

def row19898 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 6)]

def row19899 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6), (key426, 6)]

def row19900 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 6)]

def row19901 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 6), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6), (key426, 6)]

def row19902 : Integer.Sparse Key := [(key18, 6), (key23, 12), (key35, 6), (key48, 12), (key74, 6), (key100, 12), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key375, 6)]

def row19903 : Integer.Sparse Key := [(key23, 12), (key35, 6), (key43, 6), (key48, 12), (key74, 6), (key100, 12), (key105, 12), (key115, 12), (key137, 12), (key195, 12), (key196, 6), (key200, 6), (key206, 6)]

def row19904 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19905 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19906 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19907 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19908 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19909 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19910 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19911 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19912 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19913 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19914 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19915 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19916 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19917 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19918 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19919 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19920 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19921 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19922 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19923 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19924 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19925 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19926 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19927 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19928 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19929 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19930 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19931 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19932 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19933 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19934 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19935 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19936 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19937 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19938 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19939 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19940 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19941 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19942 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19943 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19944 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19945 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19946 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19947 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19948 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19949 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19950 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19951 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19952 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19953 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19954 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19955 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19956 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19957 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19958 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19959 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19960 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19961 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19962 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19963 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19964 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19965 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19966 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19967 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

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

def row19968 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19969 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19970 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19971 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19972 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19973 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19974 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19975 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19976 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19977 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19978 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19979 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19980 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19981 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19982 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19983 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19984 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19985 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19986 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19987 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19988 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19989 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19990 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19991 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19992 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19993 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19994 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19995 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19996 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19997 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19998 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row19999 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20000 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20001 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20002 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20003 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20004 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20005 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20006 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20007 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20008 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20009 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20010 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20011 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20012 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20013 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20014 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20015 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20016 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20017 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20018 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20019 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20020 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20021 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20022 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20023 : Integer.Sparse Key := [(key1252, 6), (key1257, 12), (key1266, 6), (key1527, 6), (key1532, 12), (key1605, 12), (key1610, 12), (key1638, 12), (key1649, 12), (key1672, 6), (key1766, 6), (key1807, 12), (key1830, 6)]

def row20024 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20025 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20026 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20027 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20028 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20029 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20030 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20031 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20032 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20033 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20034 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20035 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20036 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20037 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20038 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20039 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20040 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20041 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20042 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20043 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20044 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20045 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20046 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20047 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20048 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20049 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20050 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20051 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20052 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20053 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20054 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20055 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20056 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20057 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20058 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20059 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20060 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20061 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20062 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20063 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20064 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20065 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20066 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20067 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20068 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20069 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20070 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20071 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20072 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20073 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20074 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20075 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20076 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20077 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20078 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20079 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20080 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20081 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20082 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20083 : Integer.Sparse Key := [(key1293, 6), (key1313, 12), (key1323, 6), (key1388, 6), (key1421, 12), (key1441, 6), (key1543, 12), (key1553, 6), (key1570, 12), (key1590, 6), (key1619, 12), (key1621, 12), (key1630, 12)]

def row20084 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20085 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20086 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20087 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20088 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20089 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20090 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20091 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20092 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20093 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20094 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20095 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

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

def row20097 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20098 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20099 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20100 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20101 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20102 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20103 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20104 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20105 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20106 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20107 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20108 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20109 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20110 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20111 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20112 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20113 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20114 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20115 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20116 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20117 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20118 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20119 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20120 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20121 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20122 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20123 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20124 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20125 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20126 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20127 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20128 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20129 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20130 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20131 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20132 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20133 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20134 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20135 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20136 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20137 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20138 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20139 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20140 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20141 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20142 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20143 : Integer.Sparse Key := [(key626, 24), (key627, 48), (key629, 24), (key640, 24)]

def row20144 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20145 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20146 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20147 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20148 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20149 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20150 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20151 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20152 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20153 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20154 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20155 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20156 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20157 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20158 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20159 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20160 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20161 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20162 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20163 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20164 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20165 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20166 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20167 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20168 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20169 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20170 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20171 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20172 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20173 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20174 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20175 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20176 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20177 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20178 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20179 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20180 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20181 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20182 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20183 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20184 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20185 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20186 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20187 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20188 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20189 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20190 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20191 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20192 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20193 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20194 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20195 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20196 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20197 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20198 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20199 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20200 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20201 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20202 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

def row20203 : Integer.Sparse Key := [(key1407, 24), (key1411, 12), (key1435, 12), (key1436, 24), (key1584, 12), (key1585, 24), (key1628, 12)]

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

def row20301 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20302 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 4), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20303 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 4), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20304 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20305 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 8), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 8), (key347, 2), (key385, 4), (key390, 4), (key400, 8), (key406, 4), (key411, 4), (key421, 8), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key656, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20306 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20307 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20308 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 2), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20309 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 2), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20310 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20311 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 6), (key277, 2), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 6), (key346, 2), (key347, 2), (key385, 4), (key390, 4), (key400, 6), (key406, 4), (key411, 4), (key421, 6), (key435, 4), (key445, 6), (key453, 6), (key487, 2), (key488, 4), (key489, 4), (key655, 2), (key656, 2), (key657, 2), (key658, 2), (key660, 2), (key661, 4), (key662, 4)]

def row20312 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20313 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20314 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20315 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20316 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20317 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 8), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20318 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20319 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20320 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20321 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 6), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 2), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20322 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

def row20323 : Integer.Sparse Key := [(key236, 2), (key241, 4), (key248, 4), (key253, 4), (key263, 4), (key277, 4), (key278, 2), (key302, 2), (key307, 4), (key316, 4), (key321, 4), (key331, 4), (key346, 4), (key347, 2), (key385, 4), (key390, 4), (key400, 4), (key406, 4), (key411, 4), (key421, 4), (key435, 4), (key445, 4), (key453, 4), (key487, 4), (key488, 4), (key489, 4), (key655, 4), (key656, 2), (key657, 4), (key658, 2), (key660, 4), (key661, 4), (key662, 4)]

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

def rawRow1000 : Integer.Sparse Key := [(key48, -2), (key48, -2), (key74, -2), (key43, 6), (key460, 2), (key460, 2), (key663, 2), (key206, -2), (key426, -2), (key426, -2), (key490, -6), (key218, 2), (key486, 2), (key486, 2)]

def rawRow1001 : Integer.Sparse Key := [(key48, -2), (key74, -2), (key48, -2), (key43, 6), (key460, 2), (key663, 2), (key460, 2), (key426, -2), (key206, -2), (key426, -2), (key490, -6), (key486, 2), (key218, 2), (key486, 2)]

def rawRow1002 : Integer.Sparse Key := [(key74, -2), (key48, -2), (key48, -2), (key43, 6), (key663, 2), (key460, 2), (key460, 2), (key426, -2), (key426, -2), (key206, -2), (key490, -6), (key486, 2), (key486, 2), (key218, 2)]

def rawRow1003 : Integer.Sparse Key := [(key100, -2), (key105, -2), (key137, -2), (key115, 6), (key43, 2), (key48, 2), (key74, 2), (key218, -2), (key486, -2), (key490, -2), (key381, -6), (key212, 2), (key432, 2), (key460, 2)]

def rawRow1004 : Integer.Sparse Key := [(key105, -2), (key100, -2), (key137, -2), (key115, 6), (key48, 2), (key43, 2), (key74, 2), (key218, -2), (key490, -2), (key486, -2), (key381, -6), (key212, 2), (key460, 2), (key432, 2)]

def rawRow1005 : Integer.Sparse Key := [(key100, -2), (key137, -2), (key105, -2), (key115, 6), (key43, 2), (key74, 2), (key48, 2), (key486, -2), (key218, -2), (key490, -2), (key381, -6), (key432, 2), (key212, 2), (key460, 2)]

def rawRow1006 : Integer.Sparse Key := [(key137, -2), (key100, -2), (key105, -2), (key115, 6), (key74, 2), (key43, 2), (key48, 2), (key486, -2), (key490, -2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key212, 2)]

def rawRow1007 : Integer.Sparse Key := [(key105, -2), (key137, -2), (key100, -2), (key115, 6), (key48, 2), (key74, 2), (key43, 2), (key490, -2), (key218, -2), (key486, -2), (key381, -6), (key460, 2), (key212, 2), (key432, 2)]

def rawRow1008 : Integer.Sparse Key := [(key137, -2), (key105, -2), (key100, -2), (key115, 6), (key74, 2), (key48, 2), (key43, 2), (key490, -2), (key486, -2), (key218, -2), (key381, -6), (key460, 2), (key432, 2), (key212, 2)]

def rawRow1009 : Integer.Sparse Key := [(key105, -2), (key115, -2), (key137, -2), (key100, 6), (key195, 2), (key196, 2), (key200, 2), (key18, -2), (key375, -2), (key426, -2), (key460, -6), (key212, 2), (key381, 2), (key432, 2)]

def rawRow1010 : Integer.Sparse Key := [(key115, -2), (key105, -2), (key137, -2), (key100, 6), (key196, 2), (key195, 2), (key200, 2), (key18, -2), (key426, -2), (key375, -2), (key460, -6), (key212, 2), (key432, 2), (key381, 2)]

def rawRow1011 : Integer.Sparse Key := [(key105, -2), (key137, -2), (key115, -2), (key100, 6), (key195, 2), (key200, 2), (key196, 2), (key43, -2), (key206, -2), (key426, -2), (key460, -6), (key381, 2), (key212, 2), (key432, 2)]

def rawRow1012 : Integer.Sparse Key := [(key137, -2), (key105, -2), (key115, -2), (key100, 6), (key200, 2), (key195, 2), (key196, 2), (key43, -2), (key426, -2), (key206, -2), (key460, -6), (key381, 2), (key432, 2), (key212, 2)]

def rawRow1013 : Integer.Sparse Key := [(key115, -2), (key137, -2), (key105, -2), (key100, 6), (key196, 2), (key200, 2), (key195, 2), (key100, -2), (key18, -2), (key375, -2), (key460, -6), (key432, 2), (key212, 2), (key381, 2)]

def rawRow1014 : Integer.Sparse Key := [(key137, -2), (key115, -2), (key105, -2), (key100, 6), (key200, 2), (key196, 2), (key195, 2), (key100, -2), (key43, -2), (key206, -2), (key460, -6), (key432, 2), (key381, 2), (key212, 2)]

def rawRow1015 : Integer.Sparse Key := [(key195, -2), (key195, -2), (key200, -2), (key196, 6), (key48, 2), (key48, 2), (key74, 2), (key35, -2), (key115, -2), (key115, -2), (key43, -6), (key206, 2), (key426, 2), (key426, 2)]

def rawRow1016 : Integer.Sparse Key := [(key195, -2), (key200, -2), (key195, -2), (key196, 6), (key48, 2), (key74, 2), (key48, 2), (key115, -2), (key35, -2), (key115, -2), (key43, -6), (key426, 2), (key206, 2), (key426, 2)]

def rawRow1017 : Integer.Sparse Key := [(key200, -2), (key195, -2), (key195, -2), (key196, 6), (key74, 2), (key48, 2), (key48, 2), (key115, -2), (key115, -2), (key35, -2), (key43, -6), (key426, 2), (key426, 2), (key206, 2)]

def rawRow1018 : Integer.Sparse Key := [(key195, -2), (key196, -2), (key200, -2), (key195, 6), (key105, 2), (key115, 2), (key137, 2), (key23, -2), (key48, -2), (key105, -2), (key100, -6), (key18, 2), (key375, 2), (key426, 2)]

def rawRow1019 : Integer.Sparse Key := [(key196, -2), (key195, -2), (key200, -2), (key195, 6), (key115, 2), (key105, 2), (key137, 2), (key23, -2), (key105, -2), (key48, -2), (key100, -6), (key18, 2), (key426, 2), (key375, 2)]

def rawRow1020 : Integer.Sparse Key := [(key195, -2), (key200, -2), (key196, -2), (key195, 6), (key105, 2), (key137, 2), (key115, 2), (key48, -2), (key23, -2), (key105, -2), (key100, -6), (key43, 2), (key206, 2), (key426, 2)]

def rawRow1021 : Integer.Sparse Key := [(key200, -2), (key195, -2), (key196, -2), (key195, 6), (key137, 2), (key105, 2), (key115, 2), (key48, -2), (key105, -2), (key23, -2), (key100, -6), (key43, 2), (key426, 2), (key206, 2)]

def rawRow1022 : Integer.Sparse Key := [(key196, -2), (key200, -2), (key195, -2), (key195, 6), (key115, 2), (key137, 2), (key105, 2), (key105, -2), (key23, -2), (key48, -2), (key100, -6), (key100, 2), (key18, 2), (key375, 2)]

def rawRow1023 : Integer.Sparse Key := [(key200, -2), (key196, -2), (key195, -2), (key195, 6), (key137, 2), (key115, 2), (key105, 2), (key105, -2), (key48, -2), (key23, -2), (key100, -6), (key100, 2), (key43, 2), (key206, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1024 : Integer.Sparse Key := [(key1543, -6), (key1388, 2), (key1543, 2), (key1553, 2), (key1570, 6), (key1293, -2), (key1570, -2), (key1590, -2), (key1421, -2), (key1619, -2), (key1621, -2), (key1313, 2), (key1619, 2), (key1630, 2)]

def rawRow1025 : Integer.Sparse Key := [(key1543, -6), (key1388, 2), (key1553, 2), (key1543, 2), (key1570, 6), (key1293, -2), (key1590, -2), (key1570, -2), (key1421, -2), (key1621, -2), (key1619, -2), (key1313, 2), (key1630, 2), (key1619, 2)]

def rawRow1026 : Integer.Sparse Key := [(key1543, -6), (key1543, 2), (key1388, 2), (key1553, 2), (key1570, 6), (key1570, -2), (key1293, -2), (key1590, -2), (key1619, -2), (key1421, -2), (key1621, -2), (key1619, 2), (key1313, 2), (key1630, 2)]

def rawRow1027 : Integer.Sparse Key := [(key1543, -6), (key1543, 2), (key1553, 2), (key1388, 2), (key1570, 6), (key1570, -2), (key1590, -2), (key1293, -2), (key1619, -2), (key1621, -2), (key1421, -2), (key1619, 2), (key1630, 2), (key1313, 2)]

def rawRow1028 : Integer.Sparse Key := [(key1543, -6), (key1553, 2), (key1388, 2), (key1543, 2), (key1570, 6), (key1590, -2), (key1293, -2), (key1570, -2), (key1621, -2), (key1421, -2), (key1619, -2), (key1630, 2), (key1313, 2), (key1619, 2)]

def rawRow1029 : Integer.Sparse Key := [(key1543, -6), (key1553, 2), (key1543, 2), (key1388, 2), (key1570, 6), (key1590, -2), (key1570, -2), (key1293, -2), (key1621, -2), (key1619, -2), (key1421, -2), (key1630, 2), (key1619, 2), (key1313, 2)]

def rawRow1030 : Integer.Sparse Key := [(key1553, -6), (key1388, 2), (key1543, 2), (key1543, 2), (key1590, 6), (key1293, -2), (key1570, -2), (key1570, -2), (key1441, -2), (key1630, -2), (key1630, -2), (key1323, 2), (key1621, 2), (key1621, 2)]

def rawRow1031 : Integer.Sparse Key := [(key1553, -6), (key1543, 2), (key1388, 2), (key1543, 2), (key1590, 6), (key1570, -2), (key1293, -2), (key1570, -2), (key1630, -2), (key1441, -2), (key1630, -2), (key1621, 2), (key1323, 2), (key1621, 2)]

def rawRow1032 : Integer.Sparse Key := [(key1553, -6), (key1543, 2), (key1543, 2), (key1388, 2), (key1590, 6), (key1570, -2), (key1570, -2), (key1293, -2), (key1630, -2), (key1630, -2), (key1441, -2), (key1621, 2), (key1621, 2), (key1323, 2)]

def rawRow1033 : Integer.Sparse Key := [(key1570, -6), (key1421, 2), (key1619, 2), (key1621, 2), (key1543, 6), (key1313, -2), (key1619, -2), (key1630, -2), (key1388, -2), (key1543, -2), (key1553, -2), (key1293, 2), (key1570, 2), (key1590, 2)]

def rawRow1034 : Integer.Sparse Key := [(key1570, -6), (key1421, 2), (key1621, 2), (key1619, 2), (key1543, 6), (key1313, -2), (key1630, -2), (key1619, -2), (key1388, -2), (key1553, -2), (key1543, -2), (key1293, 2), (key1590, 2), (key1570, 2)]

def rawRow1035 : Integer.Sparse Key := [(key1570, -6), (key1619, 2), (key1421, 2), (key1621, 2), (key1543, 6), (key1619, -2), (key1313, -2), (key1630, -2), (key1543, -2), (key1388, -2), (key1553, -2), (key1570, 2), (key1293, 2), (key1590, 2)]

def rawRow1036 : Integer.Sparse Key := [(key1570, -6), (key1619, 2), (key1621, 2), (key1421, 2), (key1543, 6), (key1619, -2), (key1630, -2), (key1313, -2), (key1543, -2), (key1553, -2), (key1388, -2), (key1570, 2), (key1590, 2), (key1293, 2)]

def rawRow1037 : Integer.Sparse Key := [(key1570, -6), (key1621, 2), (key1421, 2), (key1619, 2), (key1543, 6), (key1630, -2), (key1313, -2), (key1619, -2), (key1553, -2), (key1388, -2), (key1543, -2), (key1590, 2), (key1293, 2), (key1570, 2)]

def rawRow1038 : Integer.Sparse Key := [(key1570, -6), (key1621, 2), (key1619, 2), (key1421, 2), (key1543, 6), (key1630, -2), (key1619, -2), (key1313, -2), (key1553, -2), (key1543, -2), (key1388, -2), (key1590, 2), (key1570, 2), (key1293, 2)]

def rawRow1039 : Integer.Sparse Key := [(key1621, -6), (key1421, 2), (key1570, 2), (key1619, 2), (key1630, 6), (key1313, -2), (key1543, -2), (key1619, -2), (key1441, -2), (key1590, -2), (key1630, -2), (key1323, 2), (key1553, 2), (key1621, 2)]

def rawRow1040 : Integer.Sparse Key := [(key1621, -6), (key1421, 2), (key1619, 2), (key1570, 2), (key1630, 6), (key1313, -2), (key1619, -2), (key1543, -2), (key1441, -2), (key1630, -2), (key1590, -2), (key1323, 2), (key1621, 2), (key1553, 2)]

def rawRow1041 : Integer.Sparse Key := [(key1621, -6), (key1570, 2), (key1421, 2), (key1619, 2), (key1630, 6), (key1543, -2), (key1313, -2), (key1619, -2), (key1590, -2), (key1441, -2), (key1630, -2), (key1553, 2), (key1323, 2), (key1621, 2)]

def rawRow1042 : Integer.Sparse Key := [(key1621, -6), (key1570, 2), (key1619, 2), (key1421, 2), (key1630, 6), (key1543, -2), (key1619, -2), (key1313, -2), (key1590, -2), (key1630, -2), (key1441, -2), (key1553, 2), (key1621, 2), (key1323, 2)]

def rawRow1043 : Integer.Sparse Key := [(key1621, -6), (key1619, 2), (key1421, 2), (key1570, 2), (key1630, 6), (key1619, -2), (key1313, -2), (key1543, -2), (key1630, -2), (key1441, -2), (key1590, -2), (key1621, 2), (key1323, 2), (key1553, 2)]

def rawRow1044 : Integer.Sparse Key := [(key1621, -6), (key1619, 2), (key1570, 2), (key1421, 2), (key1630, 6), (key1619, -2), (key1543, -2), (key1313, -2), (key1630, -2), (key1590, -2), (key1441, -2), (key1621, 2), (key1553, 2), (key1323, 2)]

def rawRow1045 : Integer.Sparse Key := [(key1590, -6), (key1441, 2), (key1630, 2), (key1630, 2), (key1553, 6), (key1323, -2), (key1621, -2), (key1621, -2), (key1388, -2), (key1543, -2), (key1543, -2), (key1293, 2), (key1570, 2), (key1570, 2)]

def rawRow1046 : Integer.Sparse Key := [(key1590, -6), (key1630, 2), (key1441, 2), (key1630, 2), (key1553, 6), (key1621, -2), (key1323, -2), (key1621, -2), (key1543, -2), (key1388, -2), (key1543, -2), (key1570, 2), (key1293, 2), (key1570, 2)]

def rawRow1047 : Integer.Sparse Key := [(key1590, -6), (key1630, 2), (key1630, 2), (key1441, 2), (key1553, 6), (key1621, -2), (key1621, -2), (key1323, -2), (key1543, -2), (key1543, -2), (key1388, -2), (key1570, 2), (key1570, 2), (key1293, 2)]

def rawRow1048 : Integer.Sparse Key := [(key1630, -6), (key1441, 2), (key1590, 2), (key1630, 2), (key1621, 6), (key1323, -2), (key1553, -2), (key1621, -2), (key1421, -2), (key1570, -2), (key1619, -2), (key1313, 2), (key1543, 2), (key1619, 2)]

def rawRow1049 : Integer.Sparse Key := [(key1630, -6), (key1441, 2), (key1630, 2), (key1590, 2), (key1621, 6), (key1323, -2), (key1621, -2), (key1553, -2), (key1421, -2), (key1619, -2), (key1570, -2), (key1313, 2), (key1619, 2), (key1543, 2)]

def rawRow1050 : Integer.Sparse Key := [(key1630, -6), (key1590, 2), (key1441, 2), (key1630, 2), (key1621, 6), (key1553, -2), (key1323, -2), (key1621, -2), (key1570, -2), (key1421, -2), (key1619, -2), (key1543, 2), (key1313, 2), (key1619, 2)]

def rawRow1051 : Integer.Sparse Key := [(key1630, -6), (key1590, 2), (key1630, 2), (key1441, 2), (key1621, 6), (key1553, -2), (key1621, -2), (key1323, -2), (key1570, -2), (key1619, -2), (key1421, -2), (key1543, 2), (key1619, 2), (key1313, 2)]

def rawRow1052 : Integer.Sparse Key := [(key1630, -6), (key1630, 2), (key1441, 2), (key1590, 2), (key1621, 6), (key1621, -2), (key1323, -2), (key1553, -2), (key1619, -2), (key1421, -2), (key1570, -2), (key1619, 2), (key1313, 2), (key1543, 2)]

def rawRow1053 : Integer.Sparse Key := [(key1630, -6), (key1630, 2), (key1590, 2), (key1441, 2), (key1621, 6), (key1621, -2), (key1553, -2), (key1323, -2), (key1619, -2), (key1570, -2), (key1421, -2), (key1619, 2), (key1543, 2), (key1313, 2)]

def rawRow1054 : Integer.Sparse Key := [(key236, -1), (key241, -1), (key406, -1), (key421, -1), (key657, -1), (key658, -1), (key241, 2), (key411, 2), (key421, 2), (key248, 1), (key253, 1), (key435, 1), (key453, 1), (key660, 1), (key662, 1), (key253, -1), (key263, -1), (key321, -1), (key331, -1), (key445, -1), (key453, -1), (key277, -2), (key487, -2), (key489, -2), (key277, 1), (key278, 1), (key346, 1), (key347, 1), (key488, 1), (key489, 1)]

def rawRow1055 : Integer.Sparse Key := [(key241, -1), (key236, -1), (key421, -1), (key406, -1), (key658, -1), (key657, -1), (key241, 2), (key421, 2), (key411, 2), (key253, 1), (key248, 1), (key453, 1), (key435, 1), (key662, 1), (key660, 1), (key263, -1), (key253, -1), (key331, -1), (key321, -1), (key453, -1), (key445, -1), (key277, -2), (key489, -2), (key487, -2), (key278, 1), (key277, 1), (key347, 1), (key346, 1), (key489, 1), (key488, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1056 : Integer.Sparse Key := [(key406, -1), (key421, -1), (key236, -1), (key658, -1), (key241, -1), (key421, -1), (key411, 2), (key241, 2), (key421, 2), (key435, 1), (key660, 1), (key248, 1), (key662, 1), (key253, 1), (key453, 1), (key321, -1), (key445, -1), (key253, -1), (key453, -1), (key263, -1), (key331, -1), (key487, -2), (key277, -2), (key489, -2), (key346, 1), (key488, 1), (key277, 1), (key489, 1), (key278, 1), (key347, 1)]

def rawRow1057 : Integer.Sparse Key := [(key421, -1), (key406, -1), (key658, -1), (key236, -1), (key421, -1), (key241, -1), (key411, 2), (key421, 2), (key241, 2), (key660, 1), (key435, 1), (key662, 1), (key248, 1), (key453, 1), (key253, 1), (key445, -1), (key321, -1), (key453, -1), (key253, -1), (key331, -1), (key263, -1), (key487, -2), (key489, -2), (key277, -2), (key488, 1), (key346, 1), (key489, 1), (key277, 1), (key347, 1), (key278, 1)]

def rawRow1058 : Integer.Sparse Key := [(key657, -1), (key658, -1), (key241, -1), (key421, -1), (key236, -1), (key406, -1), (key421, 2), (key241, 2), (key411, 2), (key453, 1), (key662, 1), (key253, 1), (key660, 1), (key248, 1), (key435, 1), (key331, -1), (key453, -1), (key263, -1), (key445, -1), (key253, -1), (key321, -1), (key489, -2), (key277, -2), (key487, -2), (key347, 1), (key489, 1), (key278, 1), (key488, 1), (key277, 1), (key346, 1)]

def rawRow1059 : Integer.Sparse Key := [(key658, -1), (key657, -1), (key421, -1), (key241, -1), (key406, -1), (key236, -1), (key421, 2), (key411, 2), (key241, 2), (key662, 1), (key453, 1), (key660, 1), (key253, 1), (key435, 1), (key248, 1), (key453, -1), (key331, -1), (key445, -1), (key263, -1), (key321, -1), (key253, -1), (key489, -2), (key487, -2), (key277, -2), (key489, 1), (key347, 1), (key488, 1), (key278, 1), (key346, 1), (key277, 1)]

def rawRow1060 : Integer.Sparse Key := [(key241, -1), (key241, -1), (key411, -1), (key411, -1), (key421, -1), (key421, -1), (key236, 2), (key406, 2), (key406, 2), (key263, 1), (key263, 1), (key445, 1), (key445, 1), (key661, 1), (key661, 1), (key248, -1), (key248, -1), (key316, -1), (key316, -1), (key435, -1), (key435, -1), (key278, -2), (key488, -2), (key488, -2), (key277, 1), (key277, 1), (key346, 1), (key346, 1), (key487, 1), (key487, 1)]

def rawRow1061 : Integer.Sparse Key := [(key411, -1), (key421, -1), (key241, -1), (key421, -1), (key241, -1), (key411, -1), (key406, 2), (key236, 2), (key406, 2), (key445, 1), (key661, 1), (key263, 1), (key661, 1), (key263, 1), (key445, 1), (key316, -1), (key435, -1), (key248, -1), (key435, -1), (key248, -1), (key316, -1), (key488, -2), (key278, -2), (key488, -2), (key346, 1), (key487, 1), (key277, 1), (key487, 1), (key277, 1), (key346, 1)]

def rawRow1062 : Integer.Sparse Key := [(key421, -1), (key411, -1), (key421, -1), (key241, -1), (key411, -1), (key241, -1), (key406, 2), (key406, 2), (key236, 2), (key661, 1), (key445, 1), (key661, 1), (key263, 1), (key445, 1), (key263, 1), (key435, -1), (key316, -1), (key435, -1), (key248, -1), (key316, -1), (key248, -1), (key488, -2), (key488, -2), (key278, -2), (key487, 1), (key346, 1), (key487, 1), (key277, 1), (key346, 1), (key277, 1)]

def rawRow1063 : Integer.Sparse Key := [(key248, -1), (key253, -1), (key435, -1), (key660, -1), (key453, -1), (key662, -1), (key263, 2), (key445, 2), (key661, 2), (key236, 1), (key241, 1), (key406, 1), (key421, 1), (key657, 1), (key658, 1), (key277, -1), (key278, -1), (key346, -1), (key347, -1), (key488, -1), (key489, -1), (key241, -2), (key411, -2), (key421, -2), (key253, 1), (key263, 1), (key321, 1), (key331, 1), (key445, 1), (key453, 1)]

def rawRow1064 : Integer.Sparse Key := [(key253, -1), (key248, -1), (key660, -1), (key435, -1), (key662, -1), (key453, -1), (key263, 2), (key661, 2), (key445, 2), (key241, 1), (key236, 1), (key421, 1), (key406, 1), (key658, 1), (key657, 1), (key278, -1), (key277, -1), (key347, -1), (key346, -1), (key489, -1), (key488, -1), (key241, -2), (key421, -2), (key411, -2), (key263, 1), (key253, 1), (key331, 1), (key321, 1), (key453, 1), (key445, 1)]

def rawRow1065 : Integer.Sparse Key := [(key435, -1), (key453, -1), (key248, -1), (key662, -1), (key253, -1), (key660, -1), (key445, 2), (key263, 2), (key661, 2), (key406, 1), (key421, 1), (key236, 1), (key658, 1), (key241, 1), (key421, 1), (key346, -1), (key488, -1), (key277, -1), (key489, -1), (key278, -1), (key347, -1), (key411, -2), (key241, -2), (key421, -2), (key321, 1), (key445, 1), (key253, 1), (key453, 1), (key263, 1), (key331, 1)]

def rawRow1066 : Integer.Sparse Key := [(key453, -1), (key435, -1), (key662, -1), (key248, -1), (key660, -1), (key253, -1), (key445, 2), (key661, 2), (key263, 2), (key421, 1), (key406, 1), (key658, 1), (key236, 1), (key421, 1), (key241, 1), (key488, -1), (key346, -1), (key489, -1), (key277, -1), (key347, -1), (key278, -1), (key411, -2), (key421, -2), (key241, -2), (key445, 1), (key321, 1), (key453, 1), (key253, 1), (key331, 1), (key263, 1)]

def rawRow1067 : Integer.Sparse Key := [(key660, -1), (key662, -1), (key253, -1), (key453, -1), (key248, -1), (key435, -1), (key661, 2), (key263, 2), (key445, 2), (key657, 1), (key658, 1), (key241, 1), (key421, 1), (key236, 1), (key406, 1), (key347, -1), (key489, -1), (key278, -1), (key488, -1), (key277, -1), (key346, -1), (key421, -2), (key241, -2), (key411, -2), (key331, 1), (key453, 1), (key263, 1), (key445, 1), (key253, 1), (key321, 1)]

def rawRow1068 : Integer.Sparse Key := [(key662, -1), (key660, -1), (key453, -1), (key253, -1), (key435, -1), (key248, -1), (key661, 2), (key445, 2), (key263, 2), (key658, 1), (key657, 1), (key421, 1), (key241, 1), (key406, 1), (key236, 1), (key489, -1), (key347, -1), (key488, -1), (key278, -1), (key346, -1), (key277, -1), (key421, -2), (key411, -2), (key241, -2), (key453, 1), (key331, 1), (key445, 1), (key263, 1), (key321, 1), (key253, 1)]

def rawRow1069 : Integer.Sparse Key := [(key253, -1), (key263, -1), (key321, -1), (key445, -1), (key331, -1), (key453, -1), (key248, 2), (key316, 2), (key435, 2), (key277, 1), (key278, 1), (key346, 1), (key488, 1), (key347, 1), (key489, 1), (key236, -1), (key248, -1), (key302, -1), (key316, -1), (key385, -1), (key406, -1), (key263, -2), (key400, -2), (key445, -2), (key241, 1), (key253, 1), (key307, 1), (key321, 1), (key390, 1), (key411, 1)]

def rawRow1070 : Integer.Sparse Key := [(key263, -1), (key253, -1), (key445, -1), (key321, -1), (key453, -1), (key331, -1), (key248, 2), (key435, 2), (key316, 2), (key278, 1), (key277, 1), (key488, 1), (key346, 1), (key489, 1), (key347, 1), (key248, -1), (key236, -1), (key316, -1), (key302, -1), (key406, -1), (key385, -1), (key263, -2), (key445, -2), (key400, -2), (key253, 1), (key241, 1), (key321, 1), (key307, 1), (key411, 1), (key390, 1)]

def rawRow1071 : Integer.Sparse Key := [(key321, -1), (key331, -1), (key253, -1), (key453, -1), (key263, -1), (key445, -1), (key316, 2), (key248, 2), (key435, 2), (key346, 1), (key347, 1), (key277, 1), (key489, 1), (key278, 1), (key488, 1), (key302, -1), (key316, -1), (key236, -1), (key406, -1), (key248, -1), (key316, -1), (key400, -2), (key263, -2), (key445, -2), (key307, 1), (key390, 1), (key241, 1), (key411, 1), (key253, 1), (key321, 1)]

def rawRow1072 : Integer.Sparse Key := [(key331, -1), (key321, -1), (key453, -1), (key253, -1), (key445, -1), (key263, -1), (key316, 2), (key435, 2), (key248, 2), (key347, 1), (key346, 1), (key489, 1), (key277, 1), (key488, 1), (key278, 1), (key316, -1), (key302, -1), (key406, -1), (key236, -1), (key316, -1), (key248, -1), (key400, -2), (key445, -2), (key263, -2), (key390, 1), (key307, 1), (key411, 1), (key241, 1), (key321, 1), (key253, 1)]

def rawRow1073 : Integer.Sparse Key := [(key445, -1), (key453, -1), (key263, -1), (key331, -1), (key253, -1), (key321, -1), (key435, 2), (key248, 2), (key316, 2), (key488, 1), (key489, 1), (key278, 1), (key347, 1), (key277, 1), (key346, 1), (key385, -1), (key406, -1), (key248, -1), (key316, -1), (key236, -1), (key302, -1), (key445, -2), (key263, -2), (key400, -2), (key321, 1), (key411, 1), (key253, 1), (key390, 1), (key241, 1), (key307, 1)]

def rawRow1074 : Integer.Sparse Key := [(key453, -1), (key445, -1), (key331, -1), (key263, -1), (key321, -1), (key253, -1), (key435, 2), (key316, 2), (key248, 2), (key489, 1), (key488, 1), (key347, 1), (key278, 1), (key346, 1), (key277, 1), (key406, -1), (key385, -1), (key316, -1), (key248, -1), (key302, -1), (key236, -1), (key445, -2), (key400, -2), (key263, -2), (key411, 1), (key321, 1), (key390, 1), (key253, 1), (key307, 1), (key241, 1)]

def rawRow1075 : Integer.Sparse Key := [(key277, -1), (key277, -1), (key487, -1), (key487, -1), (key489, -1), (key489, -1), (key278, 2), (key488, 2), (key488, 2), (key241, 1), (key241, 1), (key411, 1), (key411, 1), (key421, 1), (key421, 1), (key263, -1), (key263, -1), (key400, -1), (key400, -1), (key445, -1), (key445, -1), (key236, -2), (key406, -2), (key406, -2), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

def rawRow1076 : Integer.Sparse Key := [(key487, -1), (key489, -1), (key277, -1), (key489, -1), (key277, -1), (key487, -1), (key488, 2), (key278, 2), (key488, 2), (key411, 1), (key421, 1), (key241, 1), (key421, 1), (key241, 1), (key411, 1), (key400, -1), (key445, -1), (key263, -1), (key445, -1), (key263, -1), (key400, -1), (key406, -2), (key236, -2), (key406, -2), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

def rawRow1077 : Integer.Sparse Key := [(key489, -1), (key487, -1), (key489, -1), (key277, -1), (key487, -1), (key277, -1), (key488, 2), (key488, 2), (key278, 2), (key421, 1), (key411, 1), (key421, 1), (key241, 1), (key411, 1), (key241, 1), (key445, -1), (key400, -1), (key445, -1), (key263, -1), (key400, -1), (key263, -1), (key406, -2), (key406, -2), (key236, -2), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

def rawRow1078 : Integer.Sparse Key := [(key277, -1), (key278, -1), (key346, -1), (key488, -1), (key347, -1), (key489, -1), (key277, 2), (key346, 2), (key487, 2), (key253, 1), (key263, 1), (key321, 1), (key445, 1), (key331, 1), (key453, 1), (key241, -1), (key253, -1), (key307, -1), (key390, -1), (key321, -1), (key411, -1), (key248, -2), (key316, -2), (key435, -2), (key236, 1), (key248, 1), (key302, 1), (key316, 1), (key385, 1), (key406, 1)]

def rawRow1079 : Integer.Sparse Key := [(key278, -1), (key277, -1), (key488, -1), (key346, -1), (key489, -1), (key347, -1), (key277, 2), (key487, 2), (key346, 2), (key263, 1), (key253, 1), (key445, 1), (key321, 1), (key453, 1), (key331, 1), (key253, -1), (key241, -1), (key390, -1), (key307, -1), (key411, -1), (key321, -1), (key248, -2), (key435, -2), (key316, -2), (key248, 1), (key236, 1), (key316, 1), (key302, 1), (key406, 1), (key385, 1)]

def rawRow1080 : Integer.Sparse Key := [(key346, -1), (key347, -1), (key277, -1), (key489, -1), (key278, -1), (key488, -1), (key346, 2), (key277, 2), (key487, 2), (key321, 1), (key331, 1), (key253, 1), (key453, 1), (key263, 1), (key445, 1), (key307, -1), (key321, -1), (key241, -1), (key411, -1), (key253, -1), (key390, -1), (key316, -2), (key248, -2), (key435, -2), (key302, 1), (key316, 1), (key236, 1), (key406, 1), (key248, 1), (key316, 1)]

def rawRow1081 : Integer.Sparse Key := [(key347, -1), (key346, -1), (key489, -1), (key277, -1), (key488, -1), (key278, -1), (key346, 2), (key487, 2), (key277, 2), (key331, 1), (key321, 1), (key453, 1), (key253, 1), (key445, 1), (key263, 1), (key321, -1), (key307, -1), (key411, -1), (key241, -1), (key390, -1), (key253, -1), (key316, -2), (key435, -2), (key248, -2), (key316, 1), (key302, 1), (key406, 1), (key236, 1), (key316, 1), (key248, 1)]

def rawRow1082 : Integer.Sparse Key := [(key488, -1), (key489, -1), (key278, -1), (key347, -1), (key277, -1), (key346, -1), (key487, 2), (key277, 2), (key346, 2), (key445, 1), (key453, 1), (key263, 1), (key331, 1), (key253, 1), (key321, 1), (key390, -1), (key411, -1), (key253, -1), (key321, -1), (key241, -1), (key307, -1), (key435, -2), (key248, -2), (key316, -2), (key385, 1), (key406, 1), (key248, 1), (key316, 1), (key236, 1), (key302, 1)]

def rawRow1083 : Integer.Sparse Key := [(key489, -1), (key488, -1), (key347, -1), (key278, -1), (key346, -1), (key277, -1), (key487, 2), (key346, 2), (key277, 2), (key453, 1), (key445, 1), (key331, 1), (key263, 1), (key321, 1), (key253, 1), (key411, -1), (key390, -1), (key321, -1), (key253, -1), (key307, -1), (key241, -1), (key435, -2), (key316, -2), (key248, -2), (key406, 1), (key385, 1), (key316, 1), (key248, 1), (key302, 1), (key236, 1)]

def rawRow1084 : Integer.Sparse Key := [(key2693, -2), (key3055, -2), (key3117, -2), (key3051, 1), (key3057, 1), (key3051, 1), (key3112, 1), (key3057, 1), (key3112, 1), (key3070, 2), (key3070, 2), (key3147, 2), (key3051, -1), (key3074, -1), (key3051, -1), (key3112, -1), (key3074, -1), (key3112, -1), (key3070, -1), (key3077, -1), (key3070, -1), (key3147, -1), (key3077, -1), (key3147, -1), (key3055, 1), (key3078, 1), (key3055, 1), (key3117, 1), (key3078, 1), (key3117, 1)]

def rawRow1085 : Integer.Sparse Key := [(key2693, -2), (key3117, -2), (key3055, -2), (key3057, 1), (key3051, 1), (key3112, 1), (key3051, 1), (key3112, 1), (key3057, 1), (key3070, 2), (key3147, 2), (key3070, 2), (key3074, -1), (key3051, -1), (key3112, -1), (key3051, -1), (key3112, -1), (key3074, -1), (key3077, -1), (key3070, -1), (key3147, -1), (key3070, -1), (key3147, -1), (key3077, -1), (key3078, 1), (key3055, 1), (key3117, 1), (key3055, 1), (key3117, 1), (key3078, 1)]

def rawRow1086 : Integer.Sparse Key := [(key3018, -2), (key2693, -2), (key2693, -2), (key3112, 1), (key3112, 1), (key3057, 1), (key3057, 1), (key3051, 1), (key3051, 1), (key3147, 2), (key3070, 2), (key3070, 2), (key3112, -1), (key3112, -1), (key3074, -1), (key3074, -1), (key3051, -1), (key3051, -1), (key3147, -1), (key3147, -1), (key3077, -1), (key3077, -1), (key3070, -1), (key3070, -1), (key3117, 1), (key3117, 1), (key3078, 1), (key3078, 1), (key3055, 1), (key3055, 1)]

def rawRow1087 : Integer.Sparse Key := [(key2695, -2), (key2695, -2), (key2836, -2), (key2686, 1), (key2693, 1), (key2686, 1), (key2822, 1), (key2693, 1), (key2822, 1), (key3074, 2), (key3074, 2), (key3146, 2), (key3051, -1), (key3070, -1), (key3051, -1), (key3107, -1), (key3070, -1), (key3107, -1), (key3074, -1), (key3078, -1), (key3074, -1), (key3146, -1), (key3078, -1), (key3146, -1), (key3057, 1), (key3077, 1), (key3057, 1), (key3116, 1), (key3077, 1), (key3116, 1)]

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

def rawRow1088 : Integer.Sparse Key := [(key2695, -2), (key2836, -2), (key2695, -2), (key2693, 1), (key2686, 1), (key2822, 1), (key2686, 1), (key2822, 1), (key2693, 1), (key3074, 2), (key3146, 2), (key3074, 2), (key3070, -1), (key3051, -1), (key3107, -1), (key3051, -1), (key3107, -1), (key3070, -1), (key3078, -1), (key3074, -1), (key3146, -1), (key3074, -1), (key3146, -1), (key3078, -1), (key3077, 1), (key3057, 1), (key3116, 1), (key3057, 1), (key3116, 1), (key3077, 1)]

def rawRow1089 : Integer.Sparse Key := [(key2836, -2), (key2695, -2), (key2695, -2), (key2822, 1), (key2822, 1), (key2693, 1), (key2693, 1), (key2686, 1), (key2686, 1), (key3146, 2), (key3074, 2), (key3074, 2), (key3107, -1), (key3107, -1), (key3070, -1), (key3070, -1), (key3051, -1), (key3051, -1), (key3146, -1), (key3146, -1), (key3078, -1), (key3078, -1), (key3074, -1), (key3074, -1), (key3116, 1), (key3116, 1), (key3077, 1), (key3077, 1), (key3057, 1), (key3057, 1)]

def rawRow1090 : Integer.Sparse Key := [(key2719, -2), (key2719, -2), (key3027, -2), (key2719, 1), (key2733, 1), (key2719, 1), (key3027, 1), (key2733, 1), (key3027, 1), (key2693, 2), (key3055, 2), (key3117, 2), (key3055, -1), (key3078, -1), (key3055, -1), (key3117, -1), (key3078, -1), (key3117, -1), (key3051, -1), (key3057, -1), (key3051, -1), (key3112, -1), (key3057, -1), (key3112, -1), (key3051, 1), (key3074, 1), (key3051, 1), (key3112, 1), (key3074, 1), (key3112, 1)]

def rawRow1091 : Integer.Sparse Key := [(key2719, -2), (key3027, -2), (key2719, -2), (key2733, 1), (key2719, 1), (key3027, 1), (key2719, 1), (key3027, 1), (key2733, 1), (key2693, 2), (key3117, 2), (key3055, 2), (key3078, -1), (key3055, -1), (key3117, -1), (key3055, -1), (key3117, -1), (key3078, -1), (key3057, -1), (key3051, -1), (key3112, -1), (key3051, -1), (key3112, -1), (key3057, -1), (key3074, 1), (key3051, 1), (key3112, 1), (key3051, 1), (key3112, 1), (key3074, 1)]

def rawRow1092 : Integer.Sparse Key := [(key3027, -2), (key2719, -2), (key2719, -2), (key3027, 1), (key3027, 1), (key2733, 1), (key2733, 1), (key2719, 1), (key2719, 1), (key3018, 2), (key2693, 2), (key2693, 2), (key3117, -1), (key3117, -1), (key3078, -1), (key3078, -1), (key3055, -1), (key3055, -1), (key3112, -1), (key3112, -1), (key3057, -1), (key3057, -1), (key3051, -1), (key3051, -1), (key3112, 1), (key3112, 1), (key3074, 1), (key3074, 1), (key3051, 1), (key3051, 1)]

def rawRow1093 : Integer.Sparse Key := [(key2733, -2), (key2733, -2), (key2733, -2), (key2719, 1), (key2719, 1), (key2719, 1), (key2719, 1), (key2719, 1), (key2719, 1), (key2759, 2), (key2759, 2), (key2759, 2), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3074, -1), (key3057, 1), (key3057, 1), (key3057, 1), (key3057, 1), (key3057, 1), (key3057, 1)]

def rawRow1094 : Integer.Sparse Key := [(key2756, -2), (key2756, -2), (key2924, -2), (key2756, 1), (key2759, 1), (key2756, 1), (key2924, 1), (key2759, 1), (key2924, 1), (key2695, 2), (key2695, 2), (key2836, 2), (key2695, -1), (key2733, -1), (key2695, -1), (key2836, -1), (key2733, -1), (key2836, -1), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2686, 1), (key2719, 1), (key2686, 1), (key2822, 1), (key2719, 1), (key2822, 1)]

def rawRow1095 : Integer.Sparse Key := [(key2756, -2), (key2924, -2), (key2756, -2), (key2759, 1), (key2756, 1), (key2924, 1), (key2756, 1), (key2924, 1), (key2759, 1), (key2695, 2), (key2836, 2), (key2695, 2), (key2733, -1), (key2695, -1), (key2836, -1), (key2695, -1), (key2836, -1), (key2733, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2719, 1), (key2686, 1), (key2822, 1), (key2686, 1), (key2822, 1), (key2719, 1)]

def rawRow1096 : Integer.Sparse Key := [(key2924, -2), (key2756, -2), (key2756, -2), (key2924, 1), (key2924, 1), (key2759, 1), (key2759, 1), (key2756, 1), (key2756, 1), (key2836, 2), (key2695, 2), (key2695, 2), (key2836, -1), (key2836, -1), (key2733, -1), (key2733, -1), (key2695, -1), (key2695, -1), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2822, 1), (key2822, 1), (key2719, 1), (key2719, 1), (key2686, 1), (key2686, 1)]

def rawRow1097 : Integer.Sparse Key := [(key2759, -2), (key2759, -2), (key2759, -2), (key2756, 1), (key2756, 1), (key2756, 1), (key2756, 1), (key2756, 1), (key2756, 1), (key2733, 2), (key2733, 2), (key2733, 2), (key2695, -1), (key2695, -1), (key2695, -1), (key2695, -1), (key2695, -1), (key2695, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2693, 1), (key2693, 1), (key2693, 1), (key2693, 1), (key2693, 1), (key2693, 1)]

def rawRow1098 : Integer.Sparse Key := [(key1432, -6), (key1404, 2), (key1404, 2), (key1475, 2), (key1581, 6), (key1404, -2), (key1404, -2), (key1906, -2), (key1581, -2), (key1581, -2), (key1686, -2), (key1432, 2), (key1432, 2), (key1923, 2)]

def rawRow1099 : Integer.Sparse Key := [(key1432, -6), (key1404, 2), (key1475, 2), (key1404, 2), (key1581, 6), (key1404, -2), (key1906, -2), (key1404, -2), (key1581, -2), (key1686, -2), (key1581, -2), (key1432, 2), (key1923, 2), (key1432, 2)]

def rawRow1100 : Integer.Sparse Key := [(key1432, -6), (key1475, 2), (key1404, 2), (key1404, 2), (key1581, 6), (key1906, -2), (key1404, -2), (key1404, -2), (key1686, -2), (key1581, -2), (key1581, -2), (key1923, 2), (key1432, 2), (key1432, 2)]

def rawRow1101 : Integer.Sparse Key := [(key1475, -6), (key1404, 2), (key1404, 2), (key1432, 2), (key1906, 6), (key1404, -2), (key1404, -2), (key1581, -2), (key1906, -2), (key1906, -2), (key1923, -2), (key1475, 2), (key1475, 2), (key1686, 2)]

def rawRow1102 : Integer.Sparse Key := [(key1475, -6), (key1404, 2), (key1432, 2), (key1404, 2), (key1906, 6), (key1404, -2), (key1581, -2), (key1404, -2), (key1906, -2), (key1923, -2), (key1906, -2), (key1475, 2), (key1686, 2), (key1475, 2)]

def rawRow1103 : Integer.Sparse Key := [(key1475, -6), (key1432, 2), (key1404, 2), (key1404, 2), (key1906, 6), (key1581, -2), (key1404, -2), (key1404, -2), (key1923, -2), (key1906, -2), (key1906, -2), (key1686, 2), (key1475, 2), (key1475, 2)]

def rawRow1104 : Integer.Sparse Key := [(key1581, -6), (key1581, 2), (key1581, 2), (key1686, 2), (key1432, 6), (key1432, -2), (key1432, -2), (key1923, -2), (key1404, -2), (key1404, -2), (key1475, -2), (key1404, 2), (key1404, 2), (key1906, 2)]

def rawRow1105 : Integer.Sparse Key := [(key1581, -6), (key1581, 2), (key1686, 2), (key1581, 2), (key1432, 6), (key1432, -2), (key1923, -2), (key1432, -2), (key1404, -2), (key1475, -2), (key1404, -2), (key1404, 2), (key1906, 2), (key1404, 2)]

def rawRow1106 : Integer.Sparse Key := [(key1581, -6), (key1686, 2), (key1581, 2), (key1581, 2), (key1432, 6), (key1923, -2), (key1432, -2), (key1432, -2), (key1475, -2), (key1404, -2), (key1404, -2), (key1906, 2), (key1404, 2), (key1404, 2)]

end MUB6.Certificate.GramRows

end OAI
end


