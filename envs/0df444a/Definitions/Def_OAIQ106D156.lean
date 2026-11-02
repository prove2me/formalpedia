-- Prove2me | Definitions.Def_OAIQ106D156
-- name    : OAIQ106D156
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:05:48.582195+00:00
-- url     : https://prove2.me/theorems/79608dcf-2645-45c5-b346-c14e33509369
-- title:
--   Definitions bundle OAIQ106D156 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 958 declarations of OpenAI's Lean: 958 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow1078`, `OAI.MUB6.Certificate.GramRows.rawRow10781`, `OAI.MUB6.Certificate.GramRows.rawRow10782`, `OAI.MUB6.Certificate.GramRows.rawRow10783`, `OAI.MUB6.Certificate.GramRows.rawRow10784`, `OAI.MUB6.Certificate.GramRows.rawRow10785`, `OAI.MUB6.Certificate.GramRows.rawRow10786`, `OAI.MUB6.Certificate.GramRows.rawRow10787`, `OAI.MUB6.Certificate.GramRows.rawRow10788`, `OAI.MUB6.Certificate.GramRows.rawRow10789`, `OAI.MUB6.Certificate.GramRows.rawRow1079`, `OAI.MUB6.Certificate.GramRows.rawRow10790`, `OAI.MUB6.Certificate.GramRows.rawRow10791`, `OAI.MUB6.Certificate.GramRows.rawRow10792`, `OAI.MUB6.Certificate.GramRows.rawRow10793`, `OAI.MUB6.Certificate.GramRows.rawRow10794`, `OAI.MUB6.Certificate.GramRows.rawRow10795`, `OAI.MUB6.Certificate.GramRows.rawRow10796`, `OAI.MUB6.Certificate.GramRows.rawRow10797`, `OAI.MUB6.Certificate.GramRows.rawRow10798`, `OAI.MUB6.Certificate.GramRows.rawRow10799`, `OAI.MUB6.Certificate.GramRows.rawRow108`, `OAI.MUB6.Certificate.GramRows.rawRow1080`, `OAI.MUB6.Certificate.GramRows.rawRow10800`, `OAI.MUB6.Certificate.GramRows.rawRow10801`, `OAI.MUB6.Certificate.GramRows.rawRow10802`, `OAI.MUB6.Certificate.GramRows.rawRow10803`, `OAI.MUB6.Certificate.GramRows.rawRow10804`, `OAI.MUB6.Certificate.GramRows.rawRow10805`, `OAI.MUB6.Certificate.GramRows.rawRow10806`, `OAI.MUB6.Certificate.GramRows.rawRow10807`, `OAI.MUB6.Certificate.GramRows.rawRow10808`, `OAI.MUB6.Certificate.GramRows.rawRow10809`, `OAI.MUB6.Certificate.GramRows.rawRow1081`, `OAI.MUB6.Certificate.GramRows.rawRow10810`, `OAI.MUB6.Certificate.GramRows.rawRow10811`, `OAI.MUB6.Certificate.GramRows.rawRow10812`, `OAI.MUB6.Certificate.GramRows.rawRow10813`, `OAI.MUB6.Certificate.GramRows.rawRow10814`, `OAI.MUB6.Certificate.GramRows.rawRow10815` and 918 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block108`, `MutuallyUnbiased_GramRows_Block109`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block111`, `MutuallyUnbiased_GramRows_Block112`, `MutuallyUnbiased_GramRows_Block113`, `MutuallyUnbiased_GramRows_Block114`, `MutuallyUnbiased_GramRows_Block115`, `MutuallyUnbiased_GramRows_Block116`, `MutuallyUnbiased_GramRows_Block117`, `MutuallyUnbiased_GramRows_Block118`, `MutuallyUnbiased_GramRows_Block30`, `MutuallyUnbiased_GramRows_Block31`, `MutuallyUnbiased_GramRows_Block32`, `MutuallyUnbiased_GramRows_Block33`.
--
--   **Imports.** It imports the bundles `OAIQ106D073`, `OAIQ106D076`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D091` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D073
import Definitions.Def_OAIQ106D076
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D088
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
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

def rawRow11 : Integer.Sparse Key := [(key305, -1), (key302, -1), (key305, 2), (key319, 1), (key316, 1), (key335, -1), (key319, -1), (key328, -2), (key340, 1), (key328, 1), (key239, 1), (key236, 1), (key239, -2), (key409, -1), (key406, -1), (key418, 1), (key409, 1), (key578, 2), (key583, -1), (key578, -1), (key251, -1), (key248, -1), (key260, 1), (key251, 1), (key319, 1), (key316, 1), (key328, -1), (key319, -1), (key595, -1), (key593, -1), (key601, 1), (key593, 1), (key267, 2), (key271, -1), (key267, -1), (key335, -2), (key340, 1), (key335, 1), (key469, 1), (key467, 1), (key475, -1), (key467, -1)]

def rawRow108 : Integer.Sparse Key := [(key2833, -2), (key2810, 1), (key2833, 1), (key2906, 2), (key2787, -1), (key2906, -1), (key2899, -1), (key2915, -1), (key2797, 1), (key2915, 1), (key2730, 2), (key2707, -1), (key2730, -1), (key2985, -2), (key2633, 1), (key2985, 1), (key2978, 1), (key2994, 1), (key2643, -1), (key2994, -1), (key2749, -2), (key2672, 1), (key2749, 1), (key2962, 2), (key2617, -1), (key2962, -1), (key2749, -1), (key3004, -1), (key2655, 1), (key3004, 1), (key2797, 1), (key2946, 1), (key2675, -1), (key2946, -1), (key2833, -1), (key2964, -1), (key2620, 1), (key2964, 1), (key2730, 1), (key2994, 1), (key2643, -1), (key2994, -1)]

def rawRow109 : Integer.Sparse Key := [(key2833, -2), (key2833, 1), (key2810, 1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2899, -1), (key2915, 1), (key2797, 1), (key2730, 2), (key2730, -1), (key2707, -1), (key2985, -2), (key2985, 1), (key2633, 1), (key2994, 1), (key2978, 1), (key2994, -1), (key2643, -1), (key2749, -2), (key2749, 1), (key2672, 1), (key2962, 2), (key2962, -1), (key2617, -1), (key3004, -1), (key2749, -1), (key3004, 1), (key2655, 1), (key2946, 1), (key2797, 1), (key2946, -1), (key2675, -1), (key2964, -1), (key2833, -1), (key2964, 1), (key2620, 1), (key2994, 1), (key2730, 1), (key2994, -1), (key2643, -1)]

def rawRow110 : Integer.Sparse Key := [(key2899, -2), (key2906, 1), (key2915, 1), (key2797, 2), (key2833, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, 1), (key2899, 1), (key2978, 2), (key2985, -1), (key2994, -1), (key2643, -2), (key2730, 1), (key2994, 1), (key2633, 1), (key2643, 1), (key2707, -1), (key2978, -1), (key2945, -2), (key2962, 1), (key3004, 1), (key2655, 2), (key2749, -1), (key3004, -1), (key2617, -1), (key2655, -1), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2833, -1), (key2915, -1), (key2643, -1), (key2656, -1), (key2797, 1), (key2915, 1), (key2620, 1), (key2656, 1), (key2675, -1), (key2751, -1)]

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

def rawRow11054 : Integer.Sparse Key := [(key1308, -6), (key1416, -6), (key1614, -6), (key1810, -6), (key1288, 2), (key1308, 2), (key1334, 2), (key1383, 2), (key1538, 2), (key1769, 2), (key1416, 2), (key1452, 2), (key1565, 2), (key1785, 2), (key1652, 2), (key1810, 2)]

def rawRow11055 : Integer.Sparse Key := [(key1308, -6), (key1416, -6), (key1810, -6), (key1614, -6), (key1288, 2), (key1334, 2), (key1308, 2), (key1383, 2), (key1769, 2), (key1538, 2), (key1452, 2), (key1416, 2), (key1785, 2), (key1565, 2), (key1810, 2), (key1652, 2)]

def rawRow11056 : Integer.Sparse Key := [(key1308, -6), (key1614, -6), (key1416, -6), (key1810, -6), (key1308, 2), (key1288, 2), (key1334, 2), (key1538, 2), (key1383, 2), (key1769, 2), (key1565, 2), (key1652, 2), (key1416, 2), (key1810, 2), (key1452, 2), (key1785, 2)]

def rawRow11057 : Integer.Sparse Key := [(key1308, -6), (key1614, -6), (key1810, -6), (key1416, -6), (key1308, 2), (key1334, 2), (key1288, 2), (key1538, 2), (key1769, 2), (key1383, 2), (key1652, 2), (key1565, 2), (key1810, 2), (key1416, 2), (key1785, 2), (key1452, 2)]

def rawRow11058 : Integer.Sparse Key := [(key1308, -6), (key1810, -6), (key1416, -6), (key1614, -6), (key1334, 2), (key1288, 2), (key1308, 2), (key1769, 2), (key1383, 2), (key1538, 2), (key1785, 2), (key1810, 2), (key1452, 2), (key1652, 2), (key1416, 2), (key1565, 2)]

def rawRow11059 : Integer.Sparse Key := [(key1308, -6), (key1810, -6), (key1614, -6), (key1416, -6), (key1334, 2), (key1308, 2), (key1288, 2), (key1769, 2), (key1538, 2), (key1383, 2), (key1810, 2), (key1785, 2), (key1652, 2), (key1452, 2), (key1565, 2), (key1416, 2)]

def rawRow11060 : Integer.Sparse Key := [(key1416, -6), (key1308, -6), (key1614, -6), (key1810, -6), (key1383, 2), (key1416, 2), (key1452, 2), (key1288, 2), (key1565, 2), (key1785, 2), (key1308, 2), (key1334, 2), (key1538, 2), (key1769, 2), (key1652, 2), (key1810, 2)]

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

end MUB6.Certificate.GramRows

end OAI
end


