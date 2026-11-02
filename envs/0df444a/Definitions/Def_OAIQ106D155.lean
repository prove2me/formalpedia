-- Prove2me | Definitions.Def_OAIQ106D155
-- name    : OAIQ106D155
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:11:53.440211+00:00
-- url     : https://prove2.me/theorems/02b23951-55f8-45d0-845b-7b2dff12452b
-- title:
--   Definitions bundle OAIQ106D155 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 828 declarations of OpenAI's Lean: 828 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow100`, `OAI.MUB6.Certificate.GramRows.rawRow10000`, `OAI.MUB6.Certificate.GramRows.rawRow10001`, `OAI.MUB6.Certificate.GramRows.rawRow10002`, `OAI.MUB6.Certificate.GramRows.rawRow10003`, `OAI.MUB6.Certificate.GramRows.rawRow10004`, `OAI.MUB6.Certificate.GramRows.rawRow10005`, `OAI.MUB6.Certificate.GramRows.rawRow10006`, `OAI.MUB6.Certificate.GramRows.rawRow10007`, `OAI.MUB6.Certificate.GramRows.rawRow10008`, `OAI.MUB6.Certificate.GramRows.rawRow10009`, `OAI.MUB6.Certificate.GramRows.rawRow10010`, `OAI.MUB6.Certificate.GramRows.rawRow10011`, `OAI.MUB6.Certificate.GramRows.rawRow10012`, `OAI.MUB6.Certificate.GramRows.rawRow10013`, `OAI.MUB6.Certificate.GramRows.rawRow10014`, `OAI.MUB6.Certificate.GramRows.rawRow10015`, `OAI.MUB6.Certificate.GramRows.rawRow10016`, `OAI.MUB6.Certificate.GramRows.rawRow10017`, `OAI.MUB6.Certificate.GramRows.rawRow10018`, `OAI.MUB6.Certificate.GramRows.rawRow10019`, `OAI.MUB6.Certificate.GramRows.rawRow1002`, `OAI.MUB6.Certificate.GramRows.rawRow10020`, `OAI.MUB6.Certificate.GramRows.rawRow10021`, `OAI.MUB6.Certificate.GramRows.rawRow10022`, `OAI.MUB6.Certificate.GramRows.rawRow10023`, `OAI.MUB6.Certificate.GramRows.rawRow10024`, `OAI.MUB6.Certificate.GramRows.rawRow10025`, `OAI.MUB6.Certificate.GramRows.rawRow10026`, `OAI.MUB6.Certificate.GramRows.rawRow10027`, `OAI.MUB6.Certificate.GramRows.rawRow10028`, `OAI.MUB6.Certificate.GramRows.rawRow10029`, `OAI.MUB6.Certificate.GramRows.rawRow1003`, `OAI.MUB6.Certificate.GramRows.rawRow10030`, `OAI.MUB6.Certificate.GramRows.rawRow10031`, `OAI.MUB6.Certificate.GramRows.rawRow10032`, `OAI.MUB6.Certificate.GramRows.rawRow10033`, `OAI.MUB6.Certificate.GramRows.rawRow10034`, `OAI.MUB6.Certificate.GramRows.rawRow10035`, `OAI.MUB6.Certificate.GramRows.rawRow10036` and 788 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block102`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block102.lean), [`MutuallyUnbiased_GramRows_Block103`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block103.lean), [`MutuallyUnbiased_GramRows_Block104`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block104.lean), [`MutuallyUnbiased_GramRows_Block105`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block105.lean), [`MutuallyUnbiased_GramRows_Block106`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block106.lean), [`MutuallyUnbiased_GramRows_Block107`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block107.lean), [`MutuallyUnbiased_GramRows_Block108`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block108.lean), [`MutuallyUnbiased_GramRows_Block181`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block181.lean), [`MutuallyUnbiased_GramRows_Block28`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block28.lean), [`MutuallyUnbiased_GramRows_Block29`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block29.lean), [`MutuallyUnbiased_GramRows_Block30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block30.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D083`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092`, `OAIQ106D093` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval5_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval18_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow13`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow15`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow20`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D091
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D093
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

def rawRow100 : Integer.Sparse Key := [(key2739, -2), (key2749, 1), (key2751, 1), (key2675, 2), (key2730, -1), (key2751, -1), (key2672, -1), (key2675, -1), (key2707, 1), (key2739, 1), (key2952, 2), (key2962, -1), (key2964, -1), (key2620, -2), (key2833, 1), (key2964, 1), (key2617, 1), (key2620, 1), (key2810, -1), (key2833, -1), (key2730, -2), (key2985, 1), (key2994, 1), (key2643, 2), (key2978, -1), (key2994, -1), (key2633, -1), (key2643, -1), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2906, -1), (key2915, -1), (key2655, -1), (key2656, -1), (key2899, 1), (key2915, 1), (key2650, 1), (key2656, 1), (key2739, -1), (key2751, -1)]

def rawRow101 : Integer.Sparse Key := [(key2739, -2), (key2751, 1), (key2749, 1), (key2675, 2), (key2751, -1), (key2730, -1), (key2675, -1), (key2672, -1), (key2739, 1), (key2707, 1), (key2952, 2), (key2964, -1), (key2962, -1), (key2620, -2), (key2964, 1), (key2833, 1), (key2620, 1), (key2617, 1), (key2833, -1), (key2810, -1), (key2730, -2), (key2994, 1), (key2985, 1), (key2643, 2), (key2994, -1), (key2978, -1), (key2643, -1), (key2633, -1), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2915, -1), (key2906, -1), (key2656, -1), (key2655, -1), (key2915, 1), (key2899, 1), (key2656, 1), (key2650, 1), (key2751, -1), (key2739, -1)]

def rawRow102 : Integer.Sparse Key := [(key2749, -2), (key2739, 1), (key2751, 1), (key2730, 2), (key2675, -1), (key2751, -1), (key2707, -1), (key2730, -1), (key2672, 1), (key2749, 1), (key2962, 2), (key2952, -1), (key2964, -1), (key2833, -2), (key2620, 1), (key2964, 1), (key2810, 1), (key2833, 1), (key2617, -1), (key2962, -1), (key2985, -2), (key2730, 1), (key2994, 1), (key2978, 2), (key2643, -1), (key2994, -1), (key2707, -1), (key2978, -1), (key2633, 1), (key2985, 1), (key2906, 1), (key3001, 1), (key2749, -1), (key3004, -1), (key2899, -1), (key2999, -1), (key2655, 1), (key3004, 1), (key2739, 1), (key2999, 1), (key2650, -1), (key3001, -1)]

def rawRow103 : Integer.Sparse Key := [(key2749, -2), (key2751, 1), (key2739, 1), (key2730, 2), (key2751, -1), (key2675, -1), (key2730, -1), (key2707, -1), (key2749, 1), (key2672, 1), (key2962, 2), (key2964, -1), (key2952, -1), (key2833, -2), (key2964, 1), (key2620, 1), (key2833, 1), (key2810, 1), (key2962, -1), (key2617, -1), (key2985, -2), (key2994, 1), (key2730, 1), (key2978, 2), (key2994, -1), (key2643, -1), (key2978, -1), (key2707, -1), (key2985, 1), (key2633, 1), (key3001, 1), (key2906, 1), (key3004, -1), (key2749, -1), (key2999, -1), (key2899, -1), (key3004, 1), (key2655, 1), (key2999, 1), (key2739, 1), (key3001, -1), (key2650, -1)]

def rawRow105 : Integer.Sparse Key := [(key2797, -2), (key2787, 1), (key2797, 1), (key2899, 2), (key2810, -1), (key2899, -1), (key2906, -1), (key2915, -1), (key2833, 1), (key2915, 1), (key2643, 2), (key2633, -1), (key2643, -1), (key2978, -2), (key2707, 1), (key2978, 1), (key2985, 1), (key2994, 1), (key2730, -1), (key2994, -1), (key2655, -2), (key2617, 1), (key2655, 1), (key2749, 2), (key2672, -1), (key2749, -1), (key2962, -1), (key3004, -1), (key2945, 1), (key3004, 1), (key2643, 1), (key2656, 1), (key2620, -1), (key2656, -1), (key2730, -1), (key2751, -1), (key2675, 1), (key2751, 1), (key2833, 1), (key2915, 1), (key2797, -1), (key2915, -1)]

def rawRow106 : Integer.Sparse Key := [(key2797, -2), (key2797, 1), (key2787, 1), (key2899, 2), (key2899, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, 1), (key2833, 1), (key2643, 2), (key2643, -1), (key2633, -1), (key2978, -2), (key2978, 1), (key2707, 1), (key2994, 1), (key2985, 1), (key2994, -1), (key2730, -1), (key2655, -2), (key2655, 1), (key2617, 1), (key2749, 2), (key2749, -1), (key2672, -1), (key3004, -1), (key2962, -1), (key3004, 1), (key2945, 1), (key2656, 1), (key2643, 1), (key2656, -1), (key2620, -1), (key2751, -1), (key2730, -1), (key2751, 1), (key2675, 1), (key2915, 1), (key2833, 1), (key2915, -1), (key2797, -1)]

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

end MUB6.Certificate.GramRows

end OAI
end


