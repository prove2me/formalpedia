-- Prove2me | Definitions.Def_OAIQ106D176
-- name    : OAIQ106D176
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:41:02.429221+00:00
-- url     : https://prove2.me/theorems/9cf1dbe0-c18e-4fd0-897b-10bc91a5d922
-- title:
--   Definitions bundle OAIQ106D176 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 136 declarations of OpenAI's Lean: 136 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow6307`, `OAI.MUB6.Certificate.GramRows.rawRow6308`, `OAI.MUB6.Certificate.GramRows.rawRow6309`, `OAI.MUB6.Certificate.GramRows.rawRow6310`, `OAI.MUB6.Certificate.GramRows.rawRow6311`, `OAI.MUB6.Certificate.GramRows.rawRow6312`, `OAI.MUB6.Certificate.GramRows.rawRow6313`, `OAI.MUB6.Certificate.GramRows.rawRow6314`, `OAI.MUB6.Certificate.GramRows.rawRow6315`, `OAI.MUB6.Certificate.GramRows.rawRow6316`, `OAI.MUB6.Certificate.GramRows.rawRow6317`, `OAI.MUB6.Certificate.GramRows.rawRow634`, `OAI.MUB6.Certificate.GramRows.rawRow635`, `OAI.MUB6.Certificate.GramRows.rawRow636`, `OAI.MUB6.Certificate.GramRows.rawRow637`, `OAI.MUB6.Certificate.GramRows.rawRow638`, `OAI.MUB6.Certificate.GramRows.rawRow6398`, `OAI.MUB6.Certificate.GramRows.rawRow6399`, `OAI.MUB6.Certificate.GramRows.rawRow64`, `OAI.MUB6.Certificate.GramRows.rawRow6400`, `OAI.MUB6.Certificate.GramRows.rawRow6401`, `OAI.MUB6.Certificate.GramRows.rawRow6402`, `OAI.MUB6.Certificate.GramRows.rawRow6403`, `OAI.MUB6.Certificate.GramRows.rawRow6404`, `OAI.MUB6.Certificate.GramRows.rawRow6405`, `OAI.MUB6.Certificate.GramRows.rawRow6406`, `OAI.MUB6.Certificate.GramRows.rawRow6407`, `OAI.MUB6.Certificate.GramRows.rawRow6408`, `OAI.MUB6.Certificate.GramRows.rawRow6409`, `OAI.MUB6.Certificate.GramRows.rawRow6410`, `OAI.MUB6.Certificate.GramRows.rawRow6411`, `OAI.MUB6.Certificate.GramRows.rawRow6412`, `OAI.MUB6.Certificate.GramRows.rawRow6413`, `OAI.MUB6.Certificate.GramRows.rawRow6414`, `OAI.MUB6.Certificate.GramRows.rawRow6415`, `OAI.MUB6.Certificate.GramRows.rawRow6416`, `OAI.MUB6.Certificate.GramRows.rawRow6417`, `OAI.MUB6.Certificate.GramRows.rawRow6418`, `OAI.MUB6.Certificate.GramRows.rawRow6419`, `OAI.MUB6.Certificate.GramRows.rawRow642` and 96 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block16.lean), [`MutuallyUnbiased_GramRows_Block17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block17.lean), [`MutuallyUnbiased_GramRows_Block18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block18.lean), [`MutuallyUnbiased_GramRows_Block73`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block73.lean), [`MutuallyUnbiased_GramRows_Block74`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block74.lean), [`MutuallyUnbiased_GramRows_Block75`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block75.lean), [`MutuallyUnbiased_TaoCertificate_Merge45`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge45.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D089`, `OAIQ106D090` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D140

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow64 : Integer.Sparse Key := [(key1559, -1), (key1546, -1), (key1546, 2), (key1659, 1), (key1655, 1), (key1655, -1), (key1573, -1), (key1667, -2), (key1667, 1), (key1596, 1), (key1329, 1), (key1316, 1), (key1316, -2), (key1817, -1), (key1813, -1), (key1813, 1), (key1424, 1), (key1825, 2), (key1825, -1), (key1447, -1), (key1345, -1), (key1337, -1), (key1337, 1), (key1296, 1), (key1780, 1), (key1772, 1), (key1772, -1), (key1391, -1), (key1844, -1), (key1798, -1), (key1844, 1), (key1466, 1), (key1339, 2), (key1339, -1), (key1302, -1), (key1774, -2), (key1774, 1), (key1397, 1), (key1839, 1), (key1790, 1), (key1839, -1), (key1457, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow634 : Integer.Sparse Key := [(key2620, -2), (key2964, -2), (key2833, -2), (key2620, 1), (key2617, 1), (key2833, 1), (key2810, 1), (key2962, 1), (key2952, 1), (key2643, 2), (key2994, 2), (key2978, 2), (key2643, -1), (key2633, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2978, -1), (key2656, -1), (key2655, -1), (key2915, -1), (key2899, -1), (key3004, -1), (key2999, -1), (key2656, 1), (key2650, 1), (key2751, 1), (key2739, 1), (key3001, 1), (key2999, 1)]

def rawRow635 : Integer.Sparse Key := [(key2833, -2), (key2620, -2), (key2964, -2), (key2810, 1), (key2833, 1), (key2617, 1), (key2962, 1), (key2620, 1), (key2833, 1), (key2978, 2), (key2643, 2), (key2994, 2), (key2707, -1), (key2978, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2899, -1), (key2999, -1), (key2655, -1), (key3004, -1), (key2656, -1), (key2915, -1), (key2739, 1), (key2999, 1), (key2650, 1), (key3001, 1), (key2656, 1), (key2751, 1)]

def rawRow636 : Integer.Sparse Key := [(key2833, -2), (key2964, -2), (key2620, -2), (key2833, 1), (key2810, 1), (key2962, 1), (key2617, 1), (key2833, 1), (key2620, 1), (key2978, 2), (key2994, 2), (key2643, 2), (key2978, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2730, -1), (key2643, -1), (key2999, -1), (key2899, -1), (key3004, -1), (key2655, -1), (key2915, -1), (key2656, -1), (key2999, 1), (key2739, 1), (key3001, 1), (key2650, 1), (key2751, 1), (key2656, 1)]

def rawRow637 : Integer.Sparse Key := [(key2964, -2), (key2620, -2), (key2833, -2), (key2952, 1), (key2962, 1), (key2620, 1), (key2833, 1), (key2617, 1), (key2810, 1), (key2994, 2), (key2643, 2), (key2978, 2), (key2730, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2633, -1), (key2707, -1), (key2915, -1), (key3004, -1), (key2656, -1), (key2999, -1), (key2655, -1), (key2899, -1), (key2751, 1), (key3001, 1), (key2656, 1), (key2999, 1), (key2650, 1), (key2739, 1)]

def rawRow638 : Integer.Sparse Key := [(key2964, -2), (key2833, -2), (key2620, -2), (key2962, 1), (key2952, 1), (key2833, 1), (key2620, 1), (key2810, 1), (key2617, 1), (key2994, 2), (key2978, 2), (key2643, 2), (key2985, -1), (key2730, -1), (key2978, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key3004, -1), (key2915, -1), (key2999, -1), (key2656, -1), (key2899, -1), (key2655, -1), (key3001, 1), (key2751, 1), (key2999, 1), (key2656, 1), (key2739, 1), (key2650, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow642 : Integer.Sparse Key := [(key2643, -2), (key2730, -2), (key2994, -2), (key2633, 1), (key2643, 1), (key2707, 1), (key2978, 1), (key2730, 1), (key2985, 1), (key2655, 2), (key2749, 2), (key3004, 2), (key2617, -1), (key2655, -1), (key2672, -1), (key2749, -1), (key2945, -1), (key2962, -1), (key2643, -1), (key2656, -1), (key2797, -1), (key2915, -1), (key2946, -1), (key2994, -1), (key2620, 1), (key2656, 1), (key2675, 1), (key2751, 1), (key2946, 1), (key2964, 1)]

def rawRow643 : Integer.Sparse Key := [(key2643, -2), (key2994, -2), (key2730, -2), (key2643, 1), (key2633, 1), (key2978, 1), (key2707, 1), (key2985, 1), (key2730, 1), (key2655, 2), (key3004, 2), (key2749, 2), (key2655, -1), (key2617, -1), (key2749, -1), (key2672, -1), (key2962, -1), (key2945, -1), (key2656, -1), (key2643, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2946, -1), (key2656, 1), (key2620, 1), (key2751, 1), (key2675, 1), (key2964, 1), (key2946, 1)]

def rawRow644 : Integer.Sparse Key := [(key2730, -2), (key2643, -2), (key2994, -2), (key2707, 1), (key2730, 1), (key2633, 1), (key2985, 1), (key2643, 1), (key2978, 1), (key2749, 2), (key2655, 2), (key3004, 2), (key2672, -1), (key2749, -1), (key2617, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2797, -1), (key2946, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2675, 1), (key2946, 1), (key2620, 1), (key2964, 1), (key2656, 1), (key2751, 1)]

def rawRow645 : Integer.Sparse Key := [(key2730, -2), (key2994, -2), (key2643, -2), (key2730, 1), (key2707, 1), (key2985, 1), (key2633, 1), (key2978, 1), (key2643, 1), (key2749, 2), (key3004, 2), (key2655, 2), (key2749, -1), (key2672, -1), (key2962, -1), (key2617, -1), (key2749, -1), (key2655, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2915, -1), (key2656, -1), (key2946, 1), (key2675, 1), (key2964, 1), (key2620, 1), (key2751, 1), (key2656, 1)]

def rawRow646 : Integer.Sparse Key := [(key2994, -2), (key2643, -2), (key2730, -2), (key2978, 1), (key2985, 1), (key2643, 1), (key2730, 1), (key2633, 1), (key2707, 1), (key3004, 2), (key2655, 2), (key2749, 2), (key2945, -1), (key2962, -1), (key2655, -1), (key2749, -1), (key2617, -1), (key2672, -1), (key2915, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2643, -1), (key2797, -1), (key2751, 1), (key2964, 1), (key2656, 1), (key2946, 1), (key2620, 1), (key2675, 1)]

def rawRow647 : Integer.Sparse Key := [(key2994, -2), (key2730, -2), (key2643, -2), (key2985, 1), (key2978, 1), (key2730, 1), (key2643, 1), (key2707, 1), (key2633, 1), (key3004, 2), (key2749, 2), (key2655, 2), (key2962, -1), (key2945, -1), (key2749, -1), (key2655, -1), (key2672, -1), (key2617, -1), (key2994, -1), (key2915, -1), (key2946, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2964, 1), (key2751, 1), (key2946, 1), (key2656, 1), (key2675, 1), (key2620, 1)]

def rawRow648 : Integer.Sparse Key := [(key2650, -2), (key2906, -2), (key3001, -2), (key2655, 1), (key2656, 1), (key2899, 1), (key2999, 1), (key2915, 1), (key3004, 1), (key2620, 2), (key2833, 2), (key2964, 2), (key2643, -1), (key2656, -1), (key2797, -1), (key2946, -1), (key2915, -1), (key2994, -1), (key2617, -1), (key2620, -1), (key2810, -1), (key2833, -1), (key2952, -1), (key2962, -1), (key2633, 1), (key2643, 1), (key2707, 1), (key2730, 1), (key2978, 1), (key2985, 1)]

def rawRow649 : Integer.Sparse Key := [(key2650, -2), (key3001, -2), (key2906, -2), (key2656, 1), (key2655, 1), (key2999, 1), (key2899, 1), (key3004, 1), (key2915, 1), (key2620, 2), (key2964, 2), (key2833, 2), (key2656, -1), (key2643, -1), (key2946, -1), (key2797, -1), (key2994, -1), (key2915, -1), (key2620, -1), (key2617, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2952, -1), (key2643, 1), (key2633, 1), (key2730, 1), (key2707, 1), (key2985, 1), (key2978, 1)]

def rawRow650 : Integer.Sparse Key := [(key2906, -2), (key2650, -2), (key3001, -2), (key2899, 1), (key2915, 1), (key2655, 1), (key3004, 1), (key2656, 1), (key2999, 1), (key2833, 2), (key2620, 2), (key2964, 2), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, -1), (key2946, -1), (key2810, -1), (key2833, -1), (key2617, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2707, 1), (key2978, 1), (key2633, 1), (key2985, 1), (key2643, 1), (key2730, 1)]

def rawRow651 : Integer.Sparse Key := [(key2906, -2), (key3001, -2), (key2650, -2), (key2915, 1), (key2899, 1), (key3004, 1), (key2655, 1), (key2999, 1), (key2656, 1), (key2833, 2), (key2964, 2), (key2620, 2), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, -1), (key2656, -1), (key2833, -1), (key2810, -1), (key2962, -1), (key2617, -1), (key2833, -1), (key2620, -1), (key2978, 1), (key2707, 1), (key2985, 1), (key2633, 1), (key2730, 1), (key2643, 1)]

def rawRow652 : Integer.Sparse Key := [(key3001, -2), (key2650, -2), (key2906, -2), (key2999, 1), (key3004, 1), (key2656, 1), (key2915, 1), (key2655, 1), (key2899, 1), (key2964, 2), (key2620, 2), (key2833, 2), (key2946, -1), (key2994, -1), (key2656, -1), (key2915, -1), (key2643, -1), (key2797, -1), (key2952, -1), (key2962, -1), (key2620, -1), (key2833, -1), (key2617, -1), (key2810, -1), (key2730, 1), (key2985, 1), (key2643, 1), (key2978, 1), (key2633, 1), (key2707, 1)]

def rawRow653 : Integer.Sparse Key := [(key3001, -2), (key2906, -2), (key2650, -2), (key3004, 1), (key2999, 1), (key2915, 1), (key2656, 1), (key2899, 1), (key2655, 1), (key2964, 2), (key2833, 2), (key2620, 2), (key2994, -1), (key2946, -1), (key2915, -1), (key2656, -1), (key2797, -1), (key2643, -1), (key2962, -1), (key2952, -1), (key2833, -1), (key2620, -1), (key2810, -1), (key2617, -1), (key2985, 1), (key2730, 1), (key2978, 1), (key2643, 1), (key2707, 1), (key2633, 1)]

def rawRow654 : Integer.Sparse Key := [(key2655, -2), (key2749, -2), (key3004, -2), (key2650, 1), (key2656, 1), (key2739, 1), (key2999, 1), (key2751, 1), (key3001, 1), (key2643, 2), (key2730, 2), (key2994, 2), (key2620, -1), (key2656, -1), (key2675, -1), (key2946, -1), (key2751, -1), (key2964, -1), (key2633, -1), (key2643, -1), (key2707, -1), (key2978, -1), (key2730, -1), (key2985, -1), (key2617, 1), (key2655, 1), (key2672, 1), (key2749, 1), (key2945, 1), (key2962, 1)]

def rawRow655 : Integer.Sparse Key := [(key2655, -2), (key3004, -2), (key2749, -2), (key2656, 1), (key2650, 1), (key2999, 1), (key2739, 1), (key3001, 1), (key2751, 1), (key2643, 2), (key2994, 2), (key2730, 2), (key2656, -1), (key2620, -1), (key2946, -1), (key2675, -1), (key2964, -1), (key2751, -1), (key2643, -1), (key2633, -1), (key2978, -1), (key2707, -1), (key2985, -1), (key2730, -1), (key2655, 1), (key2617, 1), (key2749, 1), (key2672, 1), (key2962, 1), (key2945, 1)]

def rawRow656 : Integer.Sparse Key := [(key2749, -2), (key2655, -2), (key3004, -2), (key2739, 1), (key2751, 1), (key2650, 1), (key3001, 1), (key2656, 1), (key2999, 1), (key2730, 2), (key2643, 2), (key2994, 2), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, -1), (key2946, -1), (key2707, -1), (key2730, -1), (key2633, -1), (key2985, -1), (key2643, -1), (key2978, -1), (key2672, 1), (key2749, 1), (key2617, 1), (key2962, 1), (key2655, 1), (key2749, 1)]

def rawRow657 : Integer.Sparse Key := [(key2749, -2), (key3004, -2), (key2655, -2), (key2751, 1), (key2739, 1), (key3001, 1), (key2650, 1), (key2999, 1), (key2656, 1), (key2730, 2), (key2994, 2), (key2643, 2), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, -1), (key2656, -1), (key2730, -1), (key2707, -1), (key2985, -1), (key2633, -1), (key2978, -1), (key2643, -1), (key2749, 1), (key2672, 1), (key2962, 1), (key2617, 1), (key2749, 1), (key2655, 1)]

def rawRow658 : Integer.Sparse Key := [(key3004, -2), (key2655, -2), (key2749, -2), (key2999, 1), (key3001, 1), (key2656, 1), (key2751, 1), (key2650, 1), (key2739, 1), (key2994, 2), (key2643, 2), (key2730, 2), (key2946, -1), (key2964, -1), (key2656, -1), (key2751, -1), (key2620, -1), (key2675, -1), (key2978, -1), (key2985, -1), (key2643, -1), (key2730, -1), (key2633, -1), (key2707, -1), (key2945, 1), (key2962, 1), (key2655, 1), (key2749, 1), (key2617, 1), (key2672, 1)]

def rawRow659 : Integer.Sparse Key := [(key3004, -2), (key2749, -2), (key2655, -2), (key3001, 1), (key2999, 1), (key2751, 1), (key2656, 1), (key2739, 1), (key2650, 1), (key2994, 2), (key2730, 2), (key2643, 2), (key2964, -1), (key2946, -1), (key2751, -1), (key2656, -1), (key2675, -1), (key2620, -1), (key2985, -1), (key2978, -1), (key2730, -1), (key2643, -1), (key2707, -1), (key2633, -1), (key2962, 1), (key2945, 1), (key2749, 1), (key2655, 1), (key2672, 1), (key2617, 1)]

def rawRow661 : Integer.Sparse Key := [(key1389, -2), (key1453, -2), (key1453, -2), (key1389, 1), (key1389, 1), (key1422, 1), (key1422, 1), (key1453, 1), (key1453, 1), (key1544, 2), (key1653, 2), (key1653, 2), (key1544, -1), (key1544, -1), (key1571, -1), (key1571, -1), (key1653, -1), (key1653, -1), (key1770, -1), (key1770, -1), (key1811, -1), (key1811, -1), (key1838, -1), (key1838, -1), (key1770, 1), (key1770, 1), (key1786, 1), (key1786, 1), (key1838, 1), (key1838, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow675 : Integer.Sparse Key := [(key246, -6), (key234, 2), (key246, 2), (key246, 2), (key314, 6), (key300, -2), (key314, -2), (key314, -2), (key404, -2), (key433, -2), (key433, -2), (key383, 2), (key433, 2), (key433, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6307 : Integer.Sparse Key := [(key1236, -4), (key1233, 2), (key1236, 2), (key1243, 2), (key1247, 2), (key1243, -4), (key1022, 2), (key1009, -1), (key1022, -1), (key1130, 2), (key1044, -1), (key1130, -1), (key1159, -1), (key1174, -1), (key1080, -1), (key1174, -1), (key1080, 2), (key1159, 2), (key1003, -1), (key1017, -1), (key1003, 2), (key1116, -1), (key1125, -1), (key1038, 2), (key1125, 2), (key1038, -1), (key1116, -1), (key1152, 2), (key1073, -1), (key1152, -1)]

def rawRow6308 : Integer.Sparse Key := [(key1236, -4), (key1236, 2), (key1233, 2), (key1247, 2), (key1243, 2), (key1243, -4), (key1022, 2), (key1022, -1), (key1009, -1), (key1130, 2), (key1130, -1), (key1044, -1), (key1174, -1), (key1159, -1), (key1174, -1), (key1080, -1), (key1159, 2), (key1080, 2), (key1017, -1), (key1003, -1), (key1003, 2), (key1125, -1), (key1116, -1), (key1125, 2), (key1038, 2), (key1116, -1), (key1038, -1), (key1152, 2), (key1152, -1), (key1073, -1)]

def rawRow6309 : Integer.Sparse Key := [(key1233, -4), (key1243, 2), (key1243, 2), (key1236, 2), (key1236, 2), (key1247, -4), (key1044, 2), (key1080, -1), (key1080, -1), (key1009, 2), (key1159, -1), (key1159, -1), (key1022, -1), (key1022, -1), (key1130, -1), (key1130, -1), (key1174, 2), (key1174, 2), (key1038, -1), (key1038, -1), (key1073, 2), (key1003, -1), (key1003, -1), (key1116, 2), (key1116, 2), (key1152, -1), (key1152, -1), (key1017, 2), (key1125, -1), (key1125, -1)]

def rawRow6310 : Integer.Sparse Key := [(key1243, -4), (key1233, 2), (key1243, 2), (key1236, 2), (key1247, 2), (key1236, -4), (key1080, 2), (key1044, -1), (key1080, -1), (key1159, 2), (key1009, -1), (key1159, -1), (key1130, -1), (key1174, -1), (key1022, -1), (key1174, -1), (key1022, 2), (key1130, 2), (key1038, -1), (key1073, -1), (key1038, 2), (key1116, -1), (key1152, -1), (key1003, 2), (key1152, 2), (key1003, -1), (key1116, -1), (key1125, 2), (key1017, -1), (key1125, -1)]

def rawRow6311 : Integer.Sparse Key := [(key1243, -4), (key1243, 2), (key1233, 2), (key1247, 2), (key1236, 2), (key1236, -4), (key1080, 2), (key1080, -1), (key1044, -1), (key1159, 2), (key1159, -1), (key1009, -1), (key1174, -1), (key1130, -1), (key1174, -1), (key1022, -1), (key1130, 2), (key1022, 2), (key1073, -1), (key1038, -1), (key1038, 2), (key1152, -1), (key1116, -1), (key1152, 2), (key1003, 2), (key1116, -1), (key1003, -1), (key1125, 2), (key1125, -1), (key1017, -1)]

def rawRow6312 : Integer.Sparse Key := [(key1236, -4), (key1243, 2), (key1247, 2), (key1233, 2), (key1236, 2), (key1243, -4), (key1130, 2), (key1159, -1), (key1174, -1), (key1022, 2), (key1080, -1), (key1174, -1), (key1009, -1), (key1022, -1), (key1044, -1), (key1130, -1), (key1080, 2), (key1159, 2), (key1116, -1), (key1125, -1), (key1152, 2), (key1003, -1), (key1017, -1), (key1038, 2), (key1125, 2), (key1073, -1), (key1152, -1), (key1003, 2), (key1038, -1), (key1116, -1)]

def rawRow6313 : Integer.Sparse Key := [(key1236, -4), (key1247, 2), (key1243, 2), (key1236, 2), (key1233, 2), (key1243, -4), (key1130, 2), (key1174, -1), (key1159, -1), (key1022, 2), (key1174, -1), (key1080, -1), (key1022, -1), (key1009, -1), (key1130, -1), (key1044, -1), (key1159, 2), (key1080, 2), (key1125, -1), (key1116, -1), (key1152, 2), (key1017, -1), (key1003, -1), (key1125, 2), (key1038, 2), (key1152, -1), (key1073, -1), (key1003, 2), (key1116, -1), (key1038, -1)]

def rawRow6314 : Integer.Sparse Key := [(key1243, -4), (key1236, 2), (key1247, 2), (key1233, 2), (key1243, 2), (key1236, -4), (key1159, 2), (key1130, -1), (key1174, -1), (key1080, 2), (key1022, -1), (key1174, -1), (key1044, -1), (key1080, -1), (key1009, -1), (key1159, -1), (key1022, 2), (key1130, 2), (key1116, -1), (key1152, -1), (key1125, 2), (key1038, -1), (key1073, -1), (key1003, 2), (key1152, 2), (key1017, -1), (key1125, -1), (key1038, 2), (key1003, -1), (key1116, -1)]

def rawRow6315 : Integer.Sparse Key := [(key1243, -4), (key1247, 2), (key1236, 2), (key1243, 2), (key1233, 2), (key1236, -4), (key1159, 2), (key1174, -1), (key1130, -1), (key1080, 2), (key1174, -1), (key1022, -1), (key1080, -1), (key1044, -1), (key1159, -1), (key1009, -1), (key1130, 2), (key1022, 2), (key1152, -1), (key1116, -1), (key1125, 2), (key1073, -1), (key1038, -1), (key1152, 2), (key1003, 2), (key1125, -1), (key1017, -1), (key1038, 2), (key1116, -1), (key1003, -1)]

def rawRow6316 : Integer.Sparse Key := [(key1247, -4), (key1236, 2), (key1243, 2), (key1236, 2), (key1243, 2), (key1233, -4), (key1174, 2), (key1130, -1), (key1159, -1), (key1174, 2), (key1022, -1), (key1080, -1), (key1130, -1), (key1159, -1), (key1022, -1), (key1080, -1), (key1009, 2), (key1044, 2), (key1125, -1), (key1152, -1), (key1116, 2), (key1125, -1), (key1152, -1), (key1017, 2), (key1073, 2), (key1003, -1), (key1038, -1), (key1116, 2), (key1003, -1), (key1038, -1)]

def rawRow6317 : Integer.Sparse Key := [(key1247, -4), (key1243, 2), (key1236, 2), (key1243, 2), (key1236, 2), (key1233, -4), (key1174, 2), (key1159, -1), (key1130, -1), (key1174, 2), (key1080, -1), (key1022, -1), (key1159, -1), (key1130, -1), (key1080, -1), (key1022, -1), (key1044, 2), (key1009, 2), (key1152, -1), (key1125, -1), (key1116, 2), (key1152, -1), (key1125, -1), (key1073, 2), (key1017, 2), (key1038, -1), (key1003, -1), (key1116, 2), (key1038, -1), (key1003, -1)]

def rawRow6398 : Integer.Sparse Key := [(key1387, -1), (key1393, -1), (key1393, 2), (key1420, -1), (key1426, -1), (key1420, 2), (key1472, 2), (key1426, -1), (key1472, -1), (key1444, 2), (key1444, -1), (key1480, -1), (key1292, 1), (key1298, 1), (key1298, -2), (key1569, 1), (key1575, 1), (key1569, -2), (key1903, -2), (key1575, 1), (key1903, 1), (key1593, -2), (key1593, 1), (key1911, 1), (key1312, -1), (key1351, -1), (key1318, 1), (key1351, 1), (key1542, 1), (key1896, 1), (key1548, -1), (key1896, -1), (key1618, -1), (key1681, -1), (key1618, 1), (key1918, 1), (key1633, 1), (key1689, 1), (key1633, -1), (key1926, -1)]

def rawRow6399 : Integer.Sparse Key := [(key1393, -1), (key1387, -1), (key1393, 2), (key1426, -1), (key1420, -1), (key1472, 2), (key1420, 2), (key1472, -1), (key1426, -1), (key1444, 2), (key1480, -1), (key1444, -1), (key1298, 1), (key1292, 1), (key1298, -2), (key1575, 1), (key1569, 1), (key1903, -2), (key1569, -2), (key1903, 1), (key1575, 1), (key1593, -2), (key1911, 1), (key1593, 1), (key1351, -1), (key1312, -1), (key1351, 1), (key1318, 1), (key1896, 1), (key1542, 1), (key1896, -1), (key1548, -1), (key1681, -1), (key1618, -1), (key1918, 1), (key1618, 1), (key1689, 1), (key1633, 1), (key1926, -1), (key1633, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6400 : Integer.Sparse Key := [(key1393, -1), (key1393, -1), (key1387, 2), (key1472, -1), (key1472, -1), (key1426, 2), (key1426, 2), (key1420, -1), (key1420, -1), (key1480, 2), (key1444, -1), (key1444, -1), (key1298, 1), (key1298, 1), (key1292, -2), (key1903, 1), (key1903, 1), (key1575, -2), (key1575, -2), (key1569, 1), (key1569, 1), (key1911, -2), (key1593, 1), (key1593, 1), (key1318, -1), (key1318, -1), (key1312, 1), (key1312, 1), (key1548, 1), (key1548, 1), (key1542, -1), (key1542, -1), (key1918, -1), (key1918, -1), (key1681, 1), (key1681, 1), (key1926, 1), (key1926, 1), (key1689, -1), (key1689, -1)]

def rawRow6401 : Integer.Sparse Key := [(key1420, -1), (key1426, -1), (key1444, 2), (key1387, -1), (key1393, -1), (key1420, 2), (key1472, 2), (key1444, -1), (key1480, -1), (key1393, 2), (key1426, -1), (key1472, -1), (key1569, 1), (key1575, 1), (key1593, -2), (key1292, 1), (key1298, 1), (key1569, -2), (key1903, -2), (key1593, 1), (key1911, 1), (key1298, -2), (key1575, 1), (key1903, 1), (key1618, -1), (key1681, -1), (key1633, 1), (key1689, 1), (key1618, 1), (key1918, 1), (key1633, -1), (key1926, -1), (key1312, -1), (key1351, -1), (key1542, 1), (key1896, 1), (key1318, 1), (key1351, 1), (key1548, -1), (key1896, -1)]

def rawRow6402 : Integer.Sparse Key := [(key1426, -1), (key1420, -1), (key1444, 2), (key1393, -1), (key1387, -1), (key1472, 2), (key1420, 2), (key1480, -1), (key1444, -1), (key1393, 2), (key1472, -1), (key1426, -1), (key1575, 1), (key1569, 1), (key1593, -2), (key1298, 1), (key1292, 1), (key1903, -2), (key1569, -2), (key1911, 1), (key1593, 1), (key1298, -2), (key1903, 1), (key1575, 1), (key1681, -1), (key1618, -1), (key1689, 1), (key1633, 1), (key1918, 1), (key1618, 1), (key1926, -1), (key1633, -1), (key1351, -1), (key1312, -1), (key1896, 1), (key1542, 1), (key1351, 1), (key1318, 1), (key1896, -1), (key1548, -1)]

def rawRow6403 : Integer.Sparse Key := [(key1420, -1), (key1444, -1), (key1426, 2), (key1420, -1), (key1444, -1), (key1387, 2), (key1480, 2), (key1393, -1), (key1472, -1), (key1426, 2), (key1393, -1), (key1472, -1), (key1569, 1), (key1593, 1), (key1575, -2), (key1569, 1), (key1593, 1), (key1292, -2), (key1911, -2), (key1298, 1), (key1903, 1), (key1575, -2), (key1298, 1), (key1903, 1), (key1542, -1), (key1689, -1), (key1548, 1), (key1681, 1), (key1312, 1), (key1926, 1), (key1318, -1), (key1918, -1), (key1542, -1), (key1689, -1), (key1312, 1), (key1926, 1), (key1548, 1), (key1681, 1), (key1318, -1), (key1918, -1)]

def rawRow6404 : Integer.Sparse Key := [(key1444, -1), (key1420, -1), (key1426, 2), (key1444, -1), (key1420, -1), (key1480, 2), (key1387, 2), (key1472, -1), (key1393, -1), (key1426, 2), (key1472, -1), (key1393, -1), (key1593, 1), (key1569, 1), (key1575, -2), (key1593, 1), (key1569, 1), (key1911, -2), (key1292, -2), (key1903, 1), (key1298, 1), (key1575, -2), (key1903, 1), (key1298, 1), (key1689, -1), (key1542, -1), (key1681, 1), (key1548, 1), (key1926, 1), (key1312, 1), (key1918, -1), (key1318, -1), (key1689, -1), (key1542, -1), (key1926, 1), (key1312, 1), (key1681, 1), (key1548, 1), (key1918, -1), (key1318, -1)]

def rawRow6405 : Integer.Sparse Key := [(key1426, -1), (key1444, -1), (key1420, 2), (key1472, -1), (key1480, -1), (key1393, 2), (key1444, 2), (key1387, -1), (key1420, -1), (key1472, 2), (key1393, -1), (key1426, -1), (key1575, 1), (key1593, 1), (key1569, -2), (key1903, 1), (key1911, 1), (key1298, -2), (key1593, -2), (key1292, 1), (key1569, 1), (key1903, -2), (key1298, 1), (key1575, 1), (key1548, -1), (key1633, -1), (key1542, 1), (key1618, 1), (key1318, 1), (key1633, 1), (key1312, -1), (key1618, -1), (key1896, -1), (key1926, -1), (key1351, 1), (key1689, 1), (key1896, 1), (key1918, 1), (key1351, -1), (key1681, -1)]

def rawRow6406 : Integer.Sparse Key := [(key1444, -1), (key1426, -1), (key1420, 2), (key1480, -1), (key1472, -1), (key1444, 2), (key1393, 2), (key1420, -1), (key1387, -1), (key1472, 2), (key1426, -1), (key1393, -1), (key1593, 1), (key1575, 1), (key1569, -2), (key1911, 1), (key1903, 1), (key1593, -2), (key1298, -2), (key1569, 1), (key1292, 1), (key1903, -2), (key1575, 1), (key1298, 1), (key1633, -1), (key1548, -1), (key1618, 1), (key1542, 1), (key1633, 1), (key1318, 1), (key1618, -1), (key1312, -1), (key1926, -1), (key1896, -1), (key1689, 1), (key1351, 1), (key1918, 1), (key1896, 1), (key1681, -1), (key1351, -1)]

def rawRow6407 : Integer.Sparse Key := [(key1472, -1), (key1472, -1), (key1480, 2), (key1393, -1), (key1393, -1), (key1426, 2), (key1426, 2), (key1444, -1), (key1444, -1), (key1387, 2), (key1420, -1), (key1420, -1), (key1903, 1), (key1903, 1), (key1911, -2), (key1298, 1), (key1298, 1), (key1575, -2), (key1575, -2), (key1593, 1), (key1593, 1), (key1292, -2), (key1569, 1), (key1569, 1), (key1918, -1), (key1918, -1), (key1926, 1), (key1926, 1), (key1681, 1), (key1681, 1), (key1689, -1), (key1689, -1), (key1318, -1), (key1318, -1), (key1548, 1), (key1548, 1), (key1312, 1), (key1312, 1), (key1542, -1), (key1542, -1)]

def rawRow6408 : Integer.Sparse Key := [(key1472, -1), (key1480, -1), (key1472, 2), (key1426, -1), (key1444, -1), (key1393, 2), (key1444, 2), (key1393, -1), (key1426, -1), (key1420, 2), (key1387, -1), (key1420, -1), (key1903, 1), (key1911, 1), (key1903, -2), (key1575, 1), (key1593, 1), (key1298, -2), (key1593, -2), (key1298, 1), (key1575, 1), (key1569, -2), (key1292, 1), (key1569, 1), (key1896, -1), (key1926, -1), (key1896, 1), (key1918, 1), (key1351, 1), (key1689, 1), (key1351, -1), (key1681, -1), (key1548, -1), (key1633, -1), (key1318, 1), (key1633, 1), (key1542, 1), (key1618, 1), (key1312, -1), (key1618, -1)]

def rawRow6409 : Integer.Sparse Key := [(key1480, -1), (key1472, -1), (key1472, 2), (key1444, -1), (key1426, -1), (key1444, 2), (key1393, 2), (key1426, -1), (key1393, -1), (key1420, 2), (key1420, -1), (key1387, -1), (key1911, 1), (key1903, 1), (key1903, -2), (key1593, 1), (key1575, 1), (key1593, -2), (key1298, -2), (key1575, 1), (key1298, 1), (key1569, -2), (key1569, 1), (key1292, 1), (key1926, -1), (key1896, -1), (key1918, 1), (key1896, 1), (key1689, 1), (key1351, 1), (key1681, -1), (key1351, -1), (key1633, -1), (key1548, -1), (key1633, 1), (key1318, 1), (key1618, 1), (key1542, 1), (key1618, -1), (key1312, -1)]

def rawRow6410 : Integer.Sparse Key := [(key1542, -1), (key1548, -1), (key1556, 2), (key1569, -1), (key1575, -1), (key1618, 2), (key1681, 2), (key1624, -1), (key1683, -1), (key1593, 2), (key1633, -1), (key1689, -1), (key1312, 1), (key1318, 1), (key1326, -2), (key1420, 1), (key1426, 1), (key1618, -2), (key1918, -2), (key1624, 1), (key1920, 1), (key1444, -2), (key1633, 1), (key1926, 1), (key1312, -1), (key1351, -1), (key1326, 1), (key1354, 1), (key1542, 1), (key1896, 1), (key1556, -1), (key1899, -1), (key1420, -1), (key1472, -1), (key1569, 1), (key1903, 1), (key1444, 1), (key1480, 1), (key1593, -1), (key1911, -1)]

def rawRow6411 : Integer.Sparse Key := [(key1548, -1), (key1542, -1), (key1556, 2), (key1575, -1), (key1569, -1), (key1681, 2), (key1618, 2), (key1683, -1), (key1624, -1), (key1593, 2), (key1689, -1), (key1633, -1), (key1318, 1), (key1312, 1), (key1326, -2), (key1426, 1), (key1420, 1), (key1918, -2), (key1618, -2), (key1920, 1), (key1624, 1), (key1444, -2), (key1926, 1), (key1633, 1), (key1351, -1), (key1312, -1), (key1354, 1), (key1326, 1), (key1896, 1), (key1542, 1), (key1899, -1), (key1556, -1), (key1472, -1), (key1420, -1), (key1903, 1), (key1569, 1), (key1480, 1), (key1444, 1), (key1911, -1), (key1593, -1)]

def rawRow6412 : Integer.Sparse Key := [(key1548, -1), (key1556, -1), (key1542, 2), (key1681, -1), (key1683, -1), (key1575, 2), (key1624, 2), (key1569, -1), (key1618, -1), (key1689, 2), (key1593, -1), (key1633, -1), (key1318, 1), (key1326, 1), (key1312, -2), (key1918, 1), (key1920, 1), (key1426, -2), (key1624, -2), (key1420, 1), (key1618, 1), (key1926, -2), (key1444, 1), (key1633, 1), (key1298, -1), (key1326, -1), (key1292, 1), (key1312, 1), (key1393, 1), (key1556, 1), (key1387, -1), (key1542, -1), (key1903, -1), (key1920, -1), (key1472, 1), (key1683, 1), (key1911, 1), (key1926, 1), (key1480, -1), (key1689, -1)]

def rawRow6413 : Integer.Sparse Key := [(key1556, -1), (key1548, -1), (key1542, 2), (key1683, -1), (key1681, -1), (key1624, 2), (key1575, 2), (key1618, -1), (key1569, -1), (key1689, 2), (key1633, -1), (key1593, -1), (key1326, 1), (key1318, 1), (key1312, -2), (key1920, 1), (key1918, 1), (key1624, -2), (key1426, -2), (key1618, 1), (key1420, 1), (key1926, -2), (key1633, 1), (key1444, 1), (key1326, -1), (key1298, -1), (key1312, 1), (key1292, 1), (key1556, 1), (key1393, 1), (key1542, -1), (key1387, -1), (key1920, -1), (key1903, -1), (key1683, 1), (key1472, 1), (key1926, 1), (key1911, 1), (key1689, -1), (key1480, -1)]

def rawRow6414 : Integer.Sparse Key := [(key1569, -1), (key1575, -1), (key1593, 2), (key1542, -1), (key1548, -1), (key1618, 2), (key1681, 2), (key1633, -1), (key1689, -1), (key1556, 2), (key1624, -1), (key1683, -1), (key1420, 1), (key1426, 1), (key1444, -2), (key1312, 1), (key1318, 1), (key1618, -2), (key1918, -2), (key1633, 1), (key1926, 1), (key1326, -2), (key1624, 1), (key1920, 1), (key1420, -1), (key1472, -1), (key1444, 1), (key1480, 1), (key1569, 1), (key1903, 1), (key1593, -1), (key1911, -1), (key1312, -1), (key1351, -1), (key1542, 1), (key1896, 1), (key1326, 1), (key1354, 1), (key1556, -1), (key1899, -1)]

def rawRow6415 : Integer.Sparse Key := [(key1575, -1), (key1569, -1), (key1593, 2), (key1548, -1), (key1542, -1), (key1681, 2), (key1618, 2), (key1689, -1), (key1633, -1), (key1556, 2), (key1683, -1), (key1624, -1), (key1426, 1), (key1420, 1), (key1444, -2), (key1318, 1), (key1312, 1), (key1918, -2), (key1618, -2), (key1926, 1), (key1633, 1), (key1326, -2), (key1920, 1), (key1624, 1), (key1472, -1), (key1420, -1), (key1480, 1), (key1444, 1), (key1903, 1), (key1569, 1), (key1911, -1), (key1593, -1), (key1351, -1), (key1312, -1), (key1896, 1), (key1542, 1), (key1354, 1), (key1326, 1), (key1899, -1), (key1556, -1)]

def rawRow6416 : Integer.Sparse Key := [(key1569, -1), (key1593, -1), (key1575, 2), (key1618, -1), (key1633, -1), (key1542, 2), (key1689, 2), (key1548, -1), (key1681, -1), (key1624, 2), (key1556, -1), (key1683, -1), (key1420, 1), (key1444, 1), (key1426, -2), (key1618, 1), (key1633, 1), (key1312, -2), (key1926, -2), (key1318, 1), (key1918, 1), (key1624, -2), (key1326, 1), (key1920, 1), (key1387, -1), (key1480, -1), (key1393, 1), (key1472, 1), (key1292, 1), (key1911, 1), (key1298, -1), (key1903, -1), (key1542, -1), (key1689, -1), (key1312, 1), (key1926, 1), (key1556, 1), (key1683, 1), (key1326, -1), (key1920, -1)]

def rawRow6417 : Integer.Sparse Key := [(key1593, -1), (key1569, -1), (key1575, 2), (key1633, -1), (key1618, -1), (key1689, 2), (key1542, 2), (key1681, -1), (key1548, -1), (key1624, 2), (key1683, -1), (key1556, -1), (key1444, 1), (key1420, 1), (key1426, -2), (key1633, 1), (key1618, 1), (key1926, -2), (key1312, -2), (key1918, 1), (key1318, 1), (key1624, -2), (key1920, 1), (key1326, 1), (key1480, -1), (key1387, -1), (key1472, 1), (key1393, 1), (key1911, 1), (key1292, 1), (key1903, -1), (key1298, -1), (key1689, -1), (key1542, -1), (key1926, 1), (key1312, 1), (key1683, 1), (key1556, 1), (key1920, -1), (key1326, -1)]

def rawRow6418 : Integer.Sparse Key := [(key1618, -1), (key1633, -1), (key1624, 2), (key1569, -1), (key1593, -1), (key1542, 2), (key1689, 2), (key1556, -1), (key1683, -1), (key1575, 2), (key1548, -1), (key1681, -1), (key1618, 1), (key1633, 1), (key1624, -2), (key1420, 1), (key1444, 1), (key1312, -2), (key1926, -2), (key1326, 1), (key1920, 1), (key1426, -2), (key1318, 1), (key1918, 1), (key1542, -1), (key1689, -1), (key1556, 1), (key1683, 1), (key1312, 1), (key1926, 1), (key1326, -1), (key1920, -1), (key1387, -1), (key1480, -1), (key1292, 1), (key1911, 1), (key1393, 1), (key1472, 1), (key1298, -1), (key1903, -1)]

def rawRow6419 : Integer.Sparse Key := [(key1633, -1), (key1618, -1), (key1624, 2), (key1593, -1), (key1569, -1), (key1689, 2), (key1542, 2), (key1683, -1), (key1556, -1), (key1575, 2), (key1681, -1), (key1548, -1), (key1633, 1), (key1618, 1), (key1624, -2), (key1444, 1), (key1420, 1), (key1926, -2), (key1312, -2), (key1920, 1), (key1326, 1), (key1426, -2), (key1918, 1), (key1318, 1), (key1689, -1), (key1542, -1), (key1683, 1), (key1556, 1), (key1926, 1), (key1312, 1), (key1920, -1), (key1326, -1), (key1480, -1), (key1387, -1), (key1911, 1), (key1292, 1), (key1472, 1), (key1393, 1), (key1903, -1), (key1298, -1)]

def rawRow6420 : Integer.Sparse Key := [(key1624, -1), (key1633, -1), (key1618, 2), (key1683, -1), (key1689, -1), (key1556, 2), (key1593, 2), (key1542, -1), (key1569, -1), (key1681, 2), (key1548, -1), (key1575, -1), (key1624, 1), (key1633, 1), (key1618, -2), (key1920, 1), (key1926, 1), (key1326, -2), (key1444, -2), (key1312, 1), (key1420, 1), (key1918, -2), (key1318, 1), (key1426, 1), (key1556, -1), (key1593, -1), (key1542, 1), (key1569, 1), (key1326, 1), (key1444, 1), (key1312, -1), (key1420, -1), (key1899, -1), (key1911, -1), (key1354, 1), (key1480, 1), (key1896, 1), (key1903, 1), (key1351, -1), (key1472, -1)]

def rawRow6421 : Integer.Sparse Key := [(key1633, -1), (key1624, -1), (key1618, 2), (key1689, -1), (key1683, -1), (key1593, 2), (key1556, 2), (key1569, -1), (key1542, -1), (key1681, 2), (key1575, -1), (key1548, -1), (key1633, 1), (key1624, 1), (key1618, -2), (key1926, 1), (key1920, 1), (key1444, -2), (key1326, -2), (key1420, 1), (key1312, 1), (key1918, -2), (key1426, 1), (key1318, 1), (key1593, -1), (key1556, -1), (key1569, 1), (key1542, 1), (key1444, 1), (key1326, 1), (key1420, -1), (key1312, -1), (key1911, -1), (key1899, -1), (key1480, 1), (key1354, 1), (key1903, 1), (key1896, 1), (key1472, -1), (key1351, -1)]

def rawRow6422 : Integer.Sparse Key := [(key1681, -1), (key1683, -1), (key1689, 2), (key1548, -1), (key1556, -1), (key1575, 2), (key1624, 2), (key1593, -1), (key1633, -1), (key1542, 2), (key1569, -1), (key1618, -1), (key1918, 1), (key1920, 1), (key1926, -2), (key1318, 1), (key1326, 1), (key1426, -2), (key1624, -2), (key1444, 1), (key1633, 1), (key1312, -2), (key1420, 1), (key1618, 1), (key1903, -1), (key1920, -1), (key1911, 1), (key1926, 1), (key1472, 1), (key1683, 1), (key1480, -1), (key1689, -1), (key1298, -1), (key1326, -1), (key1393, 1), (key1556, 1), (key1292, 1), (key1312, 1), (key1387, -1), (key1542, -1)]

def rawRow6423 : Integer.Sparse Key := [(key1683, -1), (key1681, -1), (key1689, 2), (key1556, -1), (key1548, -1), (key1624, 2), (key1575, 2), (key1633, -1), (key1593, -1), (key1542, 2), (key1618, -1), (key1569, -1), (key1920, 1), (key1918, 1), (key1926, -2), (key1326, 1), (key1318, 1), (key1624, -2), (key1426, -2), (key1633, 1), (key1444, 1), (key1312, -2), (key1618, 1), (key1420, 1), (key1920, -1), (key1903, -1), (key1926, 1), (key1911, 1), (key1683, 1), (key1472, 1), (key1689, -1), (key1480, -1), (key1326, -1), (key1298, -1), (key1556, 1), (key1393, 1), (key1312, 1), (key1292, 1), (key1542, -1), (key1387, -1)]

def rawRow6424 : Integer.Sparse Key := [(key1683, -1), (key1689, -1), (key1681, 2), (key1624, -1), (key1633, -1), (key1556, 2), (key1593, 2), (key1548, -1), (key1575, -1), (key1618, 2), (key1542, -1), (key1569, -1), (key1920, 1), (key1926, 1), (key1918, -2), (key1624, 1), (key1633, 1), (key1326, -2), (key1444, -2), (key1318, 1), (key1426, 1), (key1618, -2), (key1312, 1), (key1420, 1), (key1899, -1), (key1911, -1), (key1896, 1), (key1903, 1), (key1354, 1), (key1480, 1), (key1351, -1), (key1472, -1), (key1556, -1), (key1593, -1), (key1326, 1), (key1444, 1), (key1542, 1), (key1569, 1), (key1312, -1), (key1420, -1)]

def rawRow6425 : Integer.Sparse Key := [(key1689, -1), (key1683, -1), (key1681, 2), (key1633, -1), (key1624, -1), (key1593, 2), (key1556, 2), (key1575, -1), (key1548, -1), (key1618, 2), (key1569, -1), (key1542, -1), (key1926, 1), (key1920, 1), (key1918, -2), (key1633, 1), (key1624, 1), (key1444, -2), (key1326, -2), (key1426, 1), (key1318, 1), (key1618, -2), (key1420, 1), (key1312, 1), (key1911, -1), (key1899, -1), (key1903, 1), (key1896, 1), (key1480, 1), (key1354, 1), (key1472, -1), (key1351, -1), (key1593, -1), (key1556, -1), (key1444, 1), (key1326, 1), (key1569, 1), (key1542, 1), (key1420, -1), (key1312, -1)]

def rawRow6426 : Integer.Sparse Key := [(key1896, -1), (key1896, -1), (key1899, 2), (key1903, -1), (key1903, -1), (key1918, 2), (key1918, 2), (key1920, -1), (key1920, -1), (key1911, 2), (key1926, -1), (key1926, -1), (key1351, 1), (key1351, 1), (key1354, -2), (key1472, 1), (key1472, 1), (key1681, -2), (key1681, -2), (key1683, 1), (key1683, 1), (key1480, -2), (key1689, 1), (key1689, 1), (key1318, -1), (key1318, -1), (key1326, 1), (key1326, 1), (key1548, 1), (key1548, 1), (key1556, -1), (key1556, -1), (key1426, -1), (key1426, -1), (key1575, 1), (key1575, 1), (key1444, 1), (key1444, 1), (key1593, -1), (key1593, -1)]

def rawRow6427 : Integer.Sparse Key := [(key1896, -1), (key1899, -1), (key1896, 2), (key1918, -1), (key1920, -1), (key1903, 2), (key1920, 2), (key1903, -1), (key1918, -1), (key1926, 2), (key1911, -1), (key1926, -1), (key1351, 1), (key1354, 1), (key1351, -2), (key1681, 1), (key1683, 1), (key1472, -2), (key1683, -2), (key1472, 1), (key1681, 1), (key1689, -2), (key1480, 1), (key1689, 1), (key1298, -1), (key1326, -1), (key1298, 1), (key1318, 1), (key1393, 1), (key1556, 1), (key1393, -1), (key1548, -1), (key1575, -1), (key1624, -1), (key1426, 1), (key1624, 1), (key1593, 1), (key1633, 1), (key1444, -1), (key1633, -1)]

def rawRow6428 : Integer.Sparse Key := [(key1899, -1), (key1896, -1), (key1896, 2), (key1920, -1), (key1918, -1), (key1920, 2), (key1903, 2), (key1918, -1), (key1903, -1), (key1926, 2), (key1926, -1), (key1911, -1), (key1354, 1), (key1351, 1), (key1351, -2), (key1683, 1), (key1681, 1), (key1683, -2), (key1472, -2), (key1681, 1), (key1472, 1), (key1689, -2), (key1689, 1), (key1480, 1), (key1326, -1), (key1298, -1), (key1318, 1), (key1298, 1), (key1556, 1), (key1393, 1), (key1548, -1), (key1393, -1), (key1624, -1), (key1575, -1), (key1624, 1), (key1426, 1), (key1633, 1), (key1593, 1), (key1633, -1), (key1444, -1)]

def rawRow6429 : Integer.Sparse Key := [(key1903, -1), (key1903, -1), (key1911, 2), (key1896, -1), (key1896, -1), (key1918, 2), (key1918, 2), (key1926, -1), (key1926, -1), (key1899, 2), (key1920, -1), (key1920, -1), (key1472, 1), (key1472, 1), (key1480, -2), (key1351, 1), (key1351, 1), (key1681, -2), (key1681, -2), (key1689, 1), (key1689, 1), (key1354, -2), (key1683, 1), (key1683, 1), (key1426, -1), (key1426, -1), (key1444, 1), (key1444, 1), (key1575, 1), (key1575, 1), (key1593, -1), (key1593, -1), (key1318, -1), (key1318, -1), (key1548, 1), (key1548, 1), (key1326, 1), (key1326, 1), (key1556, -1), (key1556, -1)]

def rawRow6430 : Integer.Sparse Key := [(key1903, -1), (key1911, -1), (key1903, 2), (key1918, -1), (key1926, -1), (key1896, 2), (key1926, 2), (key1896, -1), (key1918, -1), (key1920, 2), (key1899, -1), (key1920, -1), (key1472, 1), (key1480, 1), (key1472, -2), (key1681, 1), (key1689, 1), (key1351, -2), (key1689, -2), (key1351, 1), (key1681, 1), (key1683, -2), (key1354, 1), (key1683, 1), (key1393, -1), (key1444, -1), (key1393, 1), (key1426, 1), (key1298, 1), (key1593, 1), (key1298, -1), (key1575, -1), (key1548, -1), (key1633, -1), (key1318, 1), (key1633, 1), (key1556, 1), (key1624, 1), (key1326, -1), (key1624, -1)]

def rawRow6431 : Integer.Sparse Key := [(key1911, -1), (key1903, -1), (key1903, 2), (key1926, -1), (key1918, -1), (key1926, 2), (key1896, 2), (key1918, -1), (key1896, -1), (key1920, 2), (key1920, -1), (key1899, -1), (key1480, 1), (key1472, 1), (key1472, -2), (key1689, 1), (key1681, 1), (key1689, -2), (key1351, -2), (key1681, 1), (key1351, 1), (key1683, -2), (key1683, 1), (key1354, 1), (key1444, -1), (key1393, -1), (key1426, 1), (key1393, 1), (key1593, 1), (key1298, 1), (key1575, -1), (key1298, -1), (key1633, -1), (key1548, -1), (key1633, 1), (key1318, 1), (key1624, 1), (key1556, 1), (key1624, -1), (key1326, -1)]

def rawRow6432 : Integer.Sparse Key := [(key1918, -1), (key1920, -1), (key1926, 2), (key1896, -1), (key1899, -1), (key1903, 2), (key1920, 2), (key1911, -1), (key1926, -1), (key1896, 2), (key1903, -1), (key1918, -1), (key1681, 1), (key1683, 1), (key1689, -2), (key1351, 1), (key1354, 1), (key1472, -2), (key1683, -2), (key1480, 1), (key1689, 1), (key1351, -2), (key1472, 1), (key1681, 1), (key1575, -1), (key1624, -1), (key1593, 1), (key1633, 1), (key1426, 1), (key1624, 1), (key1444, -1), (key1633, -1), (key1298, -1), (key1326, -1), (key1393, 1), (key1556, 1), (key1298, 1), (key1318, 1), (key1393, -1), (key1548, -1)]

def rawRow6433 : Integer.Sparse Key := [(key1920, -1), (key1918, -1), (key1926, 2), (key1899, -1), (key1896, -1), (key1920, 2), (key1903, 2), (key1926, -1), (key1911, -1), (key1896, 2), (key1918, -1), (key1903, -1), (key1683, 1), (key1681, 1), (key1689, -2), (key1354, 1), (key1351, 1), (key1683, -2), (key1472, -2), (key1689, 1), (key1480, 1), (key1351, -2), (key1681, 1), (key1472, 1), (key1624, -1), (key1575, -1), (key1633, 1), (key1593, 1), (key1624, 1), (key1426, 1), (key1633, -1), (key1444, -1), (key1326, -1), (key1298, -1), (key1556, 1), (key1393, 1), (key1318, 1), (key1298, 1), (key1548, -1), (key1393, -1)]

def rawRow6434 : Integer.Sparse Key := [(key1918, -1), (key1926, -1), (key1920, 2), (key1903, -1), (key1911, -1), (key1896, 2), (key1926, 2), (key1899, -1), (key1920, -1), (key1903, 2), (key1896, -1), (key1918, -1), (key1681, 1), (key1689, 1), (key1683, -2), (key1472, 1), (key1480, 1), (key1351, -2), (key1689, -2), (key1354, 1), (key1683, 1), (key1472, -2), (key1351, 1), (key1681, 1), (key1548, -1), (key1633, -1), (key1556, 1), (key1624, 1), (key1318, 1), (key1633, 1), (key1326, -1), (key1624, -1), (key1393, -1), (key1444, -1), (key1298, 1), (key1593, 1), (key1393, 1), (key1426, 1), (key1298, -1), (key1575, -1)]

def rawRow6435 : Integer.Sparse Key := [(key1926, -1), (key1918, -1), (key1920, 2), (key1911, -1), (key1903, -1), (key1926, 2), (key1896, 2), (key1920, -1), (key1899, -1), (key1903, 2), (key1918, -1), (key1896, -1), (key1689, 1), (key1681, 1), (key1683, -2), (key1480, 1), (key1472, 1), (key1689, -2), (key1351, -2), (key1683, 1), (key1354, 1), (key1472, -2), (key1681, 1), (key1351, 1), (key1633, -1), (key1548, -1), (key1624, 1), (key1556, 1), (key1633, 1), (key1318, 1), (key1624, -1), (key1326, -1), (key1444, -1), (key1393, -1), (key1593, 1), (key1298, 1), (key1426, 1), (key1393, 1), (key1575, -1), (key1298, -1)]

def rawRow6436 : Integer.Sparse Key := [(key1920, -1), (key1926, -1), (key1918, 2), (key1920, -1), (key1926, -1), (key1899, 2), (key1911, 2), (key1896, -1), (key1903, -1), (key1918, 2), (key1896, -1), (key1903, -1), (key1683, 1), (key1689, 1), (key1681, -2), (key1683, 1), (key1689, 1), (key1354, -2), (key1480, -2), (key1351, 1), (key1472, 1), (key1681, -2), (key1351, 1), (key1472, 1), (key1556, -1), (key1593, -1), (key1548, 1), (key1575, 1), (key1326, 1), (key1444, 1), (key1318, -1), (key1426, -1), (key1556, -1), (key1593, -1), (key1326, 1), (key1444, 1), (key1548, 1), (key1575, 1), (key1318, -1), (key1426, -1)]

def rawRow6437 : Integer.Sparse Key := [(key1926, -1), (key1920, -1), (key1918, 2), (key1926, -1), (key1920, -1), (key1911, 2), (key1899, 2), (key1903, -1), (key1896, -1), (key1918, 2), (key1903, -1), (key1896, -1), (key1689, 1), (key1683, 1), (key1681, -2), (key1689, 1), (key1683, 1), (key1480, -2), (key1354, -2), (key1472, 1), (key1351, 1), (key1681, -2), (key1472, 1), (key1351, 1), (key1593, -1), (key1556, -1), (key1575, 1), (key1548, 1), (key1444, 1), (key1326, 1), (key1426, -1), (key1318, -1), (key1593, -1), (key1556, -1), (key1444, 1), (key1326, 1), (key1575, 1), (key1548, 1), (key1426, -1), (key1318, -1)]

def rawRow6498 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1303, 2), (key1316, -1), (key1316, -1), (key1337, 2), (key1337, 2), (key1340, -1), (key1340, -1), (key1330, 2), (key1346, -1), (key1346, -1), (key1391, 1), (key1391, 1), (key1398, -2), (key1546, 1), (key1546, 1), (key1772, -2), (key1772, -2), (key1775, 1), (key1775, 1), (key1560, -2), (key1781, 1), (key1781, 1), (key1455, -1), (key1455, -1), (key1458, 1), (key1458, 1), (key1788, 1), (key1788, 1), (key1791, -1), (key1791, -1), (key1655, -1), (key1655, -1), (key1813, 1), (key1813, 1), (key1660, 1), (key1660, 1), (key1818, -1), (key1818, -1)]

def rawRow6499 : Integer.Sparse Key := [(key1296, -1), (key1303, -1), (key1296, 2), (key1337, -1), (key1340, -1), (key1316, 2), (key1340, 2), (key1316, -1), (key1337, -1), (key1346, 2), (key1330, -1), (key1346, -1), (key1391, 1), (key1398, 1), (key1391, -2), (key1772, 1), (key1775, 1), (key1546, -2), (key1775, -2), (key1546, 1), (key1772, 1), (key1781, -2), (key1560, 1), (key1781, 1), (key1424, -1), (key1458, -1), (key1424, 1), (key1455, 1), (key1573, 1), (key1791, 1), (key1573, -1), (key1788, -1), (key1813, -1), (key1840, -1), (key1655, 1), (key1840, 1), (key1818, 1), (key1842, 1), (key1660, -1), (key1842, -1)]

def rawRow6500 : Integer.Sparse Key := [(key1303, -1), (key1296, -1), (key1296, 2), (key1340, -1), (key1337, -1), (key1340, 2), (key1316, 2), (key1337, -1), (key1316, -1), (key1346, 2), (key1346, -1), (key1330, -1), (key1398, 1), (key1391, 1), (key1391, -2), (key1775, 1), (key1772, 1), (key1775, -2), (key1546, -2), (key1772, 1), (key1546, 1), (key1781, -2), (key1781, 1), (key1560, 1), (key1458, -1), (key1424, -1), (key1455, 1), (key1424, 1), (key1791, 1), (key1573, 1), (key1788, -1), (key1573, -1), (key1840, -1), (key1813, -1), (key1840, 1), (key1655, 1), (key1842, 1), (key1818, 1), (key1842, -1), (key1660, -1)]

def rawRow6501 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1330, 2), (key1296, -1), (key1296, -1), (key1337, 2), (key1337, 2), (key1346, -1), (key1346, -1), (key1303, 2), (key1340, -1), (key1340, -1), (key1546, 1), (key1546, 1), (key1560, -2), (key1391, 1), (key1391, 1), (key1772, -2), (key1772, -2), (key1781, 1), (key1781, 1), (key1398, -2), (key1775, 1), (key1775, 1), (key1655, -1), (key1655, -1), (key1660, 1), (key1660, 1), (key1813, 1), (key1813, 1), (key1818, -1), (key1818, -1), (key1455, -1), (key1455, -1), (key1788, 1), (key1788, 1), (key1458, 1), (key1458, 1), (key1791, -1), (key1791, -1)]

def rawRow6502 : Integer.Sparse Key := [(key1316, -1), (key1330, -1), (key1316, 2), (key1337, -1), (key1346, -1), (key1296, 2), (key1346, 2), (key1296, -1), (key1337, -1), (key1340, 2), (key1303, -1), (key1340, -1), (key1546, 1), (key1560, 1), (key1546, -2), (key1772, 1), (key1781, 1), (key1391, -2), (key1781, -2), (key1391, 1), (key1772, 1), (key1775, -2), (key1398, 1), (key1775, 1), (key1573, -1), (key1660, -1), (key1573, 1), (key1655, 1), (key1424, 1), (key1818, 1), (key1424, -1), (key1813, -1), (key1788, -1), (key1842, -1), (key1455, 1), (key1842, 1), (key1791, 1), (key1840, 1), (key1458, -1), (key1840, -1)]

def rawRow6503 : Integer.Sparse Key := [(key1330, -1), (key1316, -1), (key1316, 2), (key1346, -1), (key1337, -1), (key1346, 2), (key1296, 2), (key1337, -1), (key1296, -1), (key1340, 2), (key1340, -1), (key1303, -1), (key1560, 1), (key1546, 1), (key1546, -2), (key1781, 1), (key1772, 1), (key1781, -2), (key1391, -2), (key1772, 1), (key1391, 1), (key1775, -2), (key1775, 1), (key1398, 1), (key1660, -1), (key1573, -1), (key1655, 1), (key1573, 1), (key1818, 1), (key1424, 1), (key1813, -1), (key1424, -1), (key1842, -1), (key1788, -1), (key1842, 1), (key1455, 1), (key1840, 1), (key1791, 1), (key1840, -1), (key1458, -1)]

def rawRow6504 : Integer.Sparse Key := [(key1337, -1), (key1340, -1), (key1346, 2), (key1296, -1), (key1303, -1), (key1316, 2), (key1340, 2), (key1330, -1), (key1346, -1), (key1296, 2), (key1316, -1), (key1337, -1), (key1772, 1), (key1775, 1), (key1781, -2), (key1391, 1), (key1398, 1), (key1546, -2), (key1775, -2), (key1560, 1), (key1781, 1), (key1391, -2), (key1546, 1), (key1772, 1), (key1813, -1), (key1840, -1), (key1818, 1), (key1842, 1), (key1655, 1), (key1840, 1), (key1660, -1), (key1842, -1), (key1424, -1), (key1458, -1), (key1573, 1), (key1791, 1), (key1424, 1), (key1455, 1), (key1573, -1), (key1788, -1)]

def rawRow6505 : Integer.Sparse Key := [(key1340, -1), (key1337, -1), (key1346, 2), (key1303, -1), (key1296, -1), (key1340, 2), (key1316, 2), (key1346, -1), (key1330, -1), (key1296, 2), (key1337, -1), (key1316, -1), (key1775, 1), (key1772, 1), (key1781, -2), (key1398, 1), (key1391, 1), (key1775, -2), (key1546, -2), (key1781, 1), (key1560, 1), (key1391, -2), (key1772, 1), (key1546, 1), (key1840, -1), (key1813, -1), (key1842, 1), (key1818, 1), (key1840, 1), (key1655, 1), (key1842, -1), (key1660, -1), (key1458, -1), (key1424, -1), (key1791, 1), (key1573, 1), (key1455, 1), (key1424, 1), (key1788, -1), (key1573, -1)]

def rawRow6506 : Integer.Sparse Key := [(key1337, -1), (key1346, -1), (key1340, 2), (key1316, -1), (key1330, -1), (key1296, 2), (key1346, 2), (key1303, -1), (key1340, -1), (key1316, 2), (key1296, -1), (key1337, -1), (key1772, 1), (key1781, 1), (key1775, -2), (key1546, 1), (key1560, 1), (key1391, -2), (key1781, -2), (key1398, 1), (key1775, 1), (key1546, -2), (key1391, 1), (key1772, 1), (key1788, -1), (key1842, -1), (key1791, 1), (key1840, 1), (key1455, 1), (key1842, 1), (key1458, -1), (key1840, -1), (key1573, -1), (key1660, -1), (key1424, 1), (key1818, 1), (key1573, 1), (key1655, 1), (key1424, -1), (key1813, -1)]

def rawRow6507 : Integer.Sparse Key := [(key1346, -1), (key1337, -1), (key1340, 2), (key1330, -1), (key1316, -1), (key1346, 2), (key1296, 2), (key1340, -1), (key1303, -1), (key1316, 2), (key1337, -1), (key1296, -1), (key1781, 1), (key1772, 1), (key1775, -2), (key1560, 1), (key1546, 1), (key1781, -2), (key1391, -2), (key1775, 1), (key1398, 1), (key1546, -2), (key1772, 1), (key1391, 1), (key1842, -1), (key1788, -1), (key1840, 1), (key1791, 1), (key1842, 1), (key1455, 1), (key1840, -1), (key1458, -1), (key1660, -1), (key1573, -1), (key1818, 1), (key1424, 1), (key1655, 1), (key1573, 1), (key1813, -1), (key1424, -1)]

def rawRow6508 : Integer.Sparse Key := [(key1340, -1), (key1346, -1), (key1337, 2), (key1340, -1), (key1346, -1), (key1303, 2), (key1330, 2), (key1296, -1), (key1316, -1), (key1337, 2), (key1296, -1), (key1316, -1), (key1775, 1), (key1781, 1), (key1772, -2), (key1775, 1), (key1781, 1), (key1398, -2), (key1560, -2), (key1391, 1), (key1546, 1), (key1772, -2), (key1391, 1), (key1546, 1), (key1791, -1), (key1818, -1), (key1788, 1), (key1813, 1), (key1458, 1), (key1660, 1), (key1455, -1), (key1655, -1), (key1791, -1), (key1818, -1), (key1458, 1), (key1660, 1), (key1788, 1), (key1813, 1), (key1455, -1), (key1655, -1)]

def rawRow6509 : Integer.Sparse Key := [(key1346, -1), (key1340, -1), (key1337, 2), (key1346, -1), (key1340, -1), (key1330, 2), (key1303, 2), (key1316, -1), (key1296, -1), (key1337, 2), (key1316, -1), (key1296, -1), (key1781, 1), (key1775, 1), (key1772, -2), (key1781, 1), (key1775, 1), (key1560, -2), (key1398, -2), (key1546, 1), (key1391, 1), (key1772, -2), (key1546, 1), (key1391, 1), (key1818, -1), (key1791, -1), (key1813, 1), (key1788, 1), (key1660, 1), (key1458, 1), (key1655, -1), (key1455, -1), (key1818, -1), (key1791, -1), (key1660, 1), (key1458, 1), (key1813, 1), (key1788, 1), (key1655, -1), (key1455, -1)]

def rawRow6510 : Integer.Sparse Key := [(key1775, -1), (key1781, -1), (key1772, 2), (key1840, -1), (key1842, -1), (key1791, 2), (key1818, 2), (key1788, -1), (key1813, -1), (key1845, 2), (key1799, -1), (key1826, -1), (key1340, 1), (key1346, 1), (key1337, -2), (key1840, 1), (key1842, 1), (key1458, -2), (key1660, -2), (key1455, 1), (key1655, 1), (key1845, -2), (key1467, 1), (key1668, 1), (key1303, -1), (key1330, -1), (key1296, 1), (key1316, 1), (key1398, 1), (key1560, 1), (key1391, -1), (key1546, -1), (key1791, -1), (key1818, -1), (key1458, 1), (key1660, 1), (key1799, 1), (key1826, 1), (key1467, -1), (key1668, -1)]

def rawRow6511 : Integer.Sparse Key := [(key1781, -1), (key1775, -1), (key1772, 2), (key1842, -1), (key1840, -1), (key1818, 2), (key1791, 2), (key1813, -1), (key1788, -1), (key1845, 2), (key1826, -1), (key1799, -1), (key1346, 1), (key1340, 1), (key1337, -2), (key1842, 1), (key1840, 1), (key1660, -2), (key1458, -2), (key1655, 1), (key1455, 1), (key1845, -2), (key1668, 1), (key1467, 1), (key1330, -1), (key1303, -1), (key1316, 1), (key1296, 1), (key1560, 1), (key1398, 1), (key1546, -1), (key1391, -1), (key1818, -1), (key1791, -1), (key1660, 1), (key1458, 1), (key1826, 1), (key1799, 1), (key1668, -1), (key1467, -1)]

def rawRow6512 : Integer.Sparse Key := [(key1788, -1), (key1799, -1), (key1791, 2), (key1813, -1), (key1826, -1), (key1772, 2), (key1845, 2), (key1775, -1), (key1840, -1), (key1818, 2), (key1781, -1), (key1842, -1), (key1455, 1), (key1467, 1), (key1458, -2), (key1655, 1), (key1668, 1), (key1337, -2), (key1845, -2), (key1340, 1), (key1840, 1), (key1660, -2), (key1346, 1), (key1842, 1), (key1391, -1), (key1467, -1), (key1398, 1), (key1458, 1), (key1296, 1), (key1799, 1), (key1303, -1), (key1791, -1), (key1546, -1), (key1668, -1), (key1316, 1), (key1826, 1), (key1560, 1), (key1660, 1), (key1330, -1), (key1818, -1)]

def rawRow6513 : Integer.Sparse Key := [(key1799, -1), (key1788, -1), (key1791, 2), (key1826, -1), (key1813, -1), (key1845, 2), (key1772, 2), (key1840, -1), (key1775, -1), (key1818, 2), (key1842, -1), (key1781, -1), (key1467, 1), (key1455, 1), (key1458, -2), (key1668, 1), (key1655, 1), (key1845, -2), (key1337, -2), (key1840, 1), (key1340, 1), (key1660, -2), (key1842, 1), (key1346, 1), (key1467, -1), (key1391, -1), (key1458, 1), (key1398, 1), (key1799, 1), (key1296, 1), (key1791, -1), (key1303, -1), (key1668, -1), (key1546, -1), (key1826, 1), (key1316, 1), (key1660, 1), (key1560, 1), (key1818, -1), (key1330, -1)]

def rawRow6514 : Integer.Sparse Key := [(key1813, -1), (key1826, -1), (key1818, 2), (key1788, -1), (key1799, -1), (key1772, 2), (key1845, 2), (key1781, -1), (key1842, -1), (key1791, 2), (key1775, -1), (key1840, -1), (key1655, 1), (key1668, 1), (key1660, -2), (key1455, 1), (key1467, 1), (key1337, -2), (key1845, -2), (key1346, 1), (key1842, 1), (key1458, -2), (key1340, 1), (key1840, 1), (key1546, -1), (key1668, -1), (key1560, 1), (key1660, 1), (key1316, 1), (key1826, 1), (key1330, -1), (key1818, -1), (key1391, -1), (key1467, -1), (key1296, 1), (key1799, 1), (key1398, 1), (key1458, 1), (key1303, -1), (key1791, -1)]

def rawRow6515 : Integer.Sparse Key := [(key1826, -1), (key1813, -1), (key1818, 2), (key1799, -1), (key1788, -1), (key1845, 2), (key1772, 2), (key1842, -1), (key1781, -1), (key1791, 2), (key1840, -1), (key1775, -1), (key1668, 1), (key1655, 1), (key1660, -2), (key1467, 1), (key1455, 1), (key1845, -2), (key1337, -2), (key1842, 1), (key1346, 1), (key1458, -2), (key1840, 1), (key1340, 1), (key1668, -1), (key1546, -1), (key1660, 1), (key1560, 1), (key1826, 1), (key1316, 1), (key1818, -1), (key1330, -1), (key1467, -1), (key1391, -1), (key1799, 1), (key1296, 1), (key1458, 1), (key1398, 1), (key1791, -1), (key1303, -1)]

def rawRow6516 : Integer.Sparse Key := [(key1840, -1), (key1842, -1), (key1845, 2), (key1775, -1), (key1781, -1), (key1791, 2), (key1818, 2), (key1799, -1), (key1826, -1), (key1772, 2), (key1788, -1), (key1813, -1), (key1840, 1), (key1842, 1), (key1845, -2), (key1340, 1), (key1346, 1), (key1458, -2), (key1660, -2), (key1467, 1), (key1668, 1), (key1337, -2), (key1455, 1), (key1655, 1), (key1791, -1), (key1818, -1), (key1799, 1), (key1826, 1), (key1458, 1), (key1660, 1), (key1467, -1), (key1668, -1), (key1303, -1), (key1330, -1), (key1398, 1), (key1560, 1), (key1296, 1), (key1316, 1), (key1391, -1), (key1546, -1)]

def rawRow6517 : Integer.Sparse Key := [(key1842, -1), (key1840, -1), (key1845, 2), (key1781, -1), (key1775, -1), (key1818, 2), (key1791, 2), (key1826, -1), (key1799, -1), (key1772, 2), (key1813, -1), (key1788, -1), (key1842, 1), (key1840, 1), (key1845, -2), (key1346, 1), (key1340, 1), (key1660, -2), (key1458, -2), (key1668, 1), (key1467, 1), (key1337, -2), (key1655, 1), (key1455, 1), (key1818, -1), (key1791, -1), (key1826, 1), (key1799, 1), (key1660, 1), (key1458, 1), (key1668, -1), (key1467, -1), (key1330, -1), (key1303, -1), (key1560, 1), (key1398, 1), (key1316, 1), (key1296, 1), (key1546, -1), (key1391, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6538 : Integer.Sparse Key := [(key1004, -4), (key1008, 2), (key1008, 2), (key1021, 2), (key1021, 2), (key1023, -4), (key1039, 2), (key1043, -1), (key1043, -1), (key1117, 2), (key1195, -1), (key1195, -1), (key1129, -1), (key1129, -1), (key1201, -1), (key1201, -1), (key1202, 2), (key1202, 2), (key1078, -1), (key1078, -1), (key1081, 2), (key1157, -1), (key1157, -1), (key1214, 2), (key1214, 2), (key1216, -1), (key1216, -1), (key1176, 2), (key1225, -1), (key1225, -1)]

def rawRow6539 : Integer.Sparse Key := [(key1008, -4), (key1004, 2), (key1008, 2), (key1021, 2), (key1023, 2), (key1021, -4), (key1043, 2), (key1039, -1), (key1043, -1), (key1195, 2), (key1117, -1), (key1195, -1), (key1201, -1), (key1202, -1), (key1129, -1), (key1202, -1), (key1129, 2), (key1201, 2), (key1078, -1), (key1081, -1), (key1078, 2), (key1214, -1), (key1216, -1), (key1157, 2), (key1216, 2), (key1157, -1), (key1214, -1), (key1225, 2), (key1176, -1), (key1225, -1)]

def rawRow6540 : Integer.Sparse Key := [(key1008, -4), (key1008, 2), (key1004, 2), (key1023, 2), (key1021, 2), (key1021, -4), (key1043, 2), (key1043, -1), (key1039, -1), (key1195, 2), (key1195, -1), (key1117, -1), (key1202, -1), (key1201, -1), (key1202, -1), (key1129, -1), (key1201, 2), (key1129, 2), (key1081, -1), (key1078, -1), (key1078, 2), (key1216, -1), (key1214, -1), (key1216, 2), (key1157, 2), (key1214, -1), (key1157, -1), (key1225, 2), (key1225, -1), (key1176, -1)]

def rawRow6541 : Integer.Sparse Key := [(key1004, -4), (key1021, 2), (key1021, 2), (key1008, 2), (key1008, 2), (key1023, -4), (key1117, 2), (key1129, -1), (key1129, -1), (key1039, 2), (key1201, -1), (key1201, -1), (key1043, -1), (key1043, -1), (key1195, -1), (key1195, -1), (key1202, 2), (key1202, 2), (key1157, -1), (key1157, -1), (key1176, 2), (key1078, -1), (key1078, -1), (key1214, 2), (key1214, 2), (key1225, -1), (key1225, -1), (key1081, 2), (key1216, -1), (key1216, -1)]

def rawRow6542 : Integer.Sparse Key := [(key1021, -4), (key1004, 2), (key1021, 2), (key1008, 2), (key1023, 2), (key1008, -4), (key1129, 2), (key1117, -1), (key1129, -1), (key1201, 2), (key1039, -1), (key1201, -1), (key1195, -1), (key1202, -1), (key1043, -1), (key1202, -1), (key1043, 2), (key1195, 2), (key1157, -1), (key1176, -1), (key1157, 2), (key1214, -1), (key1225, -1), (key1078, 2), (key1225, 2), (key1078, -1), (key1214, -1), (key1216, 2), (key1081, -1), (key1216, -1)]

def rawRow6543 : Integer.Sparse Key := [(key1021, -4), (key1021, 2), (key1004, 2), (key1023, 2), (key1008, 2), (key1008, -4), (key1129, 2), (key1129, -1), (key1117, -1), (key1201, 2), (key1201, -1), (key1039, -1), (key1202, -1), (key1195, -1), (key1202, -1), (key1043, -1), (key1195, 2), (key1043, 2), (key1176, -1), (key1157, -1), (key1157, 2), (key1225, -1), (key1214, -1), (key1225, 2), (key1078, 2), (key1214, -1), (key1078, -1), (key1216, 2), (key1216, -1), (key1081, -1)]

def rawRow6544 : Integer.Sparse Key := [(key1008, -4), (key1021, 2), (key1023, 2), (key1004, 2), (key1008, 2), (key1021, -4), (key1195, 2), (key1201, -1), (key1202, -1), (key1043, 2), (key1129, -1), (key1202, -1), (key1039, -1), (key1043, -1), (key1117, -1), (key1195, -1), (key1129, 2), (key1201, 2), (key1214, -1), (key1216, -1), (key1225, 2), (key1078, -1), (key1081, -1), (key1157, 2), (key1216, 2), (key1176, -1), (key1225, -1), (key1078, 2), (key1157, -1), (key1214, -1)]

def rawRow6545 : Integer.Sparse Key := [(key1008, -4), (key1023, 2), (key1021, 2), (key1008, 2), (key1004, 2), (key1021, -4), (key1195, 2), (key1202, -1), (key1201, -1), (key1043, 2), (key1202, -1), (key1129, -1), (key1043, -1), (key1039, -1), (key1195, -1), (key1117, -1), (key1201, 2), (key1129, 2), (key1216, -1), (key1214, -1), (key1225, 2), (key1081, -1), (key1078, -1), (key1216, 2), (key1157, 2), (key1225, -1), (key1176, -1), (key1078, 2), (key1214, -1), (key1157, -1)]

def rawRow6546 : Integer.Sparse Key := [(key1021, -4), (key1008, 2), (key1023, 2), (key1004, 2), (key1021, 2), (key1008, -4), (key1201, 2), (key1195, -1), (key1202, -1), (key1129, 2), (key1043, -1), (key1202, -1), (key1117, -1), (key1129, -1), (key1039, -1), (key1201, -1), (key1043, 2), (key1195, 2), (key1214, -1), (key1225, -1), (key1216, 2), (key1157, -1), (key1176, -1), (key1078, 2), (key1225, 2), (key1081, -1), (key1216, -1), (key1157, 2), (key1078, -1), (key1214, -1)]

def rawRow6547 : Integer.Sparse Key := [(key1021, -4), (key1023, 2), (key1008, 2), (key1021, 2), (key1004, 2), (key1008, -4), (key1201, 2), (key1202, -1), (key1195, -1), (key1129, 2), (key1202, -1), (key1043, -1), (key1129, -1), (key1117, -1), (key1201, -1), (key1039, -1), (key1195, 2), (key1043, 2), (key1225, -1), (key1214, -1), (key1216, 2), (key1176, -1), (key1157, -1), (key1225, 2), (key1078, 2), (key1216, -1), (key1081, -1), (key1157, 2), (key1214, -1), (key1078, -1)]

def rawRow6548 : Integer.Sparse Key := [(key1023, -4), (key1008, 2), (key1021, 2), (key1008, 2), (key1021, 2), (key1004, -4), (key1202, 2), (key1195, -1), (key1201, -1), (key1202, 2), (key1043, -1), (key1129, -1), (key1195, -1), (key1201, -1), (key1043, -1), (key1129, -1), (key1039, 2), (key1117, 2), (key1216, -1), (key1225, -1), (key1214, 2), (key1216, -1), (key1225, -1), (key1081, 2), (key1176, 2), (key1078, -1), (key1157, -1), (key1214, 2), (key1078, -1), (key1157, -1)]

def rawRow6549 : Integer.Sparse Key := [(key1023, -4), (key1021, 2), (key1008, 2), (key1021, 2), (key1008, 2), (key1004, -4), (key1202, 2), (key1201, -1), (key1195, -1), (key1202, 2), (key1129, -1), (key1043, -1), (key1201, -1), (key1195, -1), (key1129, -1), (key1043, -1), (key1117, 2), (key1039, 2), (key1225, -1), (key1216, -1), (key1214, 2), (key1225, -1), (key1216, -1), (key1176, 2), (key1081, 2), (key1157, -1), (key1078, -1), (key1214, 2), (key1157, -1), (key1078, -1)]

def rawRow6550 : Integer.Sparse Key := [(key1202, -4), (key1195, 2), (key1201, 2), (key1216, 2), (key1225, 2), (key1214, -4), (key1023, 2), (key1008, -1), (key1021, -1), (key1202, 2), (key1043, -1), (key1129, -1), (key1216, -1), (key1225, -1), (key1081, -1), (key1176, -1), (key1078, 2), (key1157, 2), (key1008, -1), (key1021, -1), (key1004, 2), (key1195, -1), (key1201, -1), (key1043, 2), (key1129, 2), (key1039, -1), (key1117, -1), (key1214, 2), (key1078, -1), (key1157, -1)]

def rawRow6551 : Integer.Sparse Key := [(key1202, -4), (key1201, 2), (key1195, 2), (key1225, 2), (key1216, 2), (key1214, -4), (key1023, 2), (key1021, -1), (key1008, -1), (key1202, 2), (key1129, -1), (key1043, -1), (key1225, -1), (key1216, -1), (key1176, -1), (key1081, -1), (key1157, 2), (key1078, 2), (key1021, -1), (key1008, -1), (key1004, 2), (key1201, -1), (key1195, -1), (key1129, 2), (key1043, 2), (key1117, -1), (key1039, -1), (key1214, 2), (key1157, -1), (key1078, -1)]

def rawRow6552 : Integer.Sparse Key := [(key1214, -4), (key1195, 2), (key1216, 2), (key1201, 2), (key1225, 2), (key1202, -4), (key1078, 2), (key1043, -1), (key1081, -1), (key1157, 2), (key1008, -1), (key1216, -1), (key1129, -1), (key1176, -1), (key1021, -1), (key1225, -1), (key1023, 2), (key1202, 2), (key1039, -1), (key1078, -1), (key1043, 2), (key1117, -1), (key1157, -1), (key1004, 2), (key1214, 2), (key1008, -1), (key1195, -1), (key1129, 2), (key1021, -1), (key1201, -1)]

def rawRow6553 : Integer.Sparse Key := [(key1214, -4), (key1216, 2), (key1195, 2), (key1225, 2), (key1201, 2), (key1202, -4), (key1078, 2), (key1081, -1), (key1043, -1), (key1157, 2), (key1216, -1), (key1008, -1), (key1176, -1), (key1129, -1), (key1225, -1), (key1021, -1), (key1202, 2), (key1023, 2), (key1078, -1), (key1039, -1), (key1043, 2), (key1157, -1), (key1117, -1), (key1214, 2), (key1004, 2), (key1195, -1), (key1008, -1), (key1129, 2), (key1201, -1), (key1021, -1)]

def rawRow6554 : Integer.Sparse Key := [(key1214, -4), (key1201, 2), (key1225, 2), (key1195, 2), (key1216, 2), (key1202, -4), (key1157, 2), (key1129, -1), (key1176, -1), (key1078, 2), (key1021, -1), (key1225, -1), (key1043, -1), (key1081, -1), (key1008, -1), (key1216, -1), (key1023, 2), (key1202, 2), (key1117, -1), (key1157, -1), (key1129, 2), (key1039, -1), (key1078, -1), (key1004, 2), (key1214, 2), (key1021, -1), (key1201, -1), (key1043, 2), (key1008, -1), (key1195, -1)]

def rawRow6555 : Integer.Sparse Key := [(key1214, -4), (key1225, 2), (key1201, 2), (key1216, 2), (key1195, 2), (key1202, -4), (key1157, 2), (key1176, -1), (key1129, -1), (key1078, 2), (key1225, -1), (key1021, -1), (key1081, -1), (key1043, -1), (key1216, -1), (key1008, -1), (key1202, 2), (key1023, 2), (key1157, -1), (key1117, -1), (key1129, 2), (key1078, -1), (key1039, -1), (key1214, 2), (key1004, 2), (key1201, -1), (key1021, -1), (key1043, 2), (key1195, -1), (key1008, -1)]

def rawRow6556 : Integer.Sparse Key := [(key1202, -4), (key1216, 2), (key1225, 2), (key1195, 2), (key1201, 2), (key1214, -4), (key1202, 2), (key1216, -1), (key1225, -1), (key1023, 2), (key1081, -1), (key1176, -1), (key1008, -1), (key1021, -1), (key1043, -1), (key1129, -1), (key1078, 2), (key1157, 2), (key1195, -1), (key1201, -1), (key1214, 2), (key1008, -1), (key1021, -1), (key1043, 2), (key1129, 2), (key1078, -1), (key1157, -1), (key1004, 2), (key1039, -1), (key1117, -1)]

def rawRow6557 : Integer.Sparse Key := [(key1202, -4), (key1225, 2), (key1216, 2), (key1201, 2), (key1195, 2), (key1214, -4), (key1202, 2), (key1225, -1), (key1216, -1), (key1023, 2), (key1176, -1), (key1081, -1), (key1021, -1), (key1008, -1), (key1129, -1), (key1043, -1), (key1157, 2), (key1078, 2), (key1201, -1), (key1195, -1), (key1214, 2), (key1021, -1), (key1008, -1), (key1129, 2), (key1043, 2), (key1157, -1), (key1078, -1), (key1004, 2), (key1117, -1), (key1039, -1)]

def rawRow6578 : Integer.Sparse Key := [(key2672, -2), (key2675, 1), (key2675, 1), (key2707, -2), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2749, 1), (key2749, 1), (key2751, -2), (key2751, -2), (key2787, 2), (key2797, -1), (key2797, -1), (key2810, 2), (key2833, -1), (key2833, -1), (key2899, -1), (key2899, -1), (key2906, -1), (key2906, -1), (key2915, 2), (key2915, 2), (key2940, -1), (key2940, -1), (key2945, 1), (key2945, 1), (key2952, -1), (key2952, -1), (key2964, 1), (key2964, 1), (key2978, 1), (key2978, 1), (key2994, -1), (key2994, -1), (key3001, 1), (key3001, 1), (key3004, -1), (key3004, -1)]

def rawRow6579 : Integer.Sparse Key := [(key2675, -2), (key2672, 1), (key2675, 1), (key2730, -2), (key2707, 1), (key2730, 1), (key2749, 1), (key2751, 1), (key2739, 1), (key2751, 1), (key2739, -2), (key2749, -2), (key2797, 2), (key2787, -1), (key2797, -1), (key2833, 2), (key2810, -1), (key2833, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2915, -1), (key2899, 2), (key2906, 2), (key2945, -1), (key2946, -1), (key2940, 1), (key2946, 1), (key2962, -1), (key2964, -1), (key2952, 1), (key2962, 1), (key2985, 1), (key2994, 1), (key2978, -1), (key2985, -1), (key2999, 1), (key3004, 1), (key2999, -1), (key3001, -1)]

def rawRow6580 : Integer.Sparse Key := [(key2675, -2), (key2675, 1), (key2672, 1), (key2730, -2), (key2730, 1), (key2707, 1), (key2751, 1), (key2749, 1), (key2751, 1), (key2739, 1), (key2749, -2), (key2739, -2), (key2797, 2), (key2797, -1), (key2787, -1), (key2833, 2), (key2833, -1), (key2810, -1), (key2915, -1), (key2906, -1), (key2915, -1), (key2899, -1), (key2906, 2), (key2899, 2), (key2946, -1), (key2945, -1), (key2946, 1), (key2940, 1), (key2964, -1), (key2962, -1), (key2962, 1), (key2952, 1), (key2994, 1), (key2985, 1), (key2985, -1), (key2978, -1), (key3004, 1), (key2999, 1), (key3001, -1), (key2999, -1)]

def rawRow6581 : Integer.Sparse Key := [(key2707, -2), (key2739, 1), (key2739, 1), (key2672, -2), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2730, 1), (key2730, 1), (key2751, -2), (key2751, -2), (key2810, 2), (key2899, -1), (key2899, -1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2833, -1), (key2833, -1), (key2915, 2), (key2915, 2), (key2952, -1), (key2952, -1), (key2978, 1), (key2978, 1), (key2940, -1), (key2940, -1), (key3001, 1), (key3001, 1), (key2945, 1), (key2945, 1), (key3004, -1), (key3004, -1), (key2964, 1), (key2964, 1), (key2994, -1), (key2994, -1)]

def rawRow6582 : Integer.Sparse Key := [(key2739, -2), (key2707, 1), (key2739, 1), (key2749, -2), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2675, 1), (key2751, 1), (key2675, -2), (key2730, -2), (key2899, 2), (key2810, -1), (key2899, -1), (key2906, 2), (key2787, -1), (key2906, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2915, -1), (key2797, 2), (key2833, 2), (key2978, -1), (key2999, -1), (key2952, 1), (key2999, 1), (key2985, -1), (key3001, -1), (key2940, 1), (key2985, 1), (key2962, 1), (key3004, 1), (key2945, -1), (key2962, -1), (key2946, 1), (key2994, 1), (key2946, -1), (key2964, -1)]

def rawRow6583 : Integer.Sparse Key := [(key2739, -2), (key2739, 1), (key2707, 1), (key2749, -2), (key2749, 1), (key2672, 1), (key2751, 1), (key2730, 1), (key2751, 1), (key2675, 1), (key2730, -2), (key2675, -2), (key2899, 2), (key2899, -1), (key2810, -1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2833, -1), (key2915, -1), (key2797, -1), (key2833, 2), (key2797, 2), (key2999, -1), (key2978, -1), (key2999, 1), (key2952, 1), (key3001, -1), (key2985, -1), (key2985, 1), (key2940, 1), (key3004, 1), (key2962, 1), (key2962, -1), (key2945, -1), (key2994, 1), (key2946, 1), (key2964, -1), (key2946, -1)]

def rawRow6584 : Integer.Sparse Key := [(key2730, -2), (key2749, 1), (key2751, 1), (key2675, -2), (key2739, 1), (key2751, 1), (key2672, 1), (key2675, 1), (key2707, 1), (key2730, 1), (key2739, -2), (key2749, -2), (key2833, 2), (key2906, -1), (key2915, -1), (key2797, 2), (key2899, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, -1), (key2833, -1), (key2899, 2), (key2906, 2), (key2962, -1), (key2964, -1), (key2985, 1), (key2994, 1), (key2945, -1), (key2946, -1), (key2999, 1), (key3004, 1), (key2940, 1), (key2946, 1), (key2999, -1), (key3001, -1), (key2952, 1), (key2962, 1), (key2978, -1), (key2985, -1)]

def rawRow6585 : Integer.Sparse Key := [(key2730, -2), (key2751, 1), (key2749, 1), (key2675, -2), (key2751, 1), (key2739, 1), (key2675, 1), (key2672, 1), (key2730, 1), (key2707, 1), (key2749, -2), (key2739, -2), (key2833, 2), (key2915, -1), (key2906, -1), (key2797, 2), (key2915, -1), (key2899, -1), (key2797, -1), (key2787, -1), (key2833, -1), (key2810, -1), (key2906, 2), (key2899, 2), (key2964, -1), (key2962, -1), (key2994, 1), (key2985, 1), (key2946, -1), (key2945, -1), (key3004, 1), (key2999, 1), (key2946, 1), (key2940, 1), (key3001, -1), (key2999, -1), (key2962, 1), (key2952, 1), (key2985, -1), (key2978, -1)]

def rawRow6586 : Integer.Sparse Key := [(key2749, -2), (key2730, 1), (key2751, 1), (key2739, -2), (key2675, 1), (key2751, 1), (key2707, 1), (key2739, 1), (key2672, 1), (key2749, 1), (key2675, -2), (key2730, -2), (key2906, 2), (key2833, -1), (key2915, -1), (key2899, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2899, -1), (key2787, -1), (key2906, -1), (key2797, 2), (key2833, 2), (key2985, -1), (key3001, -1), (key2962, 1), (key3004, 1), (key2978, -1), (key2999, -1), (key2946, 1), (key2994, 1), (key2952, 1), (key2999, 1), (key2946, -1), (key2964, -1), (key2940, 1), (key2985, 1), (key2945, -1), (key2962, -1)]

def rawRow6587 : Integer.Sparse Key := [(key2749, -2), (key2751, 1), (key2730, 1), (key2739, -2), (key2751, 1), (key2675, 1), (key2739, 1), (key2707, 1), (key2749, 1), (key2672, 1), (key2730, -2), (key2675, -2), (key2906, 2), (key2915, -1), (key2833, -1), (key2899, 2), (key2915, -1), (key2797, -1), (key2899, -1), (key2810, -1), (key2906, -1), (key2787, -1), (key2833, 2), (key2797, 2), (key3001, -1), (key2985, -1), (key3004, 1), (key2962, 1), (key2999, -1), (key2978, -1), (key2994, 1), (key2946, 1), (key2999, 1), (key2952, 1), (key2964, -1), (key2946, -1), (key2985, 1), (key2940, 1), (key2962, -1), (key2945, -1)]

def rawRow6588 : Integer.Sparse Key := [(key2751, -2), (key2730, 1), (key2749, 1), (key2751, -2), (key2675, 1), (key2739, 1), (key2730, 1), (key2749, 1), (key2675, 1), (key2739, 1), (key2672, -2), (key2707, -2), (key2915, 2), (key2833, -1), (key2906, -1), (key2915, 2), (key2797, -1), (key2899, -1), (key2833, -1), (key2906, -1), (key2797, -1), (key2899, -1), (key2787, 2), (key2810, 2), (key2994, -1), (key3004, -1), (key2964, 1), (key3001, 1), (key2994, -1), (key3004, -1), (key2945, 1), (key2978, 1), (key2964, 1), (key3001, 1), (key2940, -1), (key2952, -1), (key2945, 1), (key2978, 1), (key2940, -1), (key2952, -1)]

def rawRow6589 : Integer.Sparse Key := [(key2751, -2), (key2749, 1), (key2730, 1), (key2751, -2), (key2739, 1), (key2675, 1), (key2749, 1), (key2730, 1), (key2739, 1), (key2675, 1), (key2707, -2), (key2672, -2), (key2915, 2), (key2906, -1), (key2833, -1), (key2915, 2), (key2899, -1), (key2797, -1), (key2906, -1), (key2833, -1), (key2899, -1), (key2797, -1), (key2810, 2), (key2787, 2), (key3004, -1), (key2994, -1), (key3001, 1), (key2964, 1), (key3004, -1), (key2994, -1), (key2978, 1), (key2945, 1), (key3001, 1), (key2964, 1), (key2952, -1), (key2940, -1), (key2978, 1), (key2945, 1), (key2952, -1), (key2940, -1)]

def rawRow6590 : Integer.Sparse Key := [(key2656, -2), (key2650, 1), (key2655, 1), (key2999, -2), (key2739, 1), (key2899, 1), (key3001, 1), (key3004, 1), (key2751, 1), (key2915, 1), (key2749, -2), (key2906, -2), (key2656, 2), (key2620, -1), (key2643, -1), (key2946, 2), (key2675, -1), (key2797, -1), (key2964, -1), (key2994, -1), (key2751, -1), (key2915, -1), (key2730, 2), (key2833, 2), (key2650, -1), (key2655, -1), (key2620, 1), (key2643, 1), (key2730, -1), (key2749, -1), (key2672, 1), (key2707, 1), (key2833, 1), (key2906, 1), (key2787, -1), (key2810, -1), (key2945, 1), (key2978, 1), (key2940, -1), (key2952, -1)]

def rawRow6591 : Integer.Sparse Key := [(key2656, -2), (key2655, 1), (key2650, 1), (key2999, -2), (key2899, 1), (key2739, 1), (key3004, 1), (key3001, 1), (key2915, 1), (key2751, 1), (key2906, -2), (key2749, -2), (key2656, 2), (key2643, -1), (key2620, -1), (key2946, 2), (key2797, -1), (key2675, -1), (key2994, -1), (key2964, -1), (key2915, -1), (key2751, -1), (key2833, 2), (key2730, 2), (key2655, -1), (key2650, -1), (key2643, 1), (key2620, 1), (key2749, -1), (key2730, -1), (key2707, 1), (key2672, 1), (key2906, 1), (key2833, 1), (key2810, -1), (key2787, -1), (key2978, 1), (key2945, 1), (key2952, -1), (key2940, -1)]

def rawRow6592 : Integer.Sparse Key := [(key2749, -2), (key2739, 1), (key2751, 1), (key2906, -2), (key2650, 1), (key3001, 1), (key2899, 1), (key2915, 1), (key2655, 1), (key3004, 1), (key2656, -2), (key2999, -2), (key2730, 2), (key2675, -1), (key2751, -1), (key2833, 2), (key2620, -1), (key2964, -1), (key2797, -1), (key2915, -1), (key2643, -1), (key2994, -1), (key2656, 2), (key2946, 2), (key2707, -1), (key2730, -1), (key2672, 1), (key2749, 1), (key2810, -1), (key2833, -1), (key2620, 1), (key2833, 1), (key2707, 1), (key2978, 1), (key2643, -1), (key2730, -1), (key2650, 1), (key2906, 1), (key2655, -1), (key2749, -1)]

def rawRow6593 : Integer.Sparse Key := [(key2749, -2), (key2751, 1), (key2739, 1), (key2906, -2), (key3001, 1), (key2650, 1), (key2915, 1), (key2899, 1), (key3004, 1), (key2655, 1), (key2999, -2), (key2656, -2), (key2730, 2), (key2751, -1), (key2675, -1), (key2833, 2), (key2964, -1), (key2620, -1), (key2915, -1), (key2797, -1), (key2994, -1), (key2643, -1), (key2946, 2), (key2656, 2), (key2730, -1), (key2707, -1), (key2749, 1), (key2672, 1), (key2833, -1), (key2810, -1), (key2833, 1), (key2620, 1), (key2978, 1), (key2707, 1), (key2730, -1), (key2643, -1), (key2906, 1), (key2650, 1), (key2749, -1), (key2655, -1)]

def rawRow6594 : Integer.Sparse Key := [(key2906, -2), (key2899, 1), (key2915, 1), (key2749, -2), (key2655, 1), (key3004, 1), (key2739, 1), (key2751, 1), (key2650, 1), (key3001, 1), (key2656, -2), (key2999, -2), (key2833, 2), (key2797, -1), (key2915, -1), (key2730, 2), (key2643, -1), (key2994, -1), (key2675, -1), (key2751, -1), (key2620, -1), (key2964, -1), (key2656, 2), (key2946, 2), (key2810, -1), (key2833, -1), (key2787, 1), (key2906, 1), (key2707, -1), (key2730, -1), (key2643, 1), (key2978, 1), (key2672, 1), (key2749, 1), (key2655, -1), (key2749, -1), (key2620, 1), (key2833, 1), (key2643, -1), (key2730, -1)]

def rawRow6595 : Integer.Sparse Key := [(key2906, -2), (key2915, 1), (key2899, 1), (key2749, -2), (key3004, 1), (key2655, 1), (key2751, 1), (key2739, 1), (key3001, 1), (key2650, 1), (key2999, -2), (key2656, -2), (key2833, 2), (key2915, -1), (key2797, -1), (key2730, 2), (key2994, -1), (key2643, -1), (key2751, -1), (key2675, -1), (key2964, -1), (key2620, -1), (key2946, 2), (key2656, 2), (key2833, -1), (key2810, -1), (key2906, 1), (key2787, 1), (key2730, -1), (key2707, -1), (key2978, 1), (key2643, 1), (key2749, 1), (key2672, 1), (key2749, -1), (key2655, -1), (key2833, 1), (key2620, 1), (key2730, -1), (key2643, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined360_part2 : Sparse := [([1, 0, -1, 1, 0, 0, 0], 18)]

end MUB6.TaoCertificate

end OAI
end


