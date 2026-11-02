-- Prove2me | Definitions.Def_OAIQ106D107
-- name    : OAIQ106D107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:04:25.467058+00:00
-- url     : https://prove2.me/theorems/28a99251-44e9-491e-b818-c80a18928c05
-- title:
--   Definitions bundle OAIQ106D107 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 343 declarations of OpenAI's Lean: 343 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow6652`, `OAI.MUB6.Certificate.GramRows.rawRow6653`, `OAI.MUB6.Certificate.GramRows.rawRow6654`, `OAI.MUB6.Certificate.GramRows.rawRow6655`, `OAI.MUB6.Certificate.GramRows.rawRow6656`, `OAI.MUB6.Certificate.GramRows.rawRow6657`, `OAI.MUB6.Certificate.GramRows.rawRow6658`, `OAI.MUB6.Certificate.GramRows.rawRow6659`, `OAI.MUB6.Certificate.GramRows.rawRow6660`, `OAI.MUB6.Certificate.GramRows.rawRow6661`, `OAI.MUB6.Certificate.GramRows.rawRow6662`, `OAI.MUB6.Certificate.GramRows.rawRow6663`, `OAI.MUB6.Certificate.GramRows.rawRow6664`, `OAI.MUB6.Certificate.GramRows.rawRow6665`, `OAI.MUB6.Certificate.GramRows.rawRow6666`, `OAI.MUB6.Certificate.GramRows.rawRow6667`, `OAI.MUB6.Certificate.GramRows.rawRow6668`, `OAI.MUB6.Certificate.GramRows.rawRow6669`, `OAI.MUB6.Certificate.GramRows.rawRow6670`, `OAI.MUB6.Certificate.GramRows.rawRow6671`, `OAI.MUB6.Certificate.GramRows.rawRow6672`, `OAI.MUB6.Certificate.GramRows.rawRow6673`, `OAI.MUB6.Certificate.GramRows.rawRow6674`, `OAI.MUB6.Certificate.GramRows.rawRow6675`, `OAI.MUB6.Certificate.GramRows.rawRow6676`, `OAI.MUB6.Certificate.GramRows.rawRow6677`, `OAI.MUB6.Certificate.GramRows.rawRow691`, `OAI.MUB6.Certificate.GramRows.rawRow692`, `OAI.MUB6.Certificate.GramRows.rawRow693`, `OAI.MUB6.Certificate.GramRows.rawRow694`, `OAI.MUB6.Certificate.GramRows.rawRow695`, `OAI.MUB6.Certificate.GramRows.rawRow696`, `OAI.MUB6.Certificate.GramRows.rawRow697`, `OAI.MUB6.Certificate.GramRows.rawRow698`, `OAI.MUB6.Certificate.GramRows.rawRow699`, `OAI.MUB6.Certificate.GramRows.rawRow7`, `OAI.MUB6.Certificate.GramRows.rawRow700`, `OAI.MUB6.Certificate.GramRows.rawRow701`, `OAI.MUB6.Certificate.GramRows.rawRow702`, `OAI.MUB6.Certificate.GramRows.rawRow703` and 303 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block18`, `MutuallyUnbiased_GramRows_Block19`, `MutuallyUnbiased_GramRows_Block20`, `MutuallyUnbiased_GramRows_Block21`, `MutuallyUnbiased_GramRows_Block22`, `MutuallyUnbiased_GramRows_Block23`, `MutuallyUnbiased_GramRows_Block75`, `MutuallyUnbiased_GramRows_Block76`, `MutuallyUnbiased_GramRows_Block83`, `MutuallyUnbiased_GramRows_Block84`, `MutuallyUnbiased_GramRows_Block85`, `MutuallyUnbiased_GramRows_Block86`, `MutuallyUnbiased_GramRows_Block88`, `MutuallyUnbiased_GramRows_Block89`, `MutuallyUnbiased_GramRows_Block90`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_MixedSemantics_Values15`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D211`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval2_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block2.entryEval8_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval5_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval7_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval8_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval9_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7` and `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7 : Integer.Sparse Key := [(key267, -1), (key267, -1), (key271, 2), (key239, 1), (key239, 1), (key260, -1), (key260, -1), (key236, -2), (key248, 1), (key248, 1), (key328, 1), (key328, 1), (key340, -2), (key305, -1), (key305, -1), (key335, 1), (key335, 1), (key302, 2), (key316, -1), (key316, -1), (key418, -1), (key418, -1), (key475, 1), (key475, 1), (key397, 1), (key397, 1), (key469, -1), (key469, -1), (key385, -1), (key385, -1), (key406, 1), (key406, 1), (key583, 2), (key601, -1), (key601, -1), (key572, -2), (key595, 1), (key595, 1), (key568, 1), (key568, 1), (key578, -1), (key578, -1)]

def rawRow84 : Integer.Sparse Key := [(key2617, -2), (key2620, 1), (key2620, 1), (key2633, 2), (key2643, -1), (key2643, -1), (key2650, -1), (key2650, -1), (key2655, 1), (key2655, 1), (key2672, 2), (key2675, -1), (key2675, -1), (key2707, -2), (key2730, 1), (key2730, 1), (key2739, 1), (key2739, 1), (key2749, -1), (key2749, -1), (key2787, -2), (key2797, 1), (key2797, 1), (key2810, 2), (key2833, -1), (key2833, -1), (key2899, -1), (key2899, -1), (key2906, 1), (key2906, 1), (key2940, 1), (key2940, 1), (key2945, -1), (key2945, -1), (key2952, -1), (key2952, -1), (key2962, 1), (key2962, 1), (key2978, 1), (key2978, 1), (key2985, -1), (key2985, -1)]

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

def rawRow691 : Integer.Sparse Key := [(key2667, -2), (key2735, -2), (key2747, -2), (key2667, 1), (key2673, 1), (key2702, 1), (key2728, 1), (key2737, 1), (key2747, 1), (key2782, 2), (key2893, 2), (key2904, 2), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, -1), (key2972, -1), (key2983, -1), (key2997, -1), (key3000, -1), (key2936, 1), (key2943, 1), (key2948, 1), (key2960, 1), (key2998, 1), (key3000, 1)]

def rawRow692 : Integer.Sparse Key := [(key2667, -2), (key2747, -2), (key2735, -2), (key2673, 1), (key2667, 1), (key2728, 1), (key2702, 1), (key2747, 1), (key2737, 1), (key2782, 2), (key2904, 2), (key2893, 2), (key2795, -1), (key2782, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2897, -1), (key2938, -1), (key2936, -1), (key2983, -1), (key2972, -1), (key3000, -1), (key2997, -1), (key2943, 1), (key2936, 1), (key2960, 1), (key2948, 1), (key3000, 1), (key2998, 1)]

def rawRow693 : Integer.Sparse Key := [(key2735, -2), (key2667, -2), (key2747, -2), (key2702, 1), (key2737, 1), (key2667, 1), (key2747, 1), (key2673, 1), (key2728, 1), (key2893, 2), (key2782, 2), (key2904, 2), (key2805, -1), (key2897, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2972, -1), (key2997, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2948, 1), (key2998, 1), (key2936, 1), (key3000, 1), (key2943, 1), (key2960, 1)]

def rawRow694 : Integer.Sparse Key := [(key2735, -2), (key2747, -2), (key2667, -2), (key2737, 1), (key2702, 1), (key2747, 1), (key2667, 1), (key2728, 1), (key2673, 1), (key2893, 2), (key2904, 2), (key2782, 2), (key2897, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2831, -1), (key2795, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2983, -1), (key2938, -1), (key2998, 1), (key2948, 1), (key3000, 1), (key2936, 1), (key2960, 1), (key2943, 1)]

def rawRow695 : Integer.Sparse Key := [(key2747, -2), (key2667, -2), (key2735, -2), (key2728, 1), (key2747, 1), (key2673, 1), (key2737, 1), (key2667, 1), (key2702, 1), (key2904, 2), (key2782, 2), (key2893, 2), (key2831, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2782, -1), (key2805, -1), (key2983, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2936, -1), (key2972, -1), (key2960, 1), (key3000, 1), (key2943, 1), (key2998, 1), (key2936, 1), (key2948, 1)]

def rawRow696 : Integer.Sparse Key := [(key2747, -2), (key2735, -2), (key2667, -2), (key2747, 1), (key2728, 1), (key2737, 1), (key2673, 1), (key2702, 1), (key2667, 1), (key2904, 2), (key2893, 2), (key2782, 2), (key2904, -1), (key2831, -1), (key2897, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key3000, -1), (key2983, -1), (key2997, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key3000, 1), (key2960, 1), (key2998, 1), (key2943, 1), (key2948, 1), (key2936, 1)]

def rawRow697 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2948, 1), (key2950, 1), (key2948, 1), (key2960, 1), (key2950, 1), (key2960, 1), (key2702, 2), (key2702, 2), (key2728, 2), (key2972, -1), (key2976, -1), (key2972, -1), (key2983, -1), (key2976, -1), (key2983, -1), (key2735, -1), (key2737, -1), (key2735, -1), (key2747, -1), (key2737, -1), (key2747, -1), (key2893, 1), (key2897, 1), (key2893, 1), (key2904, 1), (key2897, 1), (key2904, 1)]

def rawRow698 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2950, 1), (key2948, 1), (key2960, 1), (key2948, 1), (key2960, 1), (key2950, 1), (key2702, 2), (key2728, 2), (key2702, 2), (key2976, -1), (key2972, -1), (key2983, -1), (key2972, -1), (key2983, -1), (key2976, -1), (key2737, -1), (key2735, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2737, -1), (key2897, 1), (key2893, 1), (key2904, 1), (key2893, 1), (key2904, 1), (key2897, 1)]

def rawRow699 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2960, 1), (key2960, 1), (key2950, 1), (key2950, 1), (key2948, 1), (key2948, 1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2983, -1), (key2976, -1), (key2976, -1), (key2972, -1), (key2972, -1), (key2747, -1), (key2747, -1), (key2737, -1), (key2737, -1), (key2735, -1), (key2735, -1), (key2904, 1), (key2904, 1), (key2897, 1), (key2897, 1), (key2893, 1), (key2893, 1)]

def rawRow700 : Integer.Sparse Key := [(key2612, -2), (key2948, -2), (key2960, -2), (key2612, 1), (key2618, 1), (key2805, 1), (key2831, 1), (key2950, 1), (key2960, 1), (key2628, 2), (key2972, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2728, -1), (key2976, -1), (key2983, -1), (key2646, -1), (key2648, -1), (key2893, -1), (key2904, -1), (key2997, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2747, 1), (key2998, 1), (key3000, 1)]

def rawRow701 : Integer.Sparse Key := [(key2616, -2), (key2960, -2), (key2948, -2), (key2618, 1), (key2612, 1), (key2831, 1), (key2805, 1), (key2960, 1), (key2950, 1), (key2628, 2), (key2983, 2), (key2972, 2), (key2641, -1), (key2628, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2976, -1), (key2648, -1), (key2646, -1), (key2904, -1), (key2893, -1), (key3000, -1), (key2997, -1), (key2653, 1), (key2646, 1), (key2747, 1), (key2735, 1), (key3000, 1), (key2998, 1)]

def rawRow702 : Integer.Sparse Key := [(key2829, -2), (key2612, -2), (key2960, -2), (key2805, 1), (key2950, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2972, 2), (key2628, 2), (key2983, 2), (key2702, -1), (key2976, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2893, -1), (key2997, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2735, 1), (key2998, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2747, 1)]

def rawRow703 : Integer.Sparse Key := [(key2829, -2), (key2960, -2), (key2612, -2), (key2950, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2831, 1), (key2618, 1), (key2972, 2), (key2983, 2), (key2628, 2), (key2976, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2728, -1), (key2641, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2904, -1), (key2648, -1), (key2998, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2747, 1), (key2653, 1)]

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

def rawRow704 : Integer.Sparse Key := [(key3017, -2), (key2616, -2), (key2829, -2), (key2831, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2612, 1), (key2805, 1), (key2983, 2), (key2628, 2), (key2972, 2), (key2728, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2628, -1), (key2702, -1), (key2904, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2646, -1), (key2893, -1), (key2747, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2646, 1), (key2735, 1)]

def rawRow705 : Integer.Sparse Key := [(key3017, -2), (key2829, -2), (key2616, -2), (key2960, 1), (key2831, 1), (key2950, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2983, 2), (key2972, 2), (key2628, 2), (key2983, -1), (key2728, -1), (key2976, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2904, -1), (key2997, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key3000, 1), (key2747, 1), (key2998, 1), (key2653, 1), (key2735, 1), (key2646, 1)]

def rawRow706 : Integer.Sparse Key := [(key2706, -2), (key2860, -2), (key3023, -2), (key2726, 1), (key2732, 1), (key2870, 1), (key3026, 1), (key2885, 1), (key3030, 1), (key2667, 2), (key2735, 2), (key2747, 2), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2897, 1), (key2904, 1)]

def rawRow707 : Integer.Sparse Key := [(key2706, -2), (key3023, -2), (key2860, -2), (key2732, 1), (key2726, 1), (key3026, 1), (key2870, 1), (key3030, 1), (key2885, 1), (key2667, 2), (key2747, 2), (key2735, 2), (key2943, -1), (key2936, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2998, -1), (key2673, -1), (key2667, -1), (key2728, -1), (key2702, -1), (key2747, -1), (key2737, -1), (key2795, 1), (key2782, 1), (key2831, 1), (key2805, 1), (key2904, 1), (key2897, 1)]

def rawRow708 : Integer.Sparse Key := [(key2860, -2), (key2706, -2), (key3023, -2), (key2870, 1), (key2885, 1), (key2726, 1), (key3030, 1), (key2732, 1), (key3026, 1), (key2735, 2), (key2667, 2), (key2747, 2), (key2948, -1), (key2998, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2702, -1), (key2737, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2805, 1), (key2897, 1), (key2782, 1), (key2904, 1), (key2795, 1), (key2831, 1)]

def rawRow709 : Integer.Sparse Key := [(key2860, -2), (key3023, -2), (key2706, -2), (key2885, 1), (key2870, 1), (key3030, 1), (key2726, 1), (key3026, 1), (key2732, 1), (key2735, 2), (key2747, 2), (key2667, 2), (key2998, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2960, -1), (key2943, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2728, -1), (key2673, -1), (key2897, 1), (key2805, 1), (key2904, 1), (key2782, 1), (key2831, 1), (key2795, 1)]

def rawRow710 : Integer.Sparse Key := [(key3023, -2), (key2706, -2), (key2860, -2), (key3026, 1), (key3030, 1), (key2732, 1), (key2885, 1), (key2726, 1), (key2870, 1), (key2747, 2), (key2667, 2), (key2735, 2), (key2960, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2936, -1), (key2948, -1), (key2728, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2667, -1), (key2702, -1), (key2831, 1), (key2904, 1), (key2795, 1), (key2897, 1), (key2782, 1), (key2805, 1)]

def rawRow711 : Integer.Sparse Key := [(key3023, -2), (key2860, -2), (key2706, -2), (key3030, 1), (key3026, 1), (key2885, 1), (key2732, 1), (key2870, 1), (key2726, 1), (key2747, 2), (key2735, 2), (key2667, 2), (key3000, -1), (key2960, -1), (key2998, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2747, -1), (key2728, -1), (key2737, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2904, 1), (key2831, 1), (key2897, 1), (key2795, 1), (key2805, 1), (key2782, 1)]

def rawRow712 : Integer.Sparse Key := [(key2632, -2), (key2870, -2), (key3026, -2), (key2640, 1), (key2644, 1), (key2860, 1), (key3023, 1), (key2885, 1), (key3030, 1), (key2612, 2), (key2948, 2), (key2960, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2747, -1), (key2998, -1), (key3000, -1), (key2612, -1), (key2618, -1), (key2805, -1), (key2831, -1), (key2950, -1), (key2960, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2728, 1), (key2976, 1), (key2983, 1)]

def rawRow713 : Integer.Sparse Key := [(key2632, -2), (key3026, -2), (key2870, -2), (key2644, 1), (key2640, 1), (key3023, 1), (key2860, 1), (key3030, 1), (key2885, 1), (key2616, 2), (key2960, 2), (key2948, 2), (key2653, -1), (key2646, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2998, -1), (key2618, -1), (key2612, -1), (key2831, -1), (key2805, -1), (key2960, -1), (key2950, -1), (key2641, 1), (key2628, 1), (key2728, 1), (key2702, 1), (key2983, 1), (key2976, 1)]

def rawRow714 : Integer.Sparse Key := [(key2870, -2), (key2632, -2), (key3026, -2), (key2860, 1), (key2885, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2829, 2), (key2612, 2), (key2960, 2), (key2735, -1), (key2998, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2805, -1), (key2950, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2702, 1), (key2976, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2728, 1)]

def rawRow715 : Integer.Sparse Key := [(key2870, -2), (key3026, -2), (key2632, -2), (key2885, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key3023, 1), (key2644, 1), (key2829, 2), (key2960, 2), (key2612, 2), (key2998, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2747, -1), (key2653, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2831, -1), (key2618, -1), (key2976, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2728, 1), (key2641, 1)]

def rawRow716 : Integer.Sparse Key := [(key3026, -2), (key2632, -2), (key2870, -2), (key3023, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2640, 1), (key2860, 1), (key3017, 2), (key2616, 2), (key2829, 2), (key2747, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2646, -1), (key2735, -1), (key2831, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2612, -1), (key2805, -1), (key2728, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2628, 1), (key2702, 1)]

def rawRow717 : Integer.Sparse Key := [(key3026, -2), (key2870, -2), (key2632, -2), (key3030, 1), (key3023, 1), (key2885, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key3017, 2), (key2829, 2), (key2616, 2), (key3000, -1), (key2747, -1), (key2998, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, -1), (key2831, -1), (key2950, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 1), (key2728, 1), (key2976, 1), (key2641, 1), (key2702, 1), (key2628, 1)]

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

def rawRow781 : Integer.Sparse Key := [(key1041, -2), (key1041, -2), (key1041, -2), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1033, 1), (key1127, 2), (key1127, 2), (key1127, 2), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1111, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1199, -1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1), (key1193, 1)]

def rawRow788 : Integer.Sparse Key := [(key1127, -2), (key1127, -2), (key1127, -2), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1199, 1), (key1041, 2), (key1041, 2), (key1041, 2), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1193, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1033, -1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1), (key1111, 1)]

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

def rawRow802 : Integer.Sparse Key := [(key70, -6), (key133, 2), (key133, 2), (key133, 2), (key31, 6), (key111, -2), (key111, -2), (key111, -2), (key20, -2), (key20, -2), (key20, -2), (key45, 2), (key45, 2), (key45, 2)]

def rawRow809 : Integer.Sparse Key := [(key1015, -2), (key1015, -2), (key1015, -2), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1001, 1), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1036, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1150, -1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1), (key1123, 1)]

def rawRow816 : Integer.Sparse Key := [(key1071, -2), (key1071, -2), (key1071, -2), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1150, 1), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1123, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1001, -1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1), (key1036, 1)]

def rawRow823 : Integer.Sparse Key := [(key7, -2), (key7, -2), (key7, -2), (key1, 6), (key151, 2), (key151, 2), (key151, 2), (key84, -2), (key84, -2), (key84, -2), (key202, -6), (key193, 2), (key193, 2), (key193, 2)]

def rawRow830 : Integer.Sparse Key := [(key193, -2), (key193, -2), (key193, -2), (key202, 6), (key7, 2), (key7, 2), (key7, 2), (key151, -2), (key151, -2), (key151, -2), (key1, -6), (key84, 2), (key84, 2), (key84, 2)]

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

def rawRow834 : Integer.Sparse Key := [(key2785, -2), (key2785, -2), (key2785, -2), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2793, 1), (key2808, 2), (key2808, 2), (key2808, 2), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2859, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2828, -1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1), (key2869, 1)]

def rawRow838 : Integer.Sparse Key := [(key2808, -2), (key2808, -2), (key2808, -2), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2828, 1), (key2785, 2), (key2785, 2), (key2785, 2), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2869, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2793, -1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1), (key2859, 1)]

def rawRow848 : Integer.Sparse Key := [(key1287, -6), (key1307, 2), (key1307, 2), (key1307, 2), (key1382, 6), (key1537, -2), (key1537, -2), (key1537, -2), (key1415, -2), (key1415, -2), (key1415, -2), (key1564, 2), (key1564, 2), (key1564, 2)]

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

def rawRow6652 : Integer.Sparse Key := [(key2641, 1), (key2628, 1), (key2628, -2), (key2976, 1), (key2972, 1), (key2976, -2), (key2702, -2), (key2972, 1), (key2702, 1), (key2983, -2), (key2983, 1), (key2728, 1), (key2653, -1), (key2646, -1), (key2640, 1), (key2616, 1), (key2758, -1), (key2726, -1), (key2758, 1), (key2671, 1), (key2927, 1), (key2794, 1), (key2829, -1), (key2794, -1), (key3030, 1), (key3017, 1), (key3017, -1), (key3010, -1), (key2644, 2), (key2644, -1), (key2621, -1), (key2732, 2), (key2732, -1), (key2676, -1), (key2885, -1), (key2835, -1), (key2885, -1), (key2798, -1), (key2835, 2), (key2798, 2)]

def rawRow6653 : Integer.Sparse Key := [(key2702, 1), (key2702, 1), (key2728, -2), (key2628, 1), (key2628, 1), (key2972, -2), (key2972, -2), (key2983, 1), (key2983, 1), (key2641, -2), (key2976, 1), (key2976, 1), (key2667, -1), (key2667, -1), (key2747, 1), (key2747, 1), (key2612, -1), (key2616, -1), (key2829, 1), (key2829, 1), (key2726, 1), (key2726, 1), (key3030, -1), (key3030, -1), (key2660, 1), (key2660, 1), (key2927, -1), (key2927, -1), (key2676, 2), (key2798, -1), (key2798, -1), (key2621, 2), (key2835, -1), (key2835, -1), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, 2), (key2885, 2)]

def rawRow6654 : Integer.Sparse Key := [(key2702, 1), (key2728, 1), (key2702, -2), (key2972, 1), (key2983, 1), (key2628, -2), (key2983, -2), (key2628, 1), (key2972, 1), (key2976, -2), (key2641, 1), (key2976, 1), (key2735, -1), (key2747, -1), (key2667, 1), (key2735, 1), (key2948, -1), (key2960, -1), (key2612, 1), (key2960, 1), (key2640, 1), (key3030, 1), (key2640, -1), (key2726, -1), (key2758, 1), (key2927, 1), (key2660, -1), (key2758, -1), (key2798, 2), (key2676, -1), (key2798, -1), (key2835, 2), (key2621, -1), (key2835, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, 2), (key2732, 2)]

def rawRow6655 : Integer.Sparse Key := [(key2728, 1), (key2702, 1), (key2702, -2), (key2983, 1), (key2972, 1), (key2983, -2), (key2628, -2), (key2972, 1), (key2628, 1), (key2976, -2), (key2976, 1), (key2641, 1), (key2747, -1), (key2735, -1), (key2735, 1), (key2667, 1), (key2960, -1), (key2948, -1), (key2960, 1), (key2612, 1), (key3030, 1), (key2640, 1), (key2726, -1), (key2640, -1), (key2927, 1), (key2758, 1), (key2758, -1), (key2660, -1), (key2798, 2), (key2798, -1), (key2676, -1), (key2835, 2), (key2835, -1), (key2621, -1), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, 2), (key2644, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow6656 : Integer.Sparse Key := [(key2972, 1), (key2976, 1), (key2983, -2), (key2628, 1), (key2641, 1), (key2702, -2), (key2976, -2), (key2728, 1), (key2983, 1), (key2628, -2), (key2702, 1), (key2972, 1), (key2936, -1), (key2943, -1), (key2960, 1), (key3000, 1), (key2646, -1), (key2653, -1), (key2735, 1), (key2998, 1), (key2667, 1), (key2943, 1), (key2747, -1), (key2960, -1), (key2616, 1), (key2640, 1), (key2794, -1), (key2829, -1), (key2732, 2), (key2835, -1), (key2885, -1), (key2644, 2), (key2798, -1), (key2885, -1), (key2621, -1), (key2644, -1), (key2676, -1), (key2732, -1), (key2798, 2), (key2835, 2)]

def rawRow6657 : Integer.Sparse Key := [(key2976, 1), (key2972, 1), (key2983, -2), (key2641, 1), (key2628, 1), (key2976, -2), (key2702, -2), (key2983, 1), (key2728, 1), (key2628, -2), (key2972, 1), (key2702, 1), (key2943, -1), (key2936, -1), (key3000, 1), (key2960, 1), (key2653, -1), (key2646, -1), (key2998, 1), (key2735, 1), (key2943, 1), (key2667, 1), (key2960, -1), (key2747, -1), (key2640, 1), (key2616, 1), (key2829, -1), (key2794, -1), (key2732, 2), (key2885, -1), (key2835, -1), (key2644, 2), (key2885, -1), (key2798, -1), (key2644, -1), (key2621, -1), (key2732, -1), (key2676, -1), (key2835, 2), (key2798, 2)]

def rawRow6658 : Integer.Sparse Key := [(key2972, 1), (key2983, 1), (key2976, -2), (key2702, 1), (key2728, 1), (key2628, -2), (key2983, -2), (key2641, 1), (key2976, 1), (key2702, -2), (key2628, 1), (key2972, 1), (key2948, -1), (key2960, -1), (key2943, 1), (key2998, 1), (key2735, -1), (key2747, -1), (key2646, 1), (key3000, 1), (key2612, 1), (key2960, 1), (key2653, -1), (key2943, -1), (key2671, 1), (key2794, 1), (key2640, -1), (key2726, -1), (key2835, 2), (key2732, -1), (key2885, -1), (key2798, 2), (key2644, -1), (key2885, -1), (key2676, -1), (key2798, -1), (key2621, -1), (key2835, -1), (key2644, 2), (key2732, 2)]

def rawRow6659 : Integer.Sparse Key := [(key2983, 1), (key2972, 1), (key2976, -2), (key2728, 1), (key2702, 1), (key2983, -2), (key2628, -2), (key2976, 1), (key2641, 1), (key2702, -2), (key2972, 1), (key2628, 1), (key2960, -1), (key2948, -1), (key2998, 1), (key2943, 1), (key2747, -1), (key2735, -1), (key3000, 1), (key2646, 1), (key2960, 1), (key2612, 1), (key2943, -1), (key2653, -1), (key2794, 1), (key2671, 1), (key2726, -1), (key2640, -1), (key2835, 2), (key2885, -1), (key2732, -1), (key2798, 2), (key2885, -1), (key2644, -1), (key2798, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2732, 2), (key2644, 2)]

def rawRow6660 : Integer.Sparse Key := [(key2976, 1), (key2983, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2641, -2), (key2728, -2), (key2628, 1), (key2702, 1), (key2972, -2), (key2628, 1), (key2702, 1), (key2998, -1), (key3000, -1), (key2936, 1), (key2948, 1), (key2998, -1), (key3000, -1), (key2653, 1), (key2747, 1), (key2653, 1), (key2747, 1), (key2612, -1), (key2667, -1), (key2726, 1), (key2829, 1), (key2616, -1), (key2671, -1), (key2885, 2), (key2732, -1), (key2835, -1), (key2885, 2), (key2644, -1), (key2798, -1), (key2732, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2621, 2), (key2676, 2)]

def rawRow6661 : Integer.Sparse Key := [(key2983, 1), (key2976, 1), (key2972, -2), (key2983, 1), (key2976, 1), (key2728, -2), (key2641, -2), (key2702, 1), (key2628, 1), (key2972, -2), (key2702, 1), (key2628, 1), (key3000, -1), (key2998, -1), (key2948, 1), (key2936, 1), (key3000, -1), (key2998, -1), (key2747, 1), (key2653, 1), (key2747, 1), (key2653, 1), (key2667, -1), (key2612, -1), (key2829, 1), (key2726, 1), (key2671, -1), (key2616, -1), (key2885, 2), (key2835, -1), (key2732, -1), (key2885, 2), (key2798, -1), (key2644, -1), (key2835, -1), (key2732, -1), (key2798, -1), (key2644, -1), (key2676, 2), (key2621, 2)]

def rawRow6662 : Integer.Sparse Key := [(key2646, 1), (key2648, 1), (key2653, -2), (key2735, 1), (key2737, 1), (key2893, -2), (key2997, -2), (key2897, 1), (key2998, 1), (key2747, -2), (key2904, 1), (key3000, 1), (key2612, -1), (key2618, -1), (key2641, 1), (key2653, 1), (key2667, -1), (key2673, -1), (key2782, 1), (key2938, 1), (key2805, 1), (key2950, 1), (key2897, -1), (key2976, -1), (key2728, 1), (key2747, 1), (key2904, -1), (key2983, -1), (key2616, 2), (key2632, -1), (key2640, -1), (key2671, 2), (key2706, -1), (key2726, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2829, -1), (key2860, 2), (key2870, 2)]

def rawRow6663 : Integer.Sparse Key := [(key2648, 1), (key2646, 1), (key2653, -2), (key2737, 1), (key2735, 1), (key2997, -2), (key2893, -2), (key2998, 1), (key2897, 1), (key2747, -2), (key3000, 1), (key2904, 1), (key2618, -1), (key2612, -1), (key2653, 1), (key2641, 1), (key2673, -1), (key2667, -1), (key2938, 1), (key2782, 1), (key2950, 1), (key2805, 1), (key2976, -1), (key2897, -1), (key2747, 1), (key2728, 1), (key2983, -1), (key2904, -1), (key2616, 2), (key2640, -1), (key2632, -1), (key2671, 2), (key2726, -1), (key2706, -1), (key2794, -1), (key2786, -1), (key2829, -1), (key2809, -1), (key2870, 2), (key2860, 2)]

def rawRow6664 : Integer.Sparse Key := [(key2648, 1), (key2653, 1), (key2646, -2), (key2997, 1), (key2998, 1), (key2737, -2), (key2897, -2), (key2735, 1), (key2893, 1), (key3000, -2), (key2747, 1), (key2904, 1), (key2648, -1), (key2653, -1), (key2612, 1), (key2628, 1), (key2938, -1), (key2943, -1), (key2673, 1), (key2795, 1), (key2737, 1), (key2897, 1), (key2702, -1), (key2805, -1), (key2960, 1), (key2983, 1), (key2728, -1), (key2831, -1), (key2640, 2), (key2616, -1), (key2632, -1), (key2726, 2), (key2671, -1), (key2706, -1), (key2829, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2786, 2), (key2809, 2)]

def rawRow6665 : Integer.Sparse Key := [(key2653, 1), (key2648, 1), (key2646, -2), (key2998, 1), (key2997, 1), (key2897, -2), (key2737, -2), (key2893, 1), (key2735, 1), (key3000, -2), (key2904, 1), (key2747, 1), (key2653, -1), (key2648, -1), (key2628, 1), (key2612, 1), (key2943, -1), (key2938, -1), (key2795, 1), (key2673, 1), (key2897, 1), (key2737, 1), (key2805, -1), (key2702, -1), (key2983, 1), (key2960, 1), (key2831, -1), (key2728, -1), (key2640, 2), (key2632, -1), (key2616, -1), (key2726, 2), (key2706, -1), (key2671, -1), (key2870, -1), (key2829, -1), (key2860, -1), (key2794, -1), (key2809, 2), (key2786, 2)]

def rawRow6666 : Integer.Sparse Key := [(key2735, 1), (key2737, 1), (key2747, -2), (key2646, 1), (key2648, 1), (key2893, -2), (key2997, -2), (key2904, 1), (key3000, 1), (key2653, -2), (key2897, 1), (key2998, 1), (key2667, -1), (key2673, -1), (key2728, 1), (key2747, 1), (key2612, -1), (key2618, -1), (key2805, 1), (key2950, 1), (key2782, 1), (key2938, 1), (key2904, -1), (key2983, -1), (key2641, 1), (key2653, 1), (key2897, -1), (key2976, -1), (key2671, 2), (key2786, -1), (key2794, -1), (key2616, 2), (key2809, -1), (key2829, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, 2), (key2870, 2)]

def rawRow6667 : Integer.Sparse Key := [(key2737, 1), (key2735, 1), (key2747, -2), (key2648, 1), (key2646, 1), (key2997, -2), (key2893, -2), (key3000, 1), (key2904, 1), (key2653, -2), (key2998, 1), (key2897, 1), (key2673, -1), (key2667, -1), (key2747, 1), (key2728, 1), (key2618, -1), (key2612, -1), (key2950, 1), (key2805, 1), (key2938, 1), (key2782, 1), (key2983, -1), (key2904, -1), (key2653, 1), (key2641, 1), (key2976, -1), (key2897, -1), (key2671, 2), (key2794, -1), (key2786, -1), (key2616, 2), (key2829, -1), (key2809, -1), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, 2), (key2860, 2)]

def rawRow6668 : Integer.Sparse Key := [(key2735, 1), (key2747, 1), (key2737, -2), (key2893, 1), (key2904, 1), (key2646, -2), (key3000, -2), (key2648, 1), (key2997, 1), (key2897, -2), (key2653, 1), (key2998, 1), (key2702, -1), (key2728, -1), (key2673, 1), (key2737, 1), (key2805, -1), (key2831, -1), (key2612, 1), (key2960, 1), (key2628, 1), (key2983, 1), (key2648, -1), (key2938, -1), (key2795, 1), (key2897, 1), (key2653, -1), (key2943, -1), (key2786, 2), (key2671, -1), (key2794, -1), (key2809, 2), (key2616, -1), (key2829, -1), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, 2), (key2726, 2)]

def rawRow6669 : Integer.Sparse Key := [(key2747, 1), (key2735, 1), (key2737, -2), (key2904, 1), (key2893, 1), (key3000, -2), (key2646, -2), (key2997, 1), (key2648, 1), (key2897, -2), (key2998, 1), (key2653, 1), (key2728, -1), (key2702, -1), (key2737, 1), (key2673, 1), (key2831, -1), (key2805, -1), (key2960, 1), (key2612, 1), (key2983, 1), (key2628, 1), (key2938, -1), (key2648, -1), (key2897, 1), (key2795, 1), (key2943, -1), (key2653, -1), (key2786, 2), (key2794, -1), (key2671, -1), (key2809, 2), (key2829, -1), (key2616, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, 2), (key2640, 2)]

def rawRow6670 : Integer.Sparse Key := [(key2893, 1), (key2904, 1), (key2897, -2), (key2735, 1), (key2747, 1), (key2646, -2), (key3000, -2), (key2653, 1), (key2998, 1), (key2737, -2), (key2648, 1), (key2997, 1), (key2805, -1), (key2831, -1), (key2795, 1), (key2897, 1), (key2702, -1), (key2728, -1), (key2628, 1), (key2983, 1), (key2612, 1), (key2960, 1), (key2653, -1), (key2943, -1), (key2673, 1), (key2737, 1), (key2648, -1), (key2938, -1), (key2809, 2), (key2706, -1), (key2860, -1), (key2786, 2), (key2632, -1), (key2870, -1), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, 2), (key2726, 2)]

def rawRow6671 : Integer.Sparse Key := [(key2904, 1), (key2893, 1), (key2897, -2), (key2747, 1), (key2735, 1), (key3000, -2), (key2646, -2), (key2998, 1), (key2653, 1), (key2737, -2), (key2997, 1), (key2648, 1), (key2831, -1), (key2805, -1), (key2897, 1), (key2795, 1), (key2728, -1), (key2702, -1), (key2983, 1), (key2628, 1), (key2960, 1), (key2612, 1), (key2943, -1), (key2653, -1), (key2737, 1), (key2673, 1), (key2938, -1), (key2648, -1), (key2809, 2), (key2860, -1), (key2706, -1), (key2786, 2), (key2870, -1), (key2632, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, 2), (key2640, 2)]

def rawRow6672 : Integer.Sparse Key := [(key2897, 1), (key2904, 1), (key2893, -2), (key2998, 1), (key3000, 1), (key2653, -2), (key2747, -2), (key2646, 1), (key2735, 1), (key2997, -2), (key2648, 1), (key2737, 1), (key2897, -1), (key2904, -1), (key2782, 1), (key2805, 1), (key2976, -1), (key2983, -1), (key2641, 1), (key2728, 1), (key2653, 1), (key2747, 1), (key2612, -1), (key2667, -1), (key2938, 1), (key2950, 1), (key2618, -1), (key2673, -1), (key2860, 2), (key2706, -1), (key2809, -1), (key2870, 2), (key2632, -1), (key2786, -1), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, 2), (key2671, 2)]

def rawRow6673 : Integer.Sparse Key := [(key2904, 1), (key2897, 1), (key2893, -2), (key3000, 1), (key2998, 1), (key2747, -2), (key2653, -2), (key2735, 1), (key2646, 1), (key2997, -2), (key2737, 1), (key2648, 1), (key2904, -1), (key2897, -1), (key2805, 1), (key2782, 1), (key2983, -1), (key2976, -1), (key2728, 1), (key2641, 1), (key2747, 1), (key2653, 1), (key2667, -1), (key2612, -1), (key2950, 1), (key2938, 1), (key2673, -1), (key2618, -1), (key2860, 2), (key2809, -1), (key2706, -1), (key2870, 2), (key2786, -1), (key2632, -1), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, 2), (key2616, 2)]

def rawRow6674 : Integer.Sparse Key := [(key2997, 1), (key2998, 1), (key3000, -2), (key2648, 1), (key2653, 1), (key2737, -2), (key2897, -2), (key2747, 1), (key2904, 1), (key2646, -2), (key2735, 1), (key2893, 1), (key2938, -1), (key2943, -1), (key2960, 1), (key2983, 1), (key2648, -1), (key2653, -1), (key2737, 1), (key2897, 1), (key2673, 1), (key2795, 1), (key2728, -1), (key2831, -1), (key2612, 1), (key2628, 1), (key2702, -1), (key2805, -1), (key2726, 2), (key2829, -1), (key2870, -1), (key2640, 2), (key2794, -1), (key2860, -1), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, 2), (key2809, 2)]

def rawRow6675 : Integer.Sparse Key := [(key2998, 1), (key2997, 1), (key3000, -2), (key2653, 1), (key2648, 1), (key2897, -2), (key2737, -2), (key2904, 1), (key2747, 1), (key2646, -2), (key2893, 1), (key2735, 1), (key2943, -1), (key2938, -1), (key2983, 1), (key2960, 1), (key2653, -1), (key2648, -1), (key2897, 1), (key2737, 1), (key2795, 1), (key2673, 1), (key2831, -1), (key2728, -1), (key2628, 1), (key2612, 1), (key2805, -1), (key2702, -1), (key2726, 2), (key2870, -1), (key2829, -1), (key2640, 2), (key2860, -1), (key2794, -1), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, 2), (key2786, 2)]

def rawRow6676 : Integer.Sparse Key := [(key2998, 1), (key3000, 1), (key2997, -2), (key2897, 1), (key2904, 1), (key2653, -2), (key2747, -2), (key2648, 1), (key2737, 1), (key2893, -2), (key2646, 1), (key2735, 1), (key2976, -1), (key2983, -1), (key2938, 1), (key2950, 1), (key2897, -1), (key2904, -1), (key2653, 1), (key2747, 1), (key2641, 1), (key2728, 1), (key2618, -1), (key2673, -1), (key2782, 1), (key2805, 1), (key2612, -1), (key2667, -1), (key2870, 2), (key2726, -1), (key2829, -1), (key2860, 2), (key2640, -1), (key2794, -1), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, 2), (key2671, 2)]

def rawRow6677 : Integer.Sparse Key := [(key3000, 1), (key2998, 1), (key2997, -2), (key2904, 1), (key2897, 1), (key2747, -2), (key2653, -2), (key2737, 1), (key2648, 1), (key2893, -2), (key2735, 1), (key2646, 1), (key2983, -1), (key2976, -1), (key2950, 1), (key2938, 1), (key2904, -1), (key2897, -1), (key2747, 1), (key2653, 1), (key2728, 1), (key2641, 1), (key2673, -1), (key2618, -1), (key2805, 1), (key2782, 1), (key2667, -1), (key2612, -1), (key2870, 2), (key2829, -1), (key2726, -1), (key2860, 2), (key2794, -1), (key2640, -1), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, 2), (key2616, 2)]

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

def rawRow8833 : Integer.Sparse Key := [(key2353, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2566, -6), (key2566, -6), (key2566, -6), (key2578, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1003 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end


