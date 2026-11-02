-- Prove2me | Definitions.Def_OAIQ106D185
-- name    : OAIQ106D185
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:47:10.573355+00:00
-- url     : https://prove2.me/theorems/000e1dbc-7517-467d-ab29-f65c3ce959db
-- title:
--   Definitions bundle OAIQ106D185 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 709 declarations of OpenAI's Lean: 709 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow8656`, `OAI.MUB6.Certificate.GramRows.rawRow8657`, `OAI.MUB6.Certificate.GramRows.rawRow8658`, `OAI.MUB6.Certificate.GramRows.rawRow8659`, `OAI.MUB6.Certificate.GramRows.rawRow8660`, `OAI.MUB6.Certificate.GramRows.rawRow8661`, `OAI.MUB6.Certificate.GramRows.rawRow8662`, `OAI.MUB6.Certificate.GramRows.rawRow8663`, `OAI.MUB6.Certificate.GramRows.rawRow8664`, `OAI.MUB6.Certificate.GramRows.rawRow8665`, `OAI.MUB6.Certificate.GramRows.rawRow8666`, `OAI.MUB6.Certificate.GramRows.rawRow8667`, `OAI.MUB6.Certificate.GramRows.rawRow8668`, `OAI.MUB6.Certificate.GramRows.rawRow867`, `OAI.MUB6.Certificate.GramRows.rawRow8670`, `OAI.MUB6.Certificate.GramRows.rawRow8671`, `OAI.MUB6.Certificate.GramRows.rawRow8672`, `OAI.MUB6.Certificate.GramRows.rawRow8673`, `OAI.MUB6.Certificate.GramRows.rawRow8674`, `OAI.MUB6.Certificate.GramRows.rawRow8675`, `OAI.MUB6.Certificate.GramRows.rawRow8676`, `OAI.MUB6.Certificate.GramRows.rawRow8677`, `OAI.MUB6.Certificate.GramRows.rawRow8678`, `OAI.MUB6.Certificate.GramRows.rawRow8679`, `OAI.MUB6.Certificate.GramRows.rawRow868`, `OAI.MUB6.Certificate.GramRows.rawRow8680`, `OAI.MUB6.Certificate.GramRows.rawRow8681`, `OAI.MUB6.Certificate.GramRows.rawRow8682`, `OAI.MUB6.Certificate.GramRows.rawRow8683`, `OAI.MUB6.Certificate.GramRows.rawRow8684`, `OAI.MUB6.Certificate.GramRows.rawRow8685`, `OAI.MUB6.Certificate.GramRows.rawRow8686`, `OAI.MUB6.Certificate.GramRows.rawRow8687`, `OAI.MUB6.Certificate.GramRows.rawRow8688`, `OAI.MUB6.Certificate.GramRows.rawRow8689`, `OAI.MUB6.Certificate.GramRows.rawRow869`, `OAI.MUB6.Certificate.GramRows.rawRow8690`, `OAI.MUB6.Certificate.GramRows.rawRow8691`, `OAI.MUB6.Certificate.GramRows.rawRow8692`, `OAI.MUB6.Certificate.GramRows.rawRow8693` and 669 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block24`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block24.lean), [`MutuallyUnbiased_GramRows_Block25`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block25.lean), [`MutuallyUnbiased_GramRows_Block26`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block26.lean), [`MutuallyUnbiased_GramRows_Block91`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block91.lean), [`MutuallyUnbiased_GramRows_Block92`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block92.lean), [`MutuallyUnbiased_GramRows_Block93`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block93.lean), [`MutuallyUnbiased_GramRows_Block94`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block94.lean), [`MutuallyUnbiased_GramRows_Block95`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block95.lean), [`MutuallyUnbiased_GramRows_Block96`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block96.lean), [`MutuallyUnbiased_GramRows_Block97`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block97.lean), [`MutuallyUnbiased_TaoCertificate_Merge30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge30.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D080`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D094` and `OAIQ106D140` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D200`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D089
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D094
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

def rawRow9 : Integer.Sparse Key := [(key271, -1), (key267, -1), (key267, 2), (key260, 1), (key251, 1), (key251, -1), (key239, -1), (key248, -2), (key248, 1), (key236, 1), (key340, 1), (key328, 1), (key328, -2), (key335, -1), (key319, -1), (key319, 1), (key305, 1), (key316, 2), (key316, -1), (key302, -1), (key475, -1), (key450, -1), (key450, 1), (key418, 1), (key469, 1), (key442, 1), (key442, -1), (key397, -1), (key435, -1), (key406, -1), (key435, 1), (key385, 1), (key601, 2), (key601, -1), (key583, -1), (key595, -2), (key595, 1), (key572, 1), (key593, 1), (key578, 1), (key593, -1), (key568, -1)]

def rawRow88 : Integer.Sparse Key := [(key2643, -2), (key2633, 1), (key2643, 1), (key2655, 2), (key2617, -1), (key2655, -1), (key2643, -1), (key2656, -1), (key2620, 1), (key2656, 1), (key2739, 2), (key2707, -1), (key2739, -1), (key2749, -2), (key2672, 1), (key2749, 1), (key2730, 1), (key2751, 1), (key2675, -1), (key2751, -1), (key2899, -2), (key2810, 1), (key2899, 1), (key2906, 2), (key2787, -1), (key2906, -1), (key2833, -1), (key2915, -1), (key2797, 1), (key2915, 1), (key2978, 1), (key2999, 1), (key2952, -1), (key2999, -1), (key2985, -1), (key3001, -1), (key2940, 1), (key3001, 1), (key2962, 1), (key3004, 1), (key2945, -1), (key3004, -1)]

def rawRow89 : Integer.Sparse Key := [(key2643, -2), (key2643, 1), (key2633, 1), (key2655, 2), (key2655, -1), (key2617, -1), (key2656, -1), (key2643, -1), (key2656, 1), (key2620, 1), (key2739, 2), (key2739, -1), (key2707, -1), (key2749, -2), (key2749, 1), (key2672, 1), (key2751, 1), (key2730, 1), (key2751, -1), (key2675, -1), (key2899, -2), (key2899, 1), (key2810, 1), (key2906, 2), (key2906, -1), (key2787, -1), (key2915, -1), (key2833, -1), (key2915, 1), (key2797, 1), (key2999, 1), (key2978, 1), (key2999, -1), (key2952, -1), (key3001, -1), (key2985, -1), (key3001, 1), (key2940, 1), (key3004, 1), (key2962, 1), (key3004, -1), (key2945, -1)]

def rawRow90 : Integer.Sparse Key := [(key2650, -2), (key2655, 1), (key2656, 1), (key2620, 2), (key2643, -1), (key2656, -1), (key2617, -1), (key2620, -1), (key2633, 1), (key2643, 1), (key2730, 2), (key2749, -1), (key2751, -1), (key2675, -2), (key2739, 1), (key2751, 1), (key2672, 1), (key2675, 1), (key2707, -1), (key2730, -1), (key2833, -2), (key2906, 1), (key2915, 1), (key2797, 2), (key2899, -1), (key2915, -1), (key2787, -1), (key2797, -1), (key2810, 1), (key2833, 1), (key2962, 1), (key2964, 1), (key2985, -1), (key2994, -1), (key2945, -1), (key2946, -1), (key2978, 1), (key2994, 1), (key2940, 1), (key2946, 1), (key2952, -1), (key2964, -1)]

def rawRow91 : Integer.Sparse Key := [(key2650, -2), (key2656, 1), (key2655, 1), (key2620, 2), (key2656, -1), (key2643, -1), (key2620, -1), (key2617, -1), (key2643, 1), (key2633, 1), (key2730, 2), (key2751, -1), (key2749, -1), (key2675, -2), (key2751, 1), (key2739, 1), (key2675, 1), (key2672, 1), (key2730, -1), (key2707, -1), (key2833, -2), (key2915, 1), (key2906, 1), (key2797, 2), (key2915, -1), (key2899, -1), (key2797, -1), (key2787, -1), (key2833, 1), (key2810, 1), (key2964, 1), (key2962, 1), (key2994, -1), (key2985, -1), (key2946, -1), (key2945, -1), (key2994, 1), (key2978, 1), (key2946, 1), (key2940, 1), (key2964, -1), (key2952, -1)]

def rawRow92 : Integer.Sparse Key := [(key2655, -2), (key2650, 1), (key2656, 1), (key2643, 2), (key2620, -1), (key2656, -1), (key2633, -1), (key2643, -1), (key2617, 1), (key2655, 1), (key2749, 2), (key2730, -1), (key2751, -1), (key2739, -2), (key2675, 1), (key2751, 1), (key2707, 1), (key2739, 1), (key2672, -1), (key2749, -1), (key2906, -2), (key2833, 1), (key2915, 1), (key2899, 2), (key2797, -1), (key2915, -1), (key2810, -1), (key2899, -1), (key2787, 1), (key2906, 1), (key2985, 1), (key3001, 1), (key2962, -1), (key3004, -1), (key2978, -1), (key2999, -1), (key2945, 1), (key3004, 1), (key2952, 1), (key2999, 1), (key2940, -1), (key3001, -1)]

def rawRow93 : Integer.Sparse Key := [(key2655, -2), (key2656, 1), (key2650, 1), (key2643, 2), (key2656, -1), (key2620, -1), (key2643, -1), (key2633, -1), (key2655, 1), (key2617, 1), (key2749, 2), (key2751, -1), (key2730, -1), (key2739, -2), (key2751, 1), (key2675, 1), (key2739, 1), (key2707, 1), (key2749, -1), (key2672, -1), (key2906, -2), (key2915, 1), (key2833, 1), (key2899, 2), (key2915, -1), (key2797, -1), (key2899, -1), (key2810, -1), (key2906, 1), (key2787, 1), (key3001, 1), (key2985, 1), (key3004, -1), (key2962, -1), (key2999, -1), (key2978, -1), (key3004, 1), (key2945, 1), (key2999, 1), (key2952, 1), (key3001, -1), (key2940, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow867 : Integer.Sparse Key := [(key2700, -2), (key2700, -2), (key2721, -2), (key2665, 1), (key2665, 1), (key2700, 1), (key2700, 1), (key2721, 1), (key2721, 1), (key2803, 2), (key2803, 2), (key2824, 2), (key2610, -1), (key2610, -1), (key2803, -1), (key2803, -1), (key2824, -1), (key2824, -1), (key2780, -1), (key2780, -1), (key2853, -1), (key2853, -1), (key2865, -1), (key2865, -1), (key2626, 1), (key2626, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1)]

def rawRow868 : Integer.Sparse Key := [(key2700, -2), (key2721, -2), (key2700, -2), (key2700, 1), (key2721, 1), (key2665, 1), (key2721, 1), (key2665, 1), (key2700, 1), (key2803, 2), (key2824, 2), (key2803, 2), (key2803, -1), (key2824, -1), (key2610, -1), (key2824, -1), (key2610, -1), (key2803, -1), (key2853, -1), (key2865, -1), (key2780, -1), (key2865, -1), (key2780, -1), (key2853, -1), (key2853, 1), (key2865, 1), (key2626, 1), (key2865, 1), (key2626, 1), (key2853, 1)]

def rawRow869 : Integer.Sparse Key := [(key2721, -2), (key2700, -2), (key2700, -2), (key2721, 1), (key2700, 1), (key2721, 1), (key2665, 1), (key2700, 1), (key2665, 1), (key2824, 2), (key2803, 2), (key2803, 2), (key2824, -1), (key2803, -1), (key2824, -1), (key2610, -1), (key2803, -1), (key2610, -1), (key2865, -1), (key2853, -1), (key2865, -1), (key2780, -1), (key2853, -1), (key2780, -1), (key2865, 1), (key2853, 1), (key2865, 1), (key2626, 1), (key2853, 1), (key2626, 1)]

def rawRow870 : Integer.Sparse Key := [(key2780, -2), (key2780, -2), (key2789, -2), (key2803, 1), (key2803, 1), (key2853, 1), (key2853, 1), (key2855, 1), (key2855, 1), (key2626, 2), (key2626, 2), (key2635, 2), (key2700, -1), (key2700, -1), (key2853, -1), (key2853, -1), (key2855, -1), (key2855, -1), (key2610, -1), (key2610, -1), (key2626, -1), (key2626, -1), (key2635, -1), (key2635, -1), (key2665, 1), (key2665, 1), (key2780, 1), (key2780, 1), (key2789, 1), (key2789, 1)]

def rawRow871 : Integer.Sparse Key := [(key2780, -2), (key2789, -2), (key2780, -2), (key2853, 1), (key2855, 1), (key2803, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2626, 2), (key2635, 2), (key2626, 2), (key2853, -1), (key2855, -1), (key2700, -1), (key2855, -1), (key2700, -1), (key2853, -1), (key2626, -1), (key2635, -1), (key2610, -1), (key2635, -1), (key2610, -1), (key2626, -1), (key2780, 1), (key2789, 1), (key2665, 1), (key2789, 1), (key2665, 1), (key2780, 1)]

def rawRow872 : Integer.Sparse Key := [(key2789, -2), (key2780, -2), (key2780, -2), (key2855, 1), (key2853, 1), (key2855, 1), (key2803, 1), (key2853, 1), (key2803, 1), (key2635, 2), (key2626, 2), (key2626, 2), (key2855, -1), (key2853, -1), (key2855, -1), (key2700, -1), (key2853, -1), (key2700, -1), (key2635, -1), (key2626, -1), (key2635, -1), (key2610, -1), (key2626, -1), (key2610, -1), (key2789, 1), (key2780, 1), (key2789, 1), (key2665, 1), (key2780, 1), (key2665, 1)]

def rawRow873 : Integer.Sparse Key := [(key2803, -2), (key2803, -2), (key2824, -2), (key2780, 1), (key2780, 1), (key2853, 1), (key2853, 1), (key2865, 1), (key2865, 1), (key2700, 2), (key2700, 2), (key2721, 2), (key2626, -1), (key2626, -1), (key2853, -1), (key2853, -1), (key2865, -1), (key2865, -1), (key2665, -1), (key2665, -1), (key2700, -1), (key2700, -1), (key2721, -1), (key2721, -1), (key2610, 1), (key2610, 1), (key2803, 1), (key2803, 1), (key2824, 1), (key2824, 1)]

def rawRow874 : Integer.Sparse Key := [(key2803, -2), (key2824, -2), (key2803, -2), (key2853, 1), (key2865, 1), (key2780, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2700, 2), (key2721, 2), (key2700, 2), (key2853, -1), (key2865, -1), (key2626, -1), (key2865, -1), (key2626, -1), (key2853, -1), (key2700, -1), (key2721, -1), (key2665, -1), (key2721, -1), (key2665, -1), (key2700, -1), (key2803, 1), (key2824, 1), (key2610, 1), (key2824, 1), (key2610, 1), (key2803, 1)]

def rawRow875 : Integer.Sparse Key := [(key2824, -2), (key2803, -2), (key2803, -2), (key2865, 1), (key2853, 1), (key2865, 1), (key2780, 1), (key2853, 1), (key2780, 1), (key2721, 2), (key2700, 2), (key2700, 2), (key2865, -1), (key2853, -1), (key2865, -1), (key2626, -1), (key2853, -1), (key2626, -1), (key2721, -1), (key2700, -1), (key2721, -1), (key2665, -1), (key2700, -1), (key2665, -1), (key2824, 1), (key2803, 1), (key2824, 1), (key2610, 1), (key2803, 1), (key2610, 1)]

def rawRow877 : Integer.Sparse Key := [(key995, -2), (key995, -2), (key1011, -2), (key995, 6), (key1108, 2), (key1108, 2), (key1119, 2), (key1030, -2), (key1108, -2), (key1108, -2), (key1146, -6), (key1067, 2), (key1146, 2), (key1146, 2)]

def rawRow878 : Integer.Sparse Key := [(key995, -2), (key1011, -2), (key995, -2), (key995, 6), (key1108, 2), (key1119, 2), (key1108, 2), (key1108, -2), (key1030, -2), (key1108, -2), (key1146, -6), (key1146, 2), (key1067, 2), (key1146, 2)]

def rawRow879 : Integer.Sparse Key := [(key1011, -2), (key995, -2), (key995, -2), (key995, 6), (key1119, 2), (key1108, 2), (key1108, 2), (key1108, -2), (key1108, -2), (key1030, -2), (key1146, -6), (key1146, 2), (key1146, 2), (key1067, 2)]

def rawRow881 : Integer.Sparse Key := [(key1030, -2), (key1030, -2), (key1067, -2), (key1030, 6), (key1108, 2), (key1108, 2), (key1146, 2), (key995, -2), (key1108, -2), (key1108, -2), (key1119, -6), (key1011, 2), (key1119, 2), (key1119, 2)]

def rawRow882 : Integer.Sparse Key := [(key1030, -2), (key1067, -2), (key1030, -2), (key1030, 6), (key1108, 2), (key1146, 2), (key1108, 2), (key1108, -2), (key995, -2), (key1108, -2), (key1119, -6), (key1119, 2), (key1011, 2), (key1119, 2)]

def rawRow883 : Integer.Sparse Key := [(key1067, -2), (key1030, -2), (key1030, -2), (key1030, 6), (key1146, 2), (key1108, 2), (key1108, 2), (key1108, -2), (key1108, -2), (key995, -2), (key1119, -6), (key1119, 2), (key1119, 2), (key1011, 2)]

def rawRow884 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1119, -2), (key1146, 6), (key995, 2), (key995, 2), (key1011, 2), (key1067, -2), (key1146, -2), (key1146, -2), (key995, -6), (key1030, 2), (key1108, 2), (key1108, 2)]

def rawRow885 : Integer.Sparse Key := [(key1108, -2), (key1119, -2), (key1108, -2), (key1146, 6), (key995, 2), (key1011, 2), (key995, 2), (key1146, -2), (key1067, -2), (key1146, -2), (key995, -6), (key1108, 2), (key1030, 2), (key1108, 2)]

def rawRow886 : Integer.Sparse Key := [(key1119, -2), (key1108, -2), (key1108, -2), (key1146, 6), (key1011, 2), (key995, 2), (key995, 2), (key1146, -2), (key1146, -2), (key1067, -2), (key995, -6), (key1108, 2), (key1108, 2), (key1030, 2)]

def rawRow887 : Integer.Sparse Key := [(key1108, -2), (key1108, -2), (key1146, -2), (key1119, 6), (key1030, 2), (key1030, 2), (key1067, 2), (key1011, -2), (key1119, -2), (key1119, -2), (key1030, -6), (key995, 2), (key1108, 2), (key1108, 2)]

def rawRow888 : Integer.Sparse Key := [(key1108, -2), (key1146, -2), (key1108, -2), (key1119, 6), (key1030, 2), (key1067, 2), (key1030, 2), (key1119, -2), (key1011, -2), (key1119, -2), (key1030, -6), (key1108, 2), (key995, 2), (key1108, 2)]

def rawRow889 : Integer.Sparse Key := [(key1146, -2), (key1108, -2), (key1108, -2), (key1119, 6), (key1067, 2), (key1030, 2), (key1030, 2), (key1119, -2), (key1119, -2), (key1011, -2), (key1030, -6), (key1108, 2), (key1108, 2), (key995, 2)]

def rawRow891 : Integer.Sparse Key := [(key2622, -6), (key2606, 2), (key2622, 2), (key2622, 2), (key2696, 6), (key2661, -2), (key2696, -2), (key2696, -2), (key2799, -2), (key2849, -2), (key2849, -2), (key2776, 2), (key2849, 2), (key2849, 2)]

def rawRow892 : Integer.Sparse Key := [(key2622, -6), (key2622, 2), (key2606, 2), (key2622, 2), (key2696, 6), (key2696, -2), (key2661, -2), (key2696, -2), (key2849, -2), (key2799, -2), (key2849, -2), (key2849, 2), (key2776, 2), (key2849, 2)]

def rawRow893 : Integer.Sparse Key := [(key2622, -6), (key2622, 2), (key2622, 2), (key2606, 2), (key2696, 6), (key2696, -2), (key2696, -2), (key2661, -2), (key2849, -2), (key2849, -2), (key2799, -2), (key2849, 2), (key2849, 2), (key2776, 2)]

def rawRow895 : Integer.Sparse Key := [(key2696, -6), (key2661, 2), (key2696, 2), (key2696, 2), (key2799, 6), (key2606, -2), (key2799, -2), (key2799, -2), (key2696, -2), (key2849, -2), (key2849, -2), (key2622, 2), (key2849, 2), (key2849, 2)]

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

def rawRow896 : Integer.Sparse Key := [(key2696, -6), (key2696, 2), (key2661, 2), (key2696, 2), (key2799, 6), (key2799, -2), (key2606, -2), (key2799, -2), (key2849, -2), (key2696, -2), (key2849, -2), (key2849, 2), (key2622, 2), (key2849, 2)]

def rawRow897 : Integer.Sparse Key := [(key2696, -6), (key2696, 2), (key2696, 2), (key2661, 2), (key2799, 6), (key2799, -2), (key2799, -2), (key2606, -2), (key2849, -2), (key2849, -2), (key2696, -2), (key2849, 2), (key2849, 2), (key2622, 2)]

def rawRow898 : Integer.Sparse Key := [(key2776, -6), (key2799, 2), (key2849, 2), (key2849, 2), (key2622, 6), (key2696, -2), (key2849, -2), (key2849, -2), (key2606, -2), (key2622, -2), (key2622, -2), (key2661, 2), (key2696, 2), (key2696, 2)]

def rawRow899 : Integer.Sparse Key := [(key2776, -6), (key2849, 2), (key2799, 2), (key2849, 2), (key2622, 6), (key2849, -2), (key2696, -2), (key2849, -2), (key2622, -2), (key2606, -2), (key2622, -2), (key2696, 2), (key2661, 2), (key2696, 2)]

def rawRow900 : Integer.Sparse Key := [(key2776, -6), (key2849, 2), (key2849, 2), (key2799, 2), (key2622, 6), (key2849, -2), (key2849, -2), (key2696, -2), (key2622, -2), (key2622, -2), (key2606, -2), (key2696, 2), (key2696, 2), (key2661, 2)]

def rawRow901 : Integer.Sparse Key := [(key2799, -6), (key2776, 2), (key2849, 2), (key2849, 2), (key2696, 6), (key2622, -2), (key2849, -2), (key2849, -2), (key2661, -2), (key2696, -2), (key2696, -2), (key2606, 2), (key2799, 2), (key2799, 2)]

def rawRow902 : Integer.Sparse Key := [(key2799, -6), (key2849, 2), (key2776, 2), (key2849, 2), (key2696, 6), (key2849, -2), (key2622, -2), (key2849, -2), (key2696, -2), (key2661, -2), (key2696, -2), (key2799, 2), (key2606, 2), (key2799, 2)]

def rawRow903 : Integer.Sparse Key := [(key2799, -6), (key2849, 2), (key2849, 2), (key2776, 2), (key2696, 6), (key2849, -2), (key2849, -2), (key2622, -2), (key2696, -2), (key2696, -2), (key2661, -2), (key2799, 2), (key2799, 2), (key2606, 2)]

def rawRow904 : Integer.Sparse Key := [(key1296, -2), (key1788, -2), (key1799, -2), (key1296, 1), (key1303, 1), (key1573, 1), (key1597, 1), (key1791, 1), (key1799, 1), (key1316, 2), (key1813, 2), (key1826, 2), (key1316, -1), (key1330, -1), (key1424, -1), (key1448, -1), (key1818, -1), (key1826, -1), (key1337, -1), (key1340, -1), (key1655, -1), (key1668, -1), (key1840, -1), (key1845, -1), (key1337, 1), (key1346, 1), (key1455, 1), (key1467, 1), (key1842, 1), (key1845, 1)]

def rawRow905 : Integer.Sparse Key := [(key1296, -2), (key1799, -2), (key1788, -2), (key1303, 1), (key1296, 1), (key1597, 1), (key1573, 1), (key1799, 1), (key1791, 1), (key1316, 2), (key1826, 2), (key1813, 2), (key1330, -1), (key1316, -1), (key1448, -1), (key1424, -1), (key1826, -1), (key1818, -1), (key1340, -1), (key1337, -1), (key1668, -1), (key1655, -1), (key1845, -1), (key1840, -1), (key1346, 1), (key1337, 1), (key1467, 1), (key1455, 1), (key1845, 1), (key1842, 1)]

def rawRow906 : Integer.Sparse Key := [(key1788, -2), (key1296, -2), (key1799, -2), (key1573, 1), (key1791, 1), (key1296, 1), (key1799, 1), (key1303, 1), (key1597, 1), (key1813, 2), (key1316, 2), (key1826, 2), (key1424, -1), (key1818, -1), (key1316, -1), (key1826, -1), (key1330, -1), (key1448, -1), (key1655, -1), (key1840, -1), (key1337, -1), (key1845, -1), (key1340, -1), (key1668, -1), (key1455, 1), (key1842, 1), (key1337, 1), (key1845, 1), (key1346, 1), (key1467, 1)]

def rawRow907 : Integer.Sparse Key := [(key1788, -2), (key1799, -2), (key1296, -2), (key1791, 1), (key1573, 1), (key1799, 1), (key1296, 1), (key1597, 1), (key1303, 1), (key1813, 2), (key1826, 2), (key1316, 2), (key1818, -1), (key1424, -1), (key1826, -1), (key1316, -1), (key1448, -1), (key1330, -1), (key1840, -1), (key1655, -1), (key1845, -1), (key1337, -1), (key1668, -1), (key1340, -1), (key1842, 1), (key1455, 1), (key1845, 1), (key1337, 1), (key1467, 1), (key1346, 1)]

def rawRow908 : Integer.Sparse Key := [(key1799, -2), (key1296, -2), (key1788, -2), (key1597, 1), (key1799, 1), (key1303, 1), (key1791, 1), (key1296, 1), (key1573, 1), (key1826, 2), (key1316, 2), (key1813, 2), (key1448, -1), (key1826, -1), (key1330, -1), (key1818, -1), (key1316, -1), (key1424, -1), (key1668, -1), (key1845, -1), (key1340, -1), (key1840, -1), (key1337, -1), (key1655, -1), (key1467, 1), (key1845, 1), (key1346, 1), (key1842, 1), (key1337, 1), (key1455, 1)]

def rawRow909 : Integer.Sparse Key := [(key1799, -2), (key1788, -2), (key1296, -2), (key1799, 1), (key1597, 1), (key1791, 1), (key1303, 1), (key1573, 1), (key1296, 1), (key1826, 2), (key1813, 2), (key1316, 2), (key1826, -1), (key1448, -1), (key1818, -1), (key1330, -1), (key1424, -1), (key1316, -1), (key1845, -1), (key1668, -1), (key1840, -1), (key1340, -1), (key1655, -1), (key1337, -1), (key1845, 1), (key1467, 1), (key1842, 1), (key1346, 1), (key1455, 1), (key1337, 1)]

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

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8656 : Integer.Sparse Key := [(key433, -6), (key246, -6), (key433, -6), (key314, -6), (key383, 2), (key433, 2), (key404, 2), (key246, 2), (key433, 2), (key314, 2), (key246, 2), (key234, 2), (key314, 2), (key300, 2), (key404, 2), (key383, 2)]

def rawRow8657 : Integer.Sparse Key := [(key433, -6), (key314, -6), (key246, -6), (key433, -6), (key404, 2), (key383, 2), (key433, 2), (key314, 2), (key246, 2), (key433, 2), (key300, 2), (key314, 2), (key234, 2), (key404, 2), (key246, 2), (key314, 2)]

def rawRow8658 : Integer.Sparse Key := [(key433, -6), (key314, -6), (key433, -6), (key246, -6), (key404, 2), (key433, 2), (key383, 2), (key314, 2), (key433, 2), (key246, 2), (key314, 2), (key300, 2), (key404, 2), (key234, 2), (key314, 2), (key246, 2)]

def rawRow8659 : Integer.Sparse Key := [(key433, -6), (key433, -6), (key246, -6), (key314, -6), (key433, 2), (key383, 2), (key404, 2), (key433, 2), (key246, 2), (key314, 2), (key383, 2), (key404, 2), (key246, 2), (key314, 2), (key234, 2), (key300, 2)]

def rawRow8660 : Integer.Sparse Key := [(key433, -6), (key433, -6), (key314, -6), (key246, -6), (key433, 2), (key404, 2), (key383, 2), (key433, 2), (key314, 2), (key246, 2), (key404, 2), (key383, 2), (key314, 2), (key246, 2), (key300, 2), (key234, 2)]

def rawRow8661 : Integer.Sparse Key := [(key2456, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2531, 2), (key2459, 2), (key2531, 2), (key2517, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2561, -2)]

def rawRow8662 : Integer.Sparse Key := [(key2456, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2459, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2531, 2), (key2459, 2), (key2520, -2), (key2517, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2561, -2), (key2520, -2)]

def rawRow8663 : Integer.Sparse Key := [(key2459, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2456, 2), (key2456, 2), (key2531, 2), (key2531, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2517, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2561, -2), (key2520, -2), (key2520, -2)]

def rawRow8664 : Integer.Sparse Key := [(key2531, 2), (key2531, 2), (key2531, 2), (key2459, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2456, 2), (key2561, -2), (key2561, -2), (key2561, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2520, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

def rawRow8665 : Integer.Sparse Key := [(key2364, 2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2520, 2), (key2361, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

def rawRow8666 : Integer.Sparse Key := [(key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow8667 : Integer.Sparse Key := [(key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2364, 2), (key2459, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow8668 : Integer.Sparse Key := [(key2520, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2520, 2), (key2364, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2364, 2), (key2459, 2), (key2364, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow8670 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1083, 6), (key1177, 6), (key1083, 6)]

def rawRow8671 : Integer.Sparse Key := [(key969, -24), (key1083, 6), (key1177, 6), (key1083, 6), (key1083, 6)]

def rawRow8672 : Integer.Sparse Key := [(key969, -24), (key1177, 6), (key1083, 6), (key1083, 6), (key1083, 6)]

def rawRow8673 : Integer.Sparse Key := [(key1177, -24), (key969, 6), (key1083, 6), (key1083, 6), (key1083, 6)]

def rawRow8674 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key969, 6), (key1083, 6), (key1083, 6)]

def rawRow8675 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key1083, 6), (key969, 6), (key1083, 6)]

def rawRow8676 : Integer.Sparse Key := [(key1177, -24), (key1083, 6), (key1083, 6), (key1083, 6), (key969, 6)]

def rawRow8677 : Integer.Sparse Key := [(key972, -6), (key977, -6), (key977, -6), (key977, -6), (key1086, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1181, 2)]

def rawRow8678 : Integer.Sparse Key := [(key977, -6), (key972, -6), (key977, -6), (key977, -6), (key1091, 2), (key1086, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1181, 2), (key1091, 2)]

def rawRow8679 : Integer.Sparse Key := [(key977, -6), (key977, -6), (key972, -6), (key977, -6), (key1091, 2), (key1091, 2), (key1086, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1181, 2), (key1091, 2), (key1091, 2)]

def rawRow8680 : Integer.Sparse Key := [(key977, -6), (key977, -6), (key977, -6), (key972, -6), (key1181, 2), (key1181, 2), (key1181, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1086, 2), (key1086, 2), (key1086, 2)]

def rawRow8681 : Integer.Sparse Key := [(key1181, -6), (key1181, -6), (key1181, -6), (key1218, -6), (key977, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key1162, 2)]

def rawRow8682 : Integer.Sparse Key := [(key1181, -6), (key1181, -6), (key1218, -6), (key1181, -6), (key1091, 2), (key1091, 2), (key1162, 2), (key977, 2), (key977, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, 2)]

def rawRow8683 : Integer.Sparse Key := [(key1181, -6), (key1218, -6), (key1181, -6), (key1181, -6), (key1091, 2), (key1162, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1162, 2), (key977, 2), (key1091, 2), (key1091, 2), (key977, 2), (key1091, 2)]

def rawRow8684 : Integer.Sparse Key := [(key1218, -6), (key1181, -6), (key1181, -6), (key1181, -6), (key1162, 2), (key1091, 2), (key1091, 2), (key1162, 2), (key1091, 2), (key1162, 2), (key977, 2), (key1091, 2), (key977, 2), (key1091, 2), (key1091, 2), (key977, 2)]

def rawRow8685 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2397, -6), (key2431, -6), (key2463, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2474, 2), (key2497, 2)]

def rawRow8686 : Integer.Sparse Key := [(key2397, -6), (key2397, -6), (key2431, -6), (key2397, -6), (key2463, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2474, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2497, 2), (key2474, 2)]

def rawRow8687 : Integer.Sparse Key := [(key2397, -6), (key2431, -6), (key2397, -6), (key2397, -6), (key2474, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2463, 2), (key2463, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2)]

def rawRow8688 : Integer.Sparse Key := [(key2431, -6), (key2397, -6), (key2397, -6), (key2397, -6), (key2497, 2), (key2497, 2), (key2497, 2), (key2474, 2), (key2474, 2), (key2474, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

def rawRow8689 : Integer.Sparse Key := [(key2384, -6), (key2474, -6), (key2474, -6), (key2474, -6), (key2369, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2), (key2463, 2)]

def rawRow8690 : Integer.Sparse Key := [(key2474, -6), (key2384, -6), (key2474, -6), (key2474, -6), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2369, 2), (key2397, 2), (key2397, 2), (key2463, 2), (key2463, 2)]

def rawRow8691 : Integer.Sparse Key := [(key2474, -6), (key2474, -6), (key2384, -6), (key2474, -6), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2369, 2), (key2397, 2)]

def rawRow8692 : Integer.Sparse Key := [(key2474, -6), (key2474, -6), (key2474, -6), (key2384, -6), (key2463, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2463, 2), (key2369, 2), (key2463, 2), (key2397, 2), (key2463, 2), (key2369, 2), (key2397, 2), (key2369, 2)]

def rawRow8693 : Integer.Sparse Key := [(key2354, -6), (key2358, -6), (key2358, -6), (key2358, -6), (key2449, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2529, 2)]

def rawRow8694 : Integer.Sparse Key := [(key2358, -6), (key2354, -6), (key2358, -6), (key2358, -6), (key2453, 2), (key2449, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2529, 2), (key2453, 2)]

def rawRow8695 : Integer.Sparse Key := [(key2358, -6), (key2358, -6), (key2354, -6), (key2358, -6), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2529, 2), (key2453, 2), (key2453, 2)]

def rawRow8696 : Integer.Sparse Key := [(key2358, -6), (key2358, -6), (key2358, -6), (key2354, -6), (key2529, 2), (key2529, 2), (key2529, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2449, 2), (key2449, 2), (key2449, 2)]

def rawRow8697 : Integer.Sparse Key := [(key2529, -6), (key2529, -6), (key2529, -6), (key2559, -6), (key2358, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2514, 2)]

def rawRow8698 : Integer.Sparse Key := [(key2529, -6), (key2529, -6), (key2559, -6), (key2529, -6), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, 2)]

def rawRow8699 : Integer.Sparse Key := [(key2529, -6), (key2559, -6), (key2529, -6), (key2529, -6), (key2453, 2), (key2514, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2358, 2), (key2453, 2)]

def rawRow8700 : Integer.Sparse Key := [(key2559, -6), (key2529, -6), (key2529, -6), (key2529, -6), (key2514, 2), (key2453, 2), (key2453, 2), (key2514, 2), (key2453, 2), (key2514, 2), (key2358, 2), (key2453, 2), (key2358, 2), (key2453, 2), (key2453, 2), (key2358, 2)]

def rawRow8701 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2967, 1)]

def rawRow8702 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2930, -2), (key2767, -2), (key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2888, 1)]

def rawRow8703 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2763, -2), (key2930, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2763, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow8704 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2767, -2), (key2763, -2), (key2763, -2), (key2763, -2), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1)]

def rawRow8705 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2909, -2), (key2909, -2), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1)]

def rawRow8706 : Integer.Sparse Key := [(key2888, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1)]

def rawRow8707 : Integer.Sparse Key := [(key2888, -2), (key2909, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2767, 1)]

def rawRow8708 : Integer.Sparse Key := [(key2909, -2), (key2888, -2), (key2888, -2), (key2909, -2), (key2888, -2), (key2909, -2), (key2599, -2), (key2888, -2), (key2599, -2), (key2888, -2), (key2888, -2), (key2599, -2), (key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2588, 1)]

def rawRow8709 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2447, 6), (key2447, 6), (key2511, 6)]

def rawRow8710 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2447, 6), (key2511, 6), (key2447, 6)]

def rawRow8711 : Integer.Sparse Key := [(key2352, -24), (key2447, 6), (key2511, 6), (key2447, 6), (key2447, 6)]

def rawRow8712 : Integer.Sparse Key := [(key2352, -24), (key2511, 6), (key2447, 6), (key2447, 6), (key2447, 6)]

def rawRow8713 : Integer.Sparse Key := [(key2511, -24), (key2352, 6), (key2447, 6), (key2447, 6), (key2447, 6)]

def rawRow8714 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2352, 6), (key2447, 6), (key2447, 6)]

def rawRow8715 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2447, 6), (key2352, 6), (key2447, 6)]

def rawRow8716 : Integer.Sparse Key := [(key2511, -24), (key2447, 6), (key2447, 6), (key2447, 6), (key2352, 6)]

def rawRow8717 : Integer.Sparse Key := [(key2584, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2599, -2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2)]

def rawRow8718 : Integer.Sparse Key := [(key2588, -2), (key2584, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2599, -2), (key2588, -2), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2767, 2)]

def rawRow8719 : Integer.Sparse Key := [(key2588, -2), (key2588, -2), (key2584, -2), (key2599, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2584, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2)]

def rawRow8720 : Integer.Sparse Key := [(key2599, -2), (key2599, -2), (key2599, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2588, -2), (key2584, -2), (key2584, -2), (key2584, -2), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2763, 2)]

def rawRow8721 : Integer.Sparse Key := [(key2930, -2), (key2930, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2988, -2), (key2988, -2), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2909, 2)]

def rawRow8722 : Integer.Sparse Key := [(key2967, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2)]

def rawRow8723 : Integer.Sparse Key := [(key2967, -2), (key2988, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2930, -2), (key2967, -2), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2888, 2)]

def rawRow8724 : Integer.Sparse Key := [(key2988, -2), (key2967, -2), (key2967, -2), (key2988, -2), (key2967, -2), (key2988, -2), (key2930, -2), (key2967, -2), (key2930, -2), (key2967, -2), (key2967, -2), (key2930, -2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2)]

def rawRow8725 : Integer.Sparse Key := [(key1527, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1766, -2), (key1605, 1), (key1610, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1649, 1), (key1605, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1807, 1), (key1610, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1649, 1), (key1807, 1)]

def rawRow8726 : Integer.Sparse Key := [(key1532, -2), (key1527, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1766, -2), (key1532, -2), (key1610, 1), (key1605, 1), (key1649, 1), (key1605, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1610, 1), (key1649, 1), (key1605, 1), (key1807, 1), (key1605, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1807, 1), (key1610, 1), (key1807, 1), (key1649, 1)]

def rawRow8727 : Integer.Sparse Key := [(key1532, -2), (key1532, -2), (key1527, -2), (key1766, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1527, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1605, 1), (key1605, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1)]

def rawRow8728 : Integer.Sparse Key := [(key1766, -2), (key1766, -2), (key1766, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1532, -2), (key1527, -2), (key1527, -2), (key1527, -2), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1807, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1649, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1), (key1605, 1)]

def rawRow8729 : Integer.Sparse Key := [(key1266, -2), (key1266, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1672, -2), (key1672, -2), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1), (key1638, 1)]

def rawRow8730 : Integer.Sparse Key := [(key1649, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1638, 1), (key1638, 1), (key1257, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1610, 1)]

def rawRow8731 : Integer.Sparse Key := [(key1649, -2), (key1672, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1266, -2), (key1649, -2), (key1610, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1532, 1)]

def rawRow8732 : Integer.Sparse Key := [(key1672, -2), (key1649, -2), (key1649, -2), (key1672, -2), (key1649, -2), (key1672, -2), (key1266, -2), (key1649, -2), (key1266, -2), (key1649, -2), (key1649, -2), (key1266, -2), (key1638, 1), (key1610, 1), (key1638, 1), (key1532, 1), (key1610, 1), (key1532, 1), (key1638, 1), (key1610, 1), (key1638, 1), (key1257, 1), (key1610, 1), (key1257, 1), (key1638, 1), (key1532, 1), (key1638, 1), (key1257, 1), (key1532, 1), (key1257, 1), (key1610, 1), (key1532, 1), (key1610, 1), (key1257, 1), (key1532, 1), (key1257, 1)]

def rawRow8733 : Integer.Sparse Key := [(key2840, 1), (key2844, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2967, 1), (key2875, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2988, -2), (key2909, -2), (key2988, -2)]

def rawRow8734 : Integer.Sparse Key := [(key2844, 1), (key2840, 1), (key2888, 1), (key2840, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2844, 1), (key2888, 1), (key2840, 1), (key2967, 1), (key2840, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2967, 1), (key2844, 1), (key2967, 1), (key2888, 1), (key2875, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2909, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2988, -2), (key2909, -2)]

def rawRow8735 : Integer.Sparse Key := [(key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2840, 1), (key2840, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2909, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2875, -2), (key2875, -2), (key2988, -2), (key2988, -2), (key2909, -2), (key2909, -2), (key2875, -2), (key2875, -2)]

def rawRow8736 : Integer.Sparse Key := [(key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2967, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2888, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2840, 1), (key2988, -2), (key2988, -2), (key2988, -2), (key2909, -2), (key2909, -2), (key2909, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2), (key2875, -2)]

def rawRow8737 : Integer.Sparse Key := [(key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2875, 1), (key2584, -2), (key2584, -2), (key2584, -2), (key2763, -2), (key2763, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2), (key2840, -2)]

def rawRow8738 : Integer.Sparse Key := [(key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2875, 1), (key2875, 1), (key2588, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2584, -2), (key2763, -2), (key2763, -2), (key2840, -2), (key2840, -2)]

def rawRow8739 : Integer.Sparse Key := [(key2844, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2840, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2584, -2), (key2763, -2)]

def rawRow8740 : Integer.Sparse Key := [(key2875, 1), (key2844, 1), (key2875, 1), (key2767, 1), (key2844, 1), (key2767, 1), (key2875, 1), (key2844, 1), (key2875, 1), (key2588, 1), (key2844, 1), (key2588, 1), (key2875, 1), (key2767, 1), (key2875, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2844, 1), (key2767, 1), (key2844, 1), (key2588, 1), (key2767, 1), (key2588, 1), (key2840, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2840, -2), (key2584, -2), (key2840, -2), (key2763, -2), (key2840, -2), (key2584, -2), (key2763, -2), (key2584, -2)]

def rawRow8741 : Integer.Sparse Key := [(key1524, -6), (key1524, -6), (key1524, -6), (key1762, -6), (key1602, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1645, 2), (key1803, 2)]

def rawRow8742 : Integer.Sparse Key := [(key1524, -6), (key1524, -6), (key1762, -6), (key1524, -6), (key1602, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1645, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1803, 2), (key1645, 2)]

def rawRow8743 : Integer.Sparse Key := [(key1524, -6), (key1762, -6), (key1524, -6), (key1524, -6), (key1645, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1602, 2), (key1602, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2)]

def rawRow8744 : Integer.Sparse Key := [(key1762, -6), (key1524, -6), (key1524, -6), (key1524, -6), (key1803, 2), (key1803, 2), (key1803, 2), (key1645, 2), (key1645, 2), (key1645, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2)]

def rawRow8745 : Integer.Sparse Key := [(key1262, -6), (key1645, -6), (key1645, -6), (key1645, -6), (key1249, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2), (key1602, 2)]

def rawRow8746 : Integer.Sparse Key := [(key1645, -6), (key1262, -6), (key1645, -6), (key1645, -6), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1249, 2), (key1524, 2), (key1524, 2), (key1602, 2), (key1602, 2)]

def rawRow8747 : Integer.Sparse Key := [(key1645, -6), (key1645, -6), (key1262, -6), (key1645, -6), (key1602, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1249, 2), (key1524, 2)]

def rawRow8748 : Integer.Sparse Key := [(key1645, -6), (key1645, -6), (key1645, -6), (key1262, -6), (key1602, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1602, 2), (key1249, 2), (key1602, 2), (key1524, 2), (key1602, 2), (key1249, 2), (key1524, 2), (key1249, 2)]

def rawRow8757 : Integer.Sparse Key := [(key2366, 2), (key2366, 2), (key2366, 2), (key2461, 2), (key2461, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2523, 2), (key2361, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2517, -2)]

def rawRow8758 : Integer.Sparse Key := [(key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2366, 2), (key2461, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2)]

def rawRow8759 : Integer.Sparse Key := [(key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2366, 2), (key2461, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2), (key2456, -2)]

def rawRow8760 : Integer.Sparse Key := [(key2523, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2523, 2), (key2366, 2), (key2523, 2), (key2461, 2), (key2523, 2), (key2366, 2), (key2461, 2), (key2366, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2517, -2), (key2456, -2), (key2517, -2), (key2361, -2), (key2456, -2), (key2361, -2), (key2456, -2), (key2456, -2), (key2361, -2)]

def rawRow8761 : Integer.Sparse Key := [(key1226, -24), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

def rawRow8762 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6)]

def rawRow8763 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6)]

def rawRow8764 : Integer.Sparse Key := [(key1226, -24), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6)]

def rawRow8765 : Integer.Sparse Key := [(key1228, -6), (key1228, -6), (key1228, -6), (key1245, -6), (key979, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key1164, 2)]

def rawRow8766 : Integer.Sparse Key := [(key1228, -6), (key1228, -6), (key1245, -6), (key1228, -6), (key1093, 2), (key1093, 2), (key1164, 2), (key979, 2), (key979, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, 2)]

def rawRow8767 : Integer.Sparse Key := [(key1228, -6), (key1245, -6), (key1228, -6), (key1228, -6), (key1093, 2), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1164, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2), (key1093, 2)]

def rawRow8768 : Integer.Sparse Key := [(key1245, -6), (key1228, -6), (key1228, -6), (key1228, -6), (key1164, 2), (key1093, 2), (key1093, 2), (key1164, 2), (key1093, 2), (key1164, 2), (key979, 2), (key1093, 2), (key979, 2), (key1093, 2), (key1093, 2), (key979, 2)]

def rawRow8769 : Integer.Sparse Key := [(key2385, -6), (key2475, -6), (key2475, -6), (key2475, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2), (key2466, 2)]

def rawRow8770 : Integer.Sparse Key := [(key2475, -6), (key2385, -6), (key2475, -6), (key2475, -6), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2372, 2), (key2400, 2), (key2400, 2), (key2466, 2), (key2466, 2)]

def rawRow8771 : Integer.Sparse Key := [(key2475, -6), (key2475, -6), (key2385, -6), (key2475, -6), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2372, 2), (key2400, 2)]

def rawRow8772 : Integer.Sparse Key := [(key2475, -6), (key2475, -6), (key2475, -6), (key2385, -6), (key2466, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2466, 2), (key2372, 2), (key2466, 2), (key2400, 2), (key2466, 2), (key2372, 2), (key2400, 2), (key2372, 2)]

def rawRow8773 : Integer.Sparse Key := [(key2566, -6), (key2566, -6), (key2566, -6), (key2578, -6), (key2359, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2515, 2)]

def rawRow8774 : Integer.Sparse Key := [(key2566, -6), (key2566, -6), (key2578, -6), (key2566, -6), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, 2)]

def rawRow8775 : Integer.Sparse Key := [(key2566, -6), (key2578, -6), (key2566, -6), (key2566, -6), (key2454, 2), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2359, 2), (key2454, 2)]

def rawRow8776 : Integer.Sparse Key := [(key2578, -6), (key2566, -6), (key2566, -6), (key2566, -6), (key2515, 2), (key2454, 2), (key2454, 2), (key2515, 2), (key2454, 2), (key2515, 2), (key2359, 2), (key2454, 2), (key2359, 2), (key2454, 2), (key2454, 2), (key2359, 2)]

def rawRow8777 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2435, -2), (key2464, 1), (key2470, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2501, 1)]

def rawRow8778 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2435, -2), (key2404, -2), (key2470, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2478, 1)]

def rawRow8779 : Integer.Sparse Key := [(key2404, -2), (key2404, -2), (key2398, -2), (key2435, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2398, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1)]

def rawRow8780 : Integer.Sparse Key := [(key2435, -2), (key2435, -2), (key2435, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2404, -2), (key2398, -2), (key2398, -2), (key2398, -2), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1)]

def rawRow8781 : Integer.Sparse Key := [(key2604, -2), (key2604, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2925, -2), (key2925, -2), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1)]

def rawRow8782 : Integer.Sparse Key := [(key2916, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1)]

def rawRow8783 : Integer.Sparse Key := [(key2916, -2), (key2925, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2604, -2), (key2916, -2), (key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2768, 1)]

def rawRow8784 : Integer.Sparse Key := [(key2925, -2), (key2916, -2), (key2916, -2), (key2925, -2), (key2916, -2), (key2925, -2), (key2604, -2), (key2916, -2), (key2604, -2), (key2916, -2), (key2916, -2), (key2604, -2), (key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2589, 1)]

def rawRow8785 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6)]

def rawRow8786 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6)]

def rawRow8787 : Integer.Sparse Key := [(key2355, -24), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6)]

def rawRow8788 : Integer.Sparse Key := [(key2355, -24), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

def rawRow8789 : Integer.Sparse Key := [(key2512, -24), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

def rawRow8790 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6)]

def rawRow8791 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6)]

def rawRow8792 : Integer.Sparse Key := [(key2512, -24), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6)]

def rawRow8801 : Integer.Sparse Key := [(key1526, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1894, -2), (key1604, 1), (key1612, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1679, 1), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1916, 1), (key1679, 1), (key1916, 1), (key1612, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1679, 1), (key1916, 1)]

def rawRow8802 : Integer.Sparse Key := [(key1534, -2), (key1526, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1894, -2), (key1534, -2), (key1612, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1679, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1679, 1)]

def rawRow8803 : Integer.Sparse Key := [(key1534, -2), (key1534, -2), (key1526, -2), (key1894, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1526, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1604, 1), (key1604, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1)]

def rawRow8804 : Integer.Sparse Key := [(key1894, -2), (key1894, -2), (key1894, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1534, -2), (key1526, -2), (key1526, -2), (key1526, -2), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1)]

def rawRow8805 : Integer.Sparse Key := [(key1271, -2), (key1271, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1693, -2), (key1693, -2), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1)]

def rawRow8806 : Integer.Sparse Key := [(key1679, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1640, 1), (key1640, 1), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1)]

def rawRow8807 : Integer.Sparse Key := [(key1679, -2), (key1693, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1271, -2), (key1679, -2), (key1612, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1534, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1534, 1)]

def rawRow8808 : Integer.Sparse Key := [(key1693, -2), (key1679, -2), (key1679, -2), (key1693, -2), (key1679, -2), (key1693, -2), (key1271, -2), (key1679, -2), (key1271, -2), (key1679, -2), (key1679, -2), (key1271, -2), (key1640, 1), (key1612, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1534, 1), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1259, 1), (key1534, 1), (key1259, 1), (key1612, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1534, 1), (key1259, 1)]

def rawRow8809 : Integer.Sparse Key := [(key2464, 1), (key2470, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2501, 1), (key2568, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2575, -2), (key2570, -2), (key2575, -2)]

def rawRow8810 : Integer.Sparse Key := [(key2470, 1), (key2464, 1), (key2478, 1), (key2464, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2470, 1), (key2478, 1), (key2464, 1), (key2501, 1), (key2464, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2501, 1), (key2470, 1), (key2501, 1), (key2478, 1), (key2568, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2570, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2575, -2), (key2570, -2)]

def rawRow8811 : Integer.Sparse Key := [(key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2464, 1), (key2464, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2570, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2568, -2), (key2568, -2), (key2575, -2), (key2575, -2), (key2570, -2), (key2570, -2), (key2568, -2), (key2568, -2)]

def rawRow8812 : Integer.Sparse Key := [(key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2501, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2470, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2464, 1), (key2575, -2), (key2575, -2), (key2575, -2), (key2570, -2), (key2570, -2), (key2570, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2), (key2568, -2)]

def rawRow8813 : Integer.Sparse Key := [(key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2876, 1), (key2370, -2), (key2370, -2), (key2370, -2), (key2398, -2), (key2398, -2), (key2398, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2), (key2464, -2)]

def rawRow8814 : Integer.Sparse Key := [(key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2876, 1), (key2876, 1), (key2589, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2839, -2), (key2370, -2), (key2370, -2), (key2398, -2), (key2398, -2), (key2464, -2), (key2464, -2)]

def rawRow8815 : Integer.Sparse Key := [(key2845, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2839, -2), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2370, -2), (key2398, -2)]

def rawRow8816 : Integer.Sparse Key := [(key2876, 1), (key2845, 1), (key2876, 1), (key2768, 1), (key2845, 1), (key2768, 1), (key2876, 1), (key2845, 1), (key2876, 1), (key2589, 1), (key2845, 1), (key2589, 1), (key2876, 1), (key2768, 1), (key2876, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2845, 1), (key2768, 1), (key2845, 1), (key2589, 1), (key2768, 1), (key2589, 1), (key2839, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2839, -2), (key2583, -2), (key2839, -2), (key2762, -2), (key2839, -2), (key2583, -2), (key2762, -2), (key2583, -2)]

def rawRow8817 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1525, -6), (key1892, -6), (key1603, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1677, 2), (key1914, 2)]

def rawRow8818 : Integer.Sparse Key := [(key1525, -6), (key1525, -6), (key1892, -6), (key1525, -6), (key1603, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1677, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1914, 2), (key1677, 2)]

def rawRow8819 : Integer.Sparse Key := [(key1525, -6), (key1892, -6), (key1525, -6), (key1525, -6), (key1677, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1603, 2), (key1603, 2), (key1914, 2), (key1914, 2), (key1677, 2), (key1677, 2), (key1603, 2), (key1603, 2)]

def rawRow8820 : Integer.Sparse Key := [(key1892, -6), (key1525, -6), (key1525, -6), (key1525, -6), (key1914, 2), (key1914, 2), (key1914, 2), (key1677, 2), (key1677, 2), (key1677, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2)]

def rawRow8821 : Integer.Sparse Key := [(key1269, -6), (key1677, -6), (key1677, -6), (key1677, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1525, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2), (key1603, 2)]

def rawRow8822 : Integer.Sparse Key := [(key1677, -6), (key1269, -6), (key1677, -6), (key1677, -6), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1250, 2), (key1525, 2), (key1525, 2), (key1603, 2), (key1603, 2)]

def rawRow8823 : Integer.Sparse Key := [(key1677, -6), (key1677, -6), (key1269, -6), (key1677, -6), (key1603, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1250, 2), (key1525, 2)]

def rawRow8824 : Integer.Sparse Key := [(key1677, -6), (key1677, -6), (key1677, -6), (key1269, -6), (key1603, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1603, 2), (key1250, 2), (key1603, 2), (key1525, 2), (key1603, 2), (key1250, 2), (key1525, 2), (key1250, 2)]

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

def rawRow8841 : Integer.Sparse Key := [(key2268, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2294, 2), (key2272, 2), (key2294, 2), (key2323, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2336, -2)]

def rawRow8842 : Integer.Sparse Key := [(key2268, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2272, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2294, 2), (key2272, 2), (key2324, -2), (key2323, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2336, -2), (key2324, -2)]

def rawRow8843 : Integer.Sparse Key := [(key2272, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2294, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, -2), (key2324, -2), (key2323, -2), (key2336, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2323, -2), (key2336, -2), (key2324, -2), (key2324, -2)]

def rawRow8844 : Integer.Sparse Key := [(key2294, 2), (key2294, 2), (key2294, 2), (key2272, 2), (key2272, 2), (key2272, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2268, 2), (key2336, -2), (key2336, -2), (key2336, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2324, -2), (key2323, -2), (key2323, -2), (key2323, -2)]

def rawRow8845 : Integer.Sparse Key := [(key1999, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2268, 2), (key2294, 2), (key2323, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2336, 2), (key1999, -2), (key2003, -2), (key2003, -2), (key2268, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2294, -2), (key2324, -2), (key2324, -2), (key2336, -2)]

def rawRow8846 : Integer.Sparse Key := [(key1999, 2), (key2003, 2), (key1999, 2), (key2268, 2), (key2294, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key2336, 2), (key2323, 2), (key2336, 2), (key2324, 2), (key2003, -2), (key1999, -2), (key2003, -2), (key2272, -2), (key2268, -2), (key2294, -2), (key2268, -2), (key2294, -2), (key2272, -2), (key2324, -2), (key2336, -2), (key2324, -2)]

def rawRow8847 : Integer.Sparse Key := [(key2003, 2), (key1999, 2), (key1999, 2), (key2294, 2), (key2268, 2), (key2268, 2), (key2336, 2), (key2336, 2), (key2324, 2), (key2324, 2), (key2323, 2), (key2323, 2), (key2003, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2294, -2), (key2272, -2), (key2272, -2), (key2268, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2324, -2)]

def rawRow8848 : Integer.Sparse Key := [(key2268, 2), (key2323, 2), (key2324, 2), (key1999, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2003, 2), (key2268, 2), (key2294, 2), (key2324, 2), (key2336, 2), (key2268, -2), (key2272, -2), (key2324, -2), (key1999, -2), (key2003, -2), (key2268, -2), (key2294, -2), (key2324, -2), (key2336, -2), (key2003, -2), (key2272, -2), (key2294, -2)]

def rawRow8849 : Integer.Sparse Key := [(key2268, 2), (key2324, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2323, 2), (key2003, 2), (key1999, 2), (key2294, 2), (key2268, 2), (key2336, 2), (key2324, 2), (key2272, -2), (key2268, -2), (key2324, -2), (key2003, -2), (key1999, -2), (key2294, -2), (key2268, -2), (key2336, -2), (key2324, -2), (key2003, -2), (key2294, -2), (key2272, -2)]

def rawRow8850 : Integer.Sparse Key := [(key2323, 2), (key2268, 2), (key2324, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2268, 2), (key2324, 2), (key1999, 2), (key2336, 2), (key2003, 2), (key2294, 2), (key2268, -2), (key2324, -2), (key2272, -2), (key2268, -2), (key2324, -2), (key1999, -2), (key2336, -2), (key2003, -2), (key2294, -2), (key2272, -2), (key2003, -2), (key2294, -2)]

def rawRow8851 : Integer.Sparse Key := [(key2323, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2324, 2), (key2268, 2), (key2336, 2), (key1999, 2), (key2294, 2), (key2003, 2), (key2324, -2), (key2268, -2), (key2272, -2), (key2324, -2), (key2268, -2), (key2336, -2), (key1999, -2), (key2294, -2), (key2003, -2), (key2272, -2), (key2294, -2), (key2003, -2)]

def rawRow8852 : Integer.Sparse Key := [(key2324, 2), (key2268, 2), (key2323, 2), (key2336, 2), (key1999, 2), (key2323, 2), (key2294, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key1999, 2), (key2268, 2), (key2272, -2), (key2324, -2), (key2268, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2294, -2), (key2003, -2), (key2272, -2)]

def rawRow8853 : Integer.Sparse Key := [(key2324, 2), (key2323, 2), (key2268, 2), (key2336, 2), (key2323, 2), (key1999, 2), (key2336, 2), (key2294, 2), (key2324, 2), (key2003, 2), (key2268, 2), (key1999, 2), (key2324, -2), (key2272, -2), (key2268, -2), (key2336, -2), (key2294, -2), (key2324, -2), (key2003, -2), (key2268, -2), (key1999, -2), (key2294, -2), (key2272, -2), (key2003, -2)]

def rawRow8854 : Integer.Sparse Key := [(key2294, 2), (key2336, 2), (key2336, 2), (key2003, 2), (key2324, 2), (key2324, 2), (key1999, 2), (key1999, 2), (key2268, 2), (key2268, 2), (key2323, 2), (key2323, 2), (key2294, -2), (key2294, -2), (key2336, -2), (key2003, -2), (key2003, -2), (key2272, -2), (key2272, -2), (key2324, -2), (key2324, -2), (key1999, -2), (key2268, -2), (key2268, -2)]

def rawRow8855 : Integer.Sparse Key := [(key2336, 2), (key2294, 2), (key2336, 2), (key2324, 2), (key2003, 2), (key2324, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2323, 2), (key1999, 2), (key2268, 2), (key2294, -2), (key2336, -2), (key2294, -2), (key2272, -2), (key2324, -2), (key2003, -2), (key2324, -2), (key2003, -2), (key2272, -2), (key2268, -2), (key1999, -2), (key2268, -2)]

def rawRow8856 : Integer.Sparse Key := [(key2336, 2), (key2336, 2), (key2294, 2), (key2324, 2), (key2324, 2), (key2003, 2), (key2323, 2), (key2268, 2), (key2323, 2), (key1999, 2), (key2268, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2294, -2), (key2324, -2), (key2272, -2), (key2324, -2), (key2003, -2), (key2272, -2), (key2003, -2), (key2268, -2), (key2268, -2), (key1999, -2)]

def rawRow8858 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key942, 6), (key946, 6), (key942, 6)]

def rawRow8859 : Integer.Sparse Key := [(key724, -24), (key942, 6), (key946, 6), (key942, 6), (key942, 6)]

def rawRow8860 : Integer.Sparse Key := [(key724, -24), (key946, 6), (key942, 6), (key942, 6), (key942, 6)]

def rawRow8861 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key942, 6), (key942, 6), (key946, 6)]

def rawRow8862 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key942, 6), (key946, 6), (key942, 6)]

def rawRow8863 : Integer.Sparse Key := [(key942, -24), (key724, 6), (key946, 6), (key942, 6), (key942, 6)]

def rawRow8864 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key724, 6), (key942, 6), (key946, 6)]

def rawRow8865 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key724, 6), (key946, 6), (key942, 6)]

def rawRow8866 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key942, 6), (key724, 6), (key946, 6)]

def rawRow8867 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key942, 6), (key946, 6), (key724, 6)]

def rawRow8868 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key946, 6), (key724, 6), (key942, 6)]

def rawRow8869 : Integer.Sparse Key := [(key942, -24), (key942, 6), (key946, 6), (key942, 6), (key724, 6)]

def rawRow8870 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key724, 6), (key942, 6), (key942, 6)]

def rawRow8871 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key942, 6), (key724, 6), (key942, 6)]

def rawRow8872 : Integer.Sparse Key := [(key942, -24), (key946, 6), (key942, 6), (key942, 6), (key724, 6)]

def rawRow8873 : Integer.Sparse Key := [(key713, -6), (key715, -6), (key715, -6), (key715, -6), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key892, 2), (key890, 2), (key914, 2), (key892, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2)]

def rawRow8874 : Integer.Sparse Key := [(key715, -6), (key713, -6), (key715, -6), (key715, -6), (key892, 2), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key914, 2), (key890, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key892, 2)]

def rawRow8875 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key713, -6), (key715, -6), (key892, 2), (key892, 2), (key890, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key914, 2), (key892, 2), (key892, 2)]

def rawRow8876 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key715, -6), (key713, -6), (key914, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key890, 2)]

def rawRow8877 : Integer.Sparse Key := [(key890, -6), (key892, -6), (key892, -6), (key959, -6), (key713, 2), (key715, 2), (key715, 2), (key890, 2), (key892, 2), (key890, 2), (key914, 2), (key892, 2), (key914, 2), (key959, 2), (key959, 2), (key966, 2)]

def rawRow8878 : Integer.Sparse Key := [(key892, -6), (key890, -6), (key892, -6), (key959, -6), (key715, 2), (key713, 2), (key715, 2), (key892, 2), (key890, 2), (key914, 2), (key890, 2), (key914, 2), (key892, 2), (key959, 2), (key966, 2), (key959, 2)]

def rawRow8879 : Integer.Sparse Key := [(key892, -6), (key892, -6), (key890, -6), (key959, -6), (key715, 2), (key715, 2), (key713, 2), (key914, 2), (key914, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key966, 2), (key959, 2), (key959, 2)]

def rawRow8880 : Integer.Sparse Key := [(key890, -6), (key892, -6), (key959, -6), (key892, -6), (key890, 2), (key892, 2), (key959, 2), (key713, 2), (key715, 2), (key890, 2), (key914, 2), (key959, 2), (key966, 2), (key715, 2), (key892, 2), (key914, 2)]

def rawRow8881 : Integer.Sparse Key := [(key892, -6), (key890, -6), (key959, -6), (key892, -6), (key892, 2), (key890, 2), (key959, 2), (key715, 2), (key713, 2), (key914, 2), (key890, 2), (key966, 2), (key959, 2), (key715, 2), (key914, 2), (key892, 2)]

def rawRow8882 : Integer.Sparse Key := [(key890, -6), (key959, -6), (key892, -6), (key892, -6), (key890, 2), (key959, 2), (key892, 2), (key890, 2), (key959, 2), (key713, 2), (key966, 2), (key715, 2), (key914, 2), (key892, 2), (key715, 2), (key914, 2)]

def rawRow8883 : Integer.Sparse Key := [(key959, -6), (key890, -6), (key892, -6), (key892, -6), (key959, 2), (key890, 2), (key892, 2), (key959, 2), (key890, 2), (key966, 2), (key713, 2), (key914, 2), (key715, 2), (key892, 2), (key914, 2), (key715, 2)]

def rawRow8884 : Integer.Sparse Key := [(key892, -6), (key959, -6), (key890, -6), (key892, -6), (key892, 2), (key959, 2), (key890, 2), (key914, 2), (key966, 2), (key715, 2), (key959, 2), (key713, 2), (key890, 2), (key914, 2), (key715, 2), (key892, 2)]

def rawRow8885 : Integer.Sparse Key := [(key959, -6), (key892, -6), (key890, -6), (key892, -6), (key959, 2), (key892, 2), (key890, 2), (key966, 2), (key914, 2), (key959, 2), (key715, 2), (key890, 2), (key713, 2), (key914, 2), (key892, 2), (key715, 2)]

def rawRow8886 : Integer.Sparse Key := [(key892, -6), (key892, -6), (key959, -6), (key890, -6), (key914, 2), (key914, 2), (key966, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key959, 2), (key959, 2), (key713, 2), (key890, 2), (key890, 2)]

def rawRow8887 : Integer.Sparse Key := [(key892, -6), (key959, -6), (key892, -6), (key890, -6), (key914, 2), (key966, 2), (key914, 2), (key892, 2), (key959, 2), (key715, 2), (key959, 2), (key715, 2), (key892, 2), (key890, 2), (key713, 2), (key890, 2)]

def rawRow8888 : Integer.Sparse Key := [(key959, -6), (key892, -6), (key892, -6), (key890, -6), (key966, 2), (key914, 2), (key914, 2), (key959, 2), (key892, 2), (key959, 2), (key715, 2), (key892, 2), (key715, 2), (key890, 2), (key890, 2), (key713, 2)]

def rawRow8889 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2203, -6), (key2206, -6), (key2317, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2318, 2), (key2321, 2)]

def rawRow8890 : Integer.Sparse Key := [(key2203, -6), (key2203, -6), (key2206, -6), (key2203, -6), (key2317, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2318, 2)]

def rawRow8891 : Integer.Sparse Key := [(key2203, -6), (key2206, -6), (key2203, -6), (key2203, -6), (key2318, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2317, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2)]

def rawRow8892 : Integer.Sparse Key := [(key2206, -6), (key2203, -6), (key2203, -6), (key2203, -6), (key2321, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2), (key2317, 2)]

def rawRow8893 : Integer.Sparse Key := [(key2098, -6), (key2317, -6), (key2317, -6), (key2321, -6), (key2098, 2), (key2098, 2), (key2099, 2), (key2203, 2), (key2203, 2), (key2206, 2), (key2317, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2318, 2), (key2321, 2)]

def rawRow8894 : Integer.Sparse Key := [(key2098, -6), (key2317, -6), (key2321, -6), (key2317, -6), (key2098, 2), (key2099, 2), (key2098, 2), (key2203, 2), (key2206, 2), (key2203, 2), (key2318, 2), (key2317, 2), (key2321, 2), (key2317, 2), (key2321, 2), (key2318, 2)]

def rawRow8895 : Integer.Sparse Key := [(key2098, -6), (key2321, -6), (key2317, -6), (key2317, -6), (key2099, 2), (key2098, 2), (key2098, 2), (key2206, 2), (key2203, 2), (key2203, 2), (key2321, 2), (key2321, 2), (key2318, 2), (key2318, 2), (key2317, 2), (key2317, 2)]

def rawRow8896 : Integer.Sparse Key := [(key2317, -6), (key2098, -6), (key2317, -6), (key2321, -6), (key2203, 2), (key2317, 2), (key2318, 2), (key2098, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2099, 2), (key2203, 2), (key2206, 2), (key2318, 2), (key2321, 2)]

def rawRow8897 : Integer.Sparse Key := [(key2317, -6), (key2098, -6), (key2321, -6), (key2317, -6), (key2203, 2), (key2318, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2317, 2), (key2099, 2), (key2098, 2), (key2206, 2), (key2203, 2), (key2321, 2), (key2318, 2)]

def rawRow8898 : Integer.Sparse Key := [(key2317, -6), (key2317, -6), (key2098, -6), (key2321, -6), (key2317, 2), (key2203, 2), (key2318, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2203, 2), (key2318, 2), (key2098, 2), (key2321, 2), (key2099, 2), (key2206, 2)]

def rawRow8899 : Integer.Sparse Key := [(key2317, -6), (key2317, -6), (key2321, -6), (key2098, -6), (key2317, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2318, 2), (key2203, 2), (key2321, 2), (key2098, 2), (key2206, 2), (key2099, 2)]

def rawRow8900 : Integer.Sparse Key := [(key2317, -6), (key2321, -6), (key2098, -6), (key2317, -6), (key2318, 2), (key2203, 2), (key2317, 2), (key2321, 2), (key2098, 2), (key2317, 2), (key2206, 2), (key2321, 2), (key2099, 2), (key2318, 2), (key2098, 2), (key2203, 2)]

def rawRow8901 : Integer.Sparse Key := [(key2317, -6), (key2321, -6), (key2317, -6), (key2098, -6), (key2318, 2), (key2317, 2), (key2203, 2), (key2321, 2), (key2317, 2), (key2098, 2), (key2321, 2), (key2206, 2), (key2318, 2), (key2099, 2), (key2203, 2), (key2098, 2)]

def rawRow8902 : Integer.Sparse Key := [(key2321, -6), (key2098, -6), (key2317, -6), (key2317, -6), (key2206, 2), (key2321, 2), (key2321, 2), (key2099, 2), (key2318, 2), (key2318, 2), (key2098, 2), (key2098, 2), (key2203, 2), (key2203, 2), (key2317, 2), (key2317, 2)]

def rawRow8903 : Integer.Sparse Key := [(key2321, -6), (key2317, -6), (key2098, -6), (key2317, -6), (key2321, 2), (key2206, 2), (key2321, 2), (key2318, 2), (key2099, 2), (key2318, 2), (key2203, 2), (key2317, 2), (key2098, 2), (key2317, 2), (key2098, 2), (key2203, 2)]

def rawRow8904 : Integer.Sparse Key := [(key2321, -6), (key2317, -6), (key2317, -6), (key2098, -6), (key2321, 2), (key2321, 2), (key2206, 2), (key2318, 2), (key2318, 2), (key2099, 2), (key2317, 2), (key2203, 2), (key2317, 2), (key2098, 2), (key2203, 2), (key2098, 2)]

def rawRow8905 : Integer.Sparse Key := [(key1998, -6), (key2000, -6), (key2000, -6), (key2000, -6), (key2267, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2292, 2)]

def rawRow8906 : Integer.Sparse Key := [(key2000, -6), (key1998, -6), (key2000, -6), (key2000, -6), (key2269, 2), (key2267, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2292, 2), (key2269, 2)]

def rawRow8907 : Integer.Sparse Key := [(key2000, -6), (key2000, -6), (key1998, -6), (key2000, -6), (key2269, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2269, 2)]

def rawRow8908 : Integer.Sparse Key := [(key2000, -6), (key2000, -6), (key2000, -6), (key1998, -6), (key2292, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2267, 2)]

def rawRow8909 : Integer.Sparse Key := [(key2267, -6), (key2269, -6), (key2269, -6), (key2340, -6), (key1998, 2), (key2000, 2), (key2000, 2), (key2267, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2292, 2), (key2340, 2), (key2340, 2), (key2349, 2)]

def rawRow8910 : Integer.Sparse Key := [(key2269, -6), (key2267, -6), (key2269, -6), (key2340, -6), (key2000, 2), (key1998, 2), (key2000, 2), (key2269, 2), (key2267, 2), (key2292, 2), (key2267, 2), (key2292, 2), (key2269, 2), (key2340, 2), (key2349, 2), (key2340, 2)]

def rawRow8911 : Integer.Sparse Key := [(key2269, -6), (key2269, -6), (key2267, -6), (key2340, -6), (key2000, 2), (key2000, 2), (key1998, 2), (key2292, 2), (key2292, 2), (key2269, 2), (key2269, 2), (key2267, 2), (key2267, 2), (key2349, 2), (key2340, 2), (key2340, 2)]

def rawRow8912 : Integer.Sparse Key := [(key2267, -6), (key2269, -6), (key2340, -6), (key2269, -6), (key2267, 2), (key2269, 2), (key2340, 2), (key1998, 2), (key2000, 2), (key2267, 2), (key2292, 2), (key2340, 2), (key2349, 2), (key2000, 2), (key2269, 2), (key2292, 2)]

def rawRow8913 : Integer.Sparse Key := [(key2269, -6), (key2267, -6), (key2340, -6), (key2269, -6), (key2269, 2), (key2267, 2), (key2340, 2), (key2000, 2), (key1998, 2), (key2292, 2), (key2267, 2), (key2349, 2), (key2340, 2), (key2000, 2), (key2292, 2), (key2269, 2)]

def rawRow8914 : Integer.Sparse Key := [(key2267, -6), (key2340, -6), (key2269, -6), (key2269, -6), (key2267, 2), (key2340, 2), (key2269, 2), (key2267, 2), (key2340, 2), (key1998, 2), (key2349, 2), (key2000, 2), (key2292, 2), (key2269, 2), (key2000, 2), (key2292, 2)]

def rawRow8915 : Integer.Sparse Key := [(key2340, -6), (key2267, -6), (key2269, -6), (key2269, -6), (key2340, 2), (key2267, 2), (key2269, 2), (key2340, 2), (key2267, 2), (key2349, 2), (key1998, 2), (key2292, 2), (key2000, 2), (key2269, 2), (key2292, 2), (key2000, 2)]

def rawRow8916 : Integer.Sparse Key := [(key2269, -6), (key2340, -6), (key2267, -6), (key2269, -6), (key2269, 2), (key2340, 2), (key2267, 2), (key2292, 2), (key2349, 2), (key2000, 2), (key2340, 2), (key1998, 2), (key2267, 2), (key2292, 2), (key2000, 2), (key2269, 2)]

def rawRow8917 : Integer.Sparse Key := [(key2340, -6), (key2269, -6), (key2267, -6), (key2269, -6), (key2340, 2), (key2269, 2), (key2267, 2), (key2349, 2), (key2292, 2), (key2340, 2), (key2000, 2), (key2267, 2), (key1998, 2), (key2292, 2), (key2269, 2), (key2000, 2)]

def rawRow8918 : Integer.Sparse Key := [(key2269, -6), (key2269, -6), (key2340, -6), (key2267, -6), (key2292, 2), (key2292, 2), (key2349, 2), (key2000, 2), (key2000, 2), (key2269, 2), (key2269, 2), (key2340, 2), (key2340, 2), (key1998, 2), (key2267, 2), (key2267, 2)]

def rawRow8919 : Integer.Sparse Key := [(key2269, -6), (key2340, -6), (key2269, -6), (key2267, -6), (key2292, 2), (key2349, 2), (key2292, 2), (key2269, 2), (key2340, 2), (key2000, 2), (key2340, 2), (key2000, 2), (key2269, 2), (key2267, 2), (key1998, 2), (key2267, 2)]

def rawRow8920 : Integer.Sparse Key := [(key2340, -6), (key2269, -6), (key2269, -6), (key2267, -6), (key2349, 2), (key2292, 2), (key2292, 2), (key2340, 2), (key2269, 2), (key2340, 2), (key2000, 2), (key2269, 2), (key2000, 2), (key2267, 2), (key2267, 2), (key1998, 2)]

def rawRow8921 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2287, 1)]

def rawRow8922 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2279, 1)]

def rawRow8923 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2187, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2174, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1)]

def rawRow8924 : Integer.Sparse Key := [(key2187, -2), (key2187, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2176, -2), (key2174, -2), (key2174, -2), (key2174, -2), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1)]

def rawRow8925 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2274, -2), (key2276, -2), (key2274, -2), (key2287, -2), (key2276, -2), (key2287, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2347, 1)]

def rawRow8926 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2276, -2), (key2274, -2), (key2287, -2), (key2274, -2), (key2287, -2), (key2276, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2341, 1), (key2347, 1), (key2343, 1)]

def rawRow8927 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2287, -2), (key2287, -2), (key2276, -2), (key2276, -2), (key2274, -2), (key2274, -2), (key2347, -2), (key2341, -2), (key2341, -2), (key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2347, 1), (key2347, 1), (key2343, 1), (key2343, 1), (key2341, 1), (key2341, 1)]

def rawRow8928 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2341, -2), (key2077, -2), (key2079, -2), (key2274, -2), (key2287, -2), (key2341, -2), (key2347, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2174, 1), (key2176, 1), (key2274, 1), (key2279, 1), (key2341, 1), (key2343, 1), (key2077, 1), (key2079, 1), (key2274, 1), (key2287, 1), (key2341, 1), (key2347, 1), (key2077, 1), (key2085, 1), (key2174, 1), (key2187, 1), (key2343, 1), (key2347, 1), (key2079, 1), (key2085, 1), (key2176, 1), (key2187, 1), (key2279, 1), (key2287, 1)]

def rawRow8929 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2341, -2), (key2079, -2), (key2077, -2), (key2287, -2), (key2274, -2), (key2347, -2), (key2341, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2176, 1), (key2174, 1), (key2279, 1), (key2274, 1), (key2343, 1), (key2341, 1), (key2079, 1), (key2077, 1), (key2287, 1), (key2274, 1), (key2347, 1), (key2341, 1), (key2085, 1), (key2077, 1), (key2187, 1), (key2174, 1), (key2347, 1), (key2343, 1), (key2085, 1), (key2079, 1), (key2187, 1), (key2176, 1), (key2287, 1), (key2279, 1)]

def rawRow8930 : Integer.Sparse Key := [(key2274, -2), (key2341, -2), (key2276, -2), (key2274, -2), (key2341, -2), (key2077, -2), (key2347, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2274, 1), (key2341, 1), (key2174, 1), (key2343, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2341, 1), (key2077, 1), (key2347, 1), (key2079, 1), (key2287, 1), (key2174, 1), (key2343, 1), (key2077, 1), (key2347, 1), (key2085, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2079, 1), (key2287, 1), (key2085, 1), (key2187, 1)]

def rawRow8931 : Integer.Sparse Key := [(key2341, -2), (key2274, -2), (key2276, -2), (key2341, -2), (key2274, -2), (key2347, -2), (key2077, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2341, 1), (key2274, 1), (key2343, 1), (key2174, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2274, 1), (key2347, 1), (key2077, 1), (key2287, 1), (key2079, 1), (key2343, 1), (key2174, 1), (key2347, 1), (key2077, 1), (key2187, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2287, 1), (key2079, 1), (key2187, 1), (key2085, 1)]

def rawRow8932 : Integer.Sparse Key := [(key2276, -2), (key2341, -2), (key2274, -2), (key2287, -2), (key2347, -2), (key2079, -2), (key2341, -2), (key2077, -2), (key2274, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2279, 1), (key2343, 1), (key2176, 1), (key2341, 1), (key2174, 1), (key2274, 1), (key2287, 1), (key2347, 1), (key2079, 1), (key2341, 1), (key2077, 1), (key2274, 1), (key2187, 1), (key2347, 1), (key2085, 1), (key2343, 1), (key2077, 1), (key2174, 1), (key2187, 1), (key2287, 1), (key2085, 1), (key2279, 1), (key2079, 1), (key2176, 1)]

def rawRow8933 : Integer.Sparse Key := [(key2341, -2), (key2276, -2), (key2274, -2), (key2347, -2), (key2287, -2), (key2341, -2), (key2079, -2), (key2274, -2), (key2077, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2343, 1), (key2279, 1), (key2341, 1), (key2176, 1), (key2274, 1), (key2174, 1), (key2347, 1), (key2287, 1), (key2341, 1), (key2079, 1), (key2274, 1), (key2077, 1), (key2347, 1), (key2187, 1), (key2343, 1), (key2085, 1), (key2174, 1), (key2077, 1), (key2287, 1), (key2187, 1), (key2279, 1), (key2085, 1), (key2176, 1), (key2079, 1)]

def rawRow8934 : Integer.Sparse Key := [(key2287, -2), (key2287, -2), (key2347, -2), (key2079, -2), (key2079, -2), (key2276, -2), (key2276, -2), (key2341, -2), (key2341, -2), (key2077, -2), (key2274, -2), (key2274, -2), (key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1), (key2079, 1), (key2079, 1), (key2176, 1), (key2176, 1), (key2341, 1), (key2341, 1), (key2077, 1), (key2077, 1), (key2174, 1), (key2174, 1), (key2274, 1), (key2274, 1)]

def rawRow8935 : Integer.Sparse Key := [(key2287, -2), (key2347, -2), (key2287, -2), (key2276, -2), (key2341, -2), (key2079, -2), (key2341, -2), (key2079, -2), (key2276, -2), (key2274, -2), (key2077, -2), (key2274, -2), (key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2274, 1), (key2077, 1), (key2174, 1)]

def rawRow8936 : Integer.Sparse Key := [(key2347, -2), (key2287, -2), (key2287, -2), (key2341, -2), (key2276, -2), (key2341, -2), (key2079, -2), (key2276, -2), (key2079, -2), (key2274, -2), (key2274, -2), (key2077, -2), (key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2079, 1), (key2274, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2077, 1)]

def rawRow8937 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2316, 6), (key2316, 6), (key2322, 6)]

def rawRow8938 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2316, 6), (key2322, 6), (key2316, 6)]

def rawRow8939 : Integer.Sparse Key := [(key2009, -24), (key2316, 6), (key2322, 6), (key2316, 6), (key2316, 6)]

def rawRow8940 : Integer.Sparse Key := [(key2009, -24), (key2322, 6), (key2316, 6), (key2316, 6), (key2316, 6)]

def rawRow8941 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2316, 6), (key2316, 6), (key2322, 6)]

def rawRow8942 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2316, 6), (key2322, 6), (key2316, 6)]

def rawRow8943 : Integer.Sparse Key := [(key2316, -24), (key2009, 6), (key2322, 6), (key2316, 6), (key2316, 6)]

def rawRow8944 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2009, 6), (key2316, 6), (key2322, 6)]

def rawRow8945 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2009, 6), (key2322, 6), (key2316, 6)]

def rawRow8946 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2316, 6), (key2009, 6), (key2322, 6)]

def rawRow8947 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2316, 6), (key2322, 6), (key2009, 6)]

def rawRow8948 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2322, 6), (key2009, 6), (key2316, 6)]

def rawRow8949 : Integer.Sparse Key := [(key2316, -24), (key2316, 6), (key2322, 6), (key2316, 6), (key2009, 6)]

def rawRow8950 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2009, 6), (key2316, 6), (key2316, 6)]

def rawRow8951 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2316, 6), (key2009, 6), (key2316, 6)]

def rawRow8952 : Integer.Sparse Key := [(key2316, -24), (key2322, 6), (key2316, 6), (key2316, 6), (key2009, 6)]

def rawRow8953 : Integer.Sparse Key := [(key2077, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2085, -2), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2187, 2)]

def rawRow8954 : Integer.Sparse Key := [(key2079, -2), (key2077, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2085, -2), (key2079, -2), (key2176, 2), (key2174, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2187, 2), (key2176, 2)]

def rawRow8955 : Integer.Sparse Key := [(key2079, -2), (key2079, -2), (key2077, -2), (key2085, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2077, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2176, 2), (key2176, 2), (key2174, 2), (key2187, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2174, 2), (key2187, 2), (key2176, 2), (key2176, 2)]

def rawRow8956 : Integer.Sparse Key := [(key2085, -2), (key2085, -2), (key2085, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2079, -2), (key2077, -2), (key2077, -2), (key2077, -2), (key2187, 2), (key2187, 2), (key2187, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2176, 2), (key2174, 2), (key2174, 2), (key2174, 2)]

def rawRow8957 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2176, -2), (key2274, -2), (key2276, -2), (key2274, -2), (key2279, -2), (key2276, -2), (key2279, -2), (key2341, -2), (key2341, -2), (key2343, -2), (key2077, 2), (key2079, 2), (key2079, 2), (key2274, 2), (key2276, 2), (key2274, 2), (key2287, 2), (key2276, 2), (key2287, 2), (key2341, 2), (key2341, 2), (key2347, 2)]

def rawRow8958 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2176, -2), (key2276, -2), (key2274, -2), (key2279, -2), (key2274, -2), (key2279, -2), (key2276, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2079, 2), (key2077, 2), (key2079, 2), (key2276, 2), (key2274, 2), (key2287, 2), (key2274, 2), (key2287, 2), (key2276, 2), (key2341, 2), (key2347, 2), (key2341, 2)]

def rawRow8959 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2174, -2), (key2279, -2), (key2279, -2), (key2276, -2), (key2276, -2), (key2274, -2), (key2274, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2079, 2), (key2079, 2), (key2077, 2), (key2287, 2), (key2287, 2), (key2276, 2), (key2276, 2), (key2274, 2), (key2274, 2), (key2347, 2), (key2341, 2), (key2341, 2)]

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

def rawRow8960 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2341, -2), (key2174, -2), (key2176, -2), (key2274, -2), (key2279, -2), (key2341, -2), (key2343, -2), (key2176, -2), (key2276, -2), (key2279, -2), (key2274, 2), (key2276, 2), (key2341, 2), (key2077, 2), (key2079, 2), (key2274, 2), (key2287, 2), (key2341, 2), (key2347, 2), (key2079, 2), (key2276, 2), (key2287, 2)]

def rawRow8961 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2341, -2), (key2176, -2), (key2174, -2), (key2279, -2), (key2274, -2), (key2343, -2), (key2341, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2276, 2), (key2274, 2), (key2341, 2), (key2079, 2), (key2077, 2), (key2287, 2), (key2274, 2), (key2347, 2), (key2341, 2), (key2079, 2), (key2287, 2), (key2276, 2)]

def rawRow8962 : Integer.Sparse Key := [(key2274, -2), (key2341, -2), (key2276, -2), (key2274, -2), (key2341, -2), (key2174, -2), (key2343, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2176, -2), (key2279, -2), (key2274, 2), (key2341, 2), (key2276, 2), (key2274, 2), (key2341, 2), (key2077, 2), (key2347, 2), (key2079, 2), (key2287, 2), (key2276, 2), (key2079, 2), (key2287, 2)]

def rawRow8963 : Integer.Sparse Key := [(key2341, -2), (key2274, -2), (key2276, -2), (key2341, -2), (key2274, -2), (key2343, -2), (key2174, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2279, -2), (key2176, -2), (key2341, 2), (key2274, 2), (key2276, 2), (key2341, 2), (key2274, 2), (key2347, 2), (key2077, 2), (key2287, 2), (key2079, 2), (key2276, 2), (key2287, 2), (key2079, 2)]

def rawRow8964 : Integer.Sparse Key := [(key2276, -2), (key2341, -2), (key2274, -2), (key2279, -2), (key2343, -2), (key2176, -2), (key2341, -2), (key2174, -2), (key2274, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2276, 2), (key2341, 2), (key2274, 2), (key2287, 2), (key2347, 2), (key2079, 2), (key2341, 2), (key2077, 2), (key2274, 2), (key2287, 2), (key2079, 2), (key2276, 2)]

def rawRow8965 : Integer.Sparse Key := [(key2341, -2), (key2276, -2), (key2274, -2), (key2343, -2), (key2279, -2), (key2341, -2), (key2176, -2), (key2274, -2), (key2174, -2), (key2279, -2), (key2276, -2), (key2176, -2), (key2341, 2), (key2276, 2), (key2274, 2), (key2347, 2), (key2287, 2), (key2341, 2), (key2079, 2), (key2274, 2), (key2077, 2), (key2287, 2), (key2276, 2), (key2079, 2)]

def rawRow8966 : Integer.Sparse Key := [(key2279, -2), (key2279, -2), (key2343, -2), (key2176, -2), (key2176, -2), (key2276, -2), (key2276, -2), (key2341, -2), (key2341, -2), (key2174, -2), (key2274, -2), (key2274, -2), (key2287, 2), (key2287, 2), (key2347, 2), (key2079, 2), (key2079, 2), (key2276, 2), (key2276, 2), (key2341, 2), (key2341, 2), (key2077, 2), (key2274, 2), (key2274, 2)]

def rawRow8967 : Integer.Sparse Key := [(key2279, -2), (key2343, -2), (key2279, -2), (key2276, -2), (key2341, -2), (key2176, -2), (key2341, -2), (key2176, -2), (key2276, -2), (key2274, -2), (key2174, -2), (key2274, -2), (key2287, 2), (key2347, 2), (key2287, 2), (key2276, 2), (key2341, 2), (key2079, 2), (key2341, 2), (key2079, 2), (key2276, 2), (key2274, 2), (key2077, 2), (key2274, 2)]

def rawRow8968 : Integer.Sparse Key := [(key2343, -2), (key2279, -2), (key2279, -2), (key2341, -2), (key2276, -2), (key2341, -2), (key2176, -2), (key2276, -2), (key2176, -2), (key2274, -2), (key2274, -2), (key2174, -2), (key2347, 2), (key2287, 2), (key2287, 2), (key2341, 2), (key2276, 2), (key2341, 2), (key2079, 2), (key2276, 2), (key2079, 2), (key2274, 2), (key2274, 2), (key2077, 2)]

def rawRow8969 : Integer.Sparse Key := [(key817, -2), (key818, -2), (key818, -2), (key817, -2), (key818, -2), (key817, -2), (key825, -2), (key818, -2), (key825, -2), (key818, -2), (key818, -2), (key825, -2), (key897, 1), (key898, 1), (key897, 1), (key902, 1), (key898, 1), (key902, 1), (key897, 1), (key898, 1), (key897, 1), (key908, 1), (key898, 1), (key908, 1), (key897, 1), (key902, 1), (key897, 1), (key908, 1), (key902, 1), (key908, 1), (key898, 1), (key902, 1), (key898, 1), (key908, 1), (key902, 1), (key908, 1)]

def rawRow8970 : Integer.Sparse Key := [(key818, -2), (key817, -2), (key818, -2), (key818, -2), (key817, -2), (key825, -2), (key817, -2), (key825, -2), (key818, -2), (key818, -2), (key825, -2), (key818, -2), (key898, 1), (key897, 1), (key902, 1), (key897, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key898, 1), (key902, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key908, 1), (key898, 1), (key908, 1), (key902, 1)]

def rawRow8971 : Integer.Sparse Key := [(key818, -2), (key818, -2), (key817, -2), (key825, -2), (key825, -2), (key818, -2), (key818, -2), (key817, -2), (key817, -2), (key825, -2), (key818, -2), (key818, -2), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key897, 1), (key897, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1)]

def rawRow8972 : Integer.Sparse Key := [(key825, -2), (key825, -2), (key825, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key818, -2), (key817, -2), (key817, -2), (key817, -2), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key902, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key898, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1), (key897, 1)]

def rawRow8973 : Integer.Sparse Key := [(key737, -2), (key738, -2), (key738, -2), (key897, -2), (key898, -2), (key897, -2), (key908, -2), (key898, -2), (key908, -2), (key960, -2), (key960, -2), (key964, -2), (key737, 1), (key738, 1), (key737, 1), (key743, 1), (key738, 1), (key743, 1), (key817, 1), (key818, 1), (key817, 1), (key825, 1), (key818, 1), (key825, 1), (key897, 1), (key902, 1), (key897, 1), (key908, 1), (key902, 1), (key908, 1), (key960, 1), (key962, 1), (key960, 1), (key964, 1), (key962, 1), (key964, 1)]

def rawRow8974 : Integer.Sparse Key := [(key738, -2), (key737, -2), (key738, -2), (key898, -2), (key897, -2), (key908, -2), (key897, -2), (key908, -2), (key898, -2), (key960, -2), (key964, -2), (key960, -2), (key738, 1), (key737, 1), (key743, 1), (key737, 1), (key743, 1), (key738, 1), (key818, 1), (key817, 1), (key825, 1), (key817, 1), (key825, 1), (key818, 1), (key902, 1), (key897, 1), (key908, 1), (key897, 1), (key908, 1), (key902, 1), (key962, 1), (key960, 1), (key964, 1), (key960, 1), (key964, 1), (key962, 1)]

def rawRow8975 : Integer.Sparse Key := [(key738, -2), (key738, -2), (key737, -2), (key908, -2), (key908, -2), (key898, -2), (key898, -2), (key897, -2), (key897, -2), (key964, -2), (key960, -2), (key960, -2), (key743, 1), (key743, 1), (key738, 1), (key738, 1), (key737, 1), (key737, 1), (key825, 1), (key825, 1), (key818, 1), (key818, 1), (key817, 1), (key817, 1), (key908, 1), (key908, 1), (key902, 1), (key902, 1), (key897, 1), (key897, 1), (key964, 1), (key964, 1), (key962, 1), (key962, 1), (key960, 1), (key960, 1)]

def rawRow8976 : Integer.Sparse Key := [(key897, -2), (key898, -2), (key960, -2), (key737, -2), (key738, -2), (key897, -2), (key908, -2), (key960, -2), (key964, -2), (key738, -2), (key898, -2), (key908, -2), (key817, 1), (key818, 1), (key897, 1), (key902, 1), (key960, 1), (key962, 1), (key737, 1), (key738, 1), (key897, 1), (key908, 1), (key960, 1), (key964, 1), (key737, 1), (key743, 1), (key817, 1), (key825, 1), (key962, 1), (key964, 1), (key738, 1), (key743, 1), (key818, 1), (key825, 1), (key902, 1), (key908, 1)]

def rawRow8977 : Integer.Sparse Key := [(key898, -2), (key897, -2), (key960, -2), (key738, -2), (key737, -2), (key908, -2), (key897, -2), (key964, -2), (key960, -2), (key738, -2), (key908, -2), (key898, -2), (key818, 1), (key817, 1), (key902, 1), (key897, 1), (key962, 1), (key960, 1), (key738, 1), (key737, 1), (key908, 1), (key897, 1), (key964, 1), (key960, 1), (key743, 1), (key737, 1), (key825, 1), (key817, 1), (key964, 1), (key962, 1), (key743, 1), (key738, 1), (key825, 1), (key818, 1), (key908, 1), (key902, 1)]

def rawRow8978 : Integer.Sparse Key := [(key897, -2), (key960, -2), (key898, -2), (key897, -2), (key960, -2), (key737, -2), (key964, -2), (key738, -2), (key908, -2), (key898, -2), (key738, -2), (key908, -2), (key897, 1), (key960, 1), (key817, 1), (key962, 1), (key818, 1), (key902, 1), (key897, 1), (key960, 1), (key737, 1), (key964, 1), (key738, 1), (key908, 1), (key817, 1), (key962, 1), (key737, 1), (key964, 1), (key743, 1), (key825, 1), (key818, 1), (key902, 1), (key738, 1), (key908, 1), (key743, 1), (key825, 1)]

def rawRow8979 : Integer.Sparse Key := [(key960, -2), (key897, -2), (key898, -2), (key960, -2), (key897, -2), (key964, -2), (key737, -2), (key908, -2), (key738, -2), (key898, -2), (key908, -2), (key738, -2), (key960, 1), (key897, 1), (key962, 1), (key817, 1), (key902, 1), (key818, 1), (key960, 1), (key897, 1), (key964, 1), (key737, 1), (key908, 1), (key738, 1), (key962, 1), (key817, 1), (key964, 1), (key737, 1), (key825, 1), (key743, 1), (key902, 1), (key818, 1), (key908, 1), (key738, 1), (key825, 1), (key743, 1)]

def rawRow8980 : Integer.Sparse Key := [(key898, -2), (key960, -2), (key897, -2), (key908, -2), (key964, -2), (key738, -2), (key960, -2), (key737, -2), (key897, -2), (key908, -2), (key738, -2), (key898, -2), (key902, 1), (key962, 1), (key818, 1), (key960, 1), (key817, 1), (key897, 1), (key908, 1), (key964, 1), (key738, 1), (key960, 1), (key737, 1), (key897, 1), (key825, 1), (key964, 1), (key743, 1), (key962, 1), (key737, 1), (key817, 1), (key825, 1), (key908, 1), (key743, 1), (key902, 1), (key738, 1), (key818, 1)]

def rawRow8981 : Integer.Sparse Key := [(key960, -2), (key898, -2), (key897, -2), (key964, -2), (key908, -2), (key960, -2), (key738, -2), (key897, -2), (key737, -2), (key908, -2), (key898, -2), (key738, -2), (key962, 1), (key902, 1), (key960, 1), (key818, 1), (key897, 1), (key817, 1), (key964, 1), (key908, 1), (key960, 1), (key738, 1), (key897, 1), (key737, 1), (key964, 1), (key825, 1), (key962, 1), (key743, 1), (key817, 1), (key737, 1), (key908, 1), (key825, 1), (key902, 1), (key743, 1), (key818, 1), (key738, 1)]

def rawRow8982 : Integer.Sparse Key := [(key908, -2), (key908, -2), (key964, -2), (key738, -2), (key738, -2), (key898, -2), (key898, -2), (key960, -2), (key960, -2), (key737, -2), (key897, -2), (key897, -2), (key825, 1), (key825, 1), (key908, 1), (key908, 1), (key964, 1), (key964, 1), (key743, 1), (key743, 1), (key902, 1), (key902, 1), (key962, 1), (key962, 1), (key738, 1), (key738, 1), (key818, 1), (key818, 1), (key960, 1), (key960, 1), (key737, 1), (key737, 1), (key817, 1), (key817, 1), (key897, 1), (key897, 1)]

def rawRow8983 : Integer.Sparse Key := [(key908, -2), (key964, -2), (key908, -2), (key898, -2), (key960, -2), (key738, -2), (key960, -2), (key738, -2), (key898, -2), (key897, -2), (key737, -2), (key897, -2), (key908, 1), (key964, 1), (key825, 1), (key964, 1), (key825, 1), (key908, 1), (key902, 1), (key962, 1), (key743, 1), (key962, 1), (key743, 1), (key902, 1), (key818, 1), (key960, 1), (key738, 1), (key960, 1), (key738, 1), (key818, 1), (key817, 1), (key897, 1), (key737, 1), (key897, 1), (key737, 1), (key817, 1)]

def rawRow8984 : Integer.Sparse Key := [(key964, -2), (key908, -2), (key908, -2), (key960, -2), (key898, -2), (key960, -2), (key738, -2), (key898, -2), (key738, -2), (key897, -2), (key897, -2), (key737, -2), (key964, 1), (key908, 1), (key964, 1), (key825, 1), (key908, 1), (key825, 1), (key962, 1), (key902, 1), (key962, 1), (key743, 1), (key902, 1), (key743, 1), (key960, 1), (key818, 1), (key960, 1), (key738, 1), (key818, 1), (key738, 1), (key897, 1), (key817, 1), (key897, 1), (key737, 1), (key817, 1), (key737, 1)]

def rawRow8985 : Integer.Sparse Key := [(key2274, 1), (key2276, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2347, -2), (key2343, -2), (key2347, -2)]

def rawRow8986 : Integer.Sparse Key := [(key2276, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2276, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2287, 1), (key2276, 1), (key2287, 1), (key2279, 1), (key2341, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2343, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2347, -2), (key2343, -2)]

def rawRow8987 : Integer.Sparse Key := [(key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2343, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2341, -2), (key2341, -2), (key2347, -2), (key2347, -2), (key2343, -2), (key2343, -2), (key2341, -2), (key2341, -2)]

def rawRow8988 : Integer.Sparse Key := [(key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2279, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2276, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2274, 1), (key2347, -2), (key2347, -2), (key2347, -2), (key2343, -2), (key2343, -2), (key2343, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2), (key2341, -2)]

def rawRow8989 : Integer.Sparse Key := [(key2077, 1), (key2079, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2085, 1), (key2174, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2187, 1), (key2274, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2287, 1), (key2341, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2347, 1), (key2079, -2), (key2079, -2), (key2085, -2), (key2176, -2), (key2176, -2), (key2187, -2), (key2276, -2), (key2279, -2), (key2276, -2), (key2287, -2), (key2279, -2), (key2287, -2)]

def rawRow8990 : Integer.Sparse Key := [(key2079, 1), (key2077, 1), (key2085, 1), (key2077, 1), (key2085, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2187, 1), (key2174, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2287, 1), (key2274, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2341, 1), (key2347, 1), (key2341, 1), (key2347, 1), (key2343, 1), (key2079, -2), (key2085, -2), (key2079, -2), (key2176, -2), (key2187, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2287, -2), (key2276, -2), (key2287, -2), (key2279, -2)]

def rawRow8991 : Integer.Sparse Key := [(key2085, 1), (key2085, 1), (key2079, 1), (key2079, 1), (key2077, 1), (key2077, 1), (key2187, 1), (key2187, 1), (key2176, 1), (key2176, 1), (key2174, 1), (key2174, 1), (key2287, 1), (key2287, 1), (key2279, 1), (key2279, 1), (key2274, 1), (key2274, 1), (key2347, 1), (key2347, 1), (key2343, 1), (key2343, 1), (key2341, 1), (key2341, 1), (key2085, -2), (key2079, -2), (key2079, -2), (key2187, -2), (key2176, -2), (key2176, -2), (key2287, -2), (key2287, -2), (key2279, -2), (key2279, -2), (key2276, -2), (key2276, -2)]

def rawRow8992 : Integer.Sparse Key := [(key2174, 1), (key2176, 1), (key2274, 1), (key2279, 1), (key2341, 1), (key2343, 1), (key2077, 1), (key2079, 1), (key2274, 1), (key2287, 1), (key2341, 1), (key2347, 1), (key2077, 1), (key2085, 1), (key2174, 1), (key2187, 1), (key2343, 1), (key2347, 1), (key2079, 1), (key2085, 1), (key2176, 1), (key2187, 1), (key2279, 1), (key2287, 1), (key2176, -2), (key2276, -2), (key2279, -2), (key2079, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2085, -2), (key2176, -2), (key2187, -2), (key2279, -2), (key2287, -2)]

def rawRow8993 : Integer.Sparse Key := [(key2176, 1), (key2174, 1), (key2279, 1), (key2274, 1), (key2343, 1), (key2341, 1), (key2079, 1), (key2077, 1), (key2287, 1), (key2274, 1), (key2347, 1), (key2341, 1), (key2085, 1), (key2077, 1), (key2187, 1), (key2174, 1), (key2347, 1), (key2343, 1), (key2085, 1), (key2079, 1), (key2187, 1), (key2176, 1), (key2287, 1), (key2279, 1), (key2176, -2), (key2279, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2276, -2), (key2085, -2), (key2079, -2), (key2187, -2), (key2176, -2), (key2287, -2), (key2279, -2)]

def rawRow8994 : Integer.Sparse Key := [(key2274, 1), (key2341, 1), (key2174, 1), (key2343, 1), (key2176, 1), (key2279, 1), (key2274, 1), (key2341, 1), (key2077, 1), (key2347, 1), (key2079, 1), (key2287, 1), (key2174, 1), (key2343, 1), (key2077, 1), (key2347, 1), (key2085, 1), (key2187, 1), (key2176, 1), (key2279, 1), (key2079, 1), (key2287, 1), (key2085, 1), (key2187, 1), (key2276, -2), (key2176, -2), (key2279, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2176, -2), (key2279, -2), (key2079, -2), (key2287, -2), (key2085, -2), (key2187, -2)]

def rawRow8995 : Integer.Sparse Key := [(key2341, 1), (key2274, 1), (key2343, 1), (key2174, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2274, 1), (key2347, 1), (key2077, 1), (key2287, 1), (key2079, 1), (key2343, 1), (key2174, 1), (key2347, 1), (key2077, 1), (key2187, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2287, 1), (key2079, 1), (key2187, 1), (key2085, 1), (key2276, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2279, -2), (key2176, -2), (key2287, -2), (key2079, -2), (key2187, -2), (key2085, -2)]

def rawRow8996 : Integer.Sparse Key := [(key2279, 1), (key2343, 1), (key2176, 1), (key2341, 1), (key2174, 1), (key2274, 1), (key2287, 1), (key2347, 1), (key2079, 1), (key2341, 1), (key2077, 1), (key2274, 1), (key2187, 1), (key2347, 1), (key2085, 1), (key2343, 1), (key2077, 1), (key2174, 1), (key2187, 1), (key2287, 1), (key2085, 1), (key2279, 1), (key2079, 1), (key2176, 1), (key2279, -2), (key2176, -2), (key2276, -2), (key2287, -2), (key2079, -2), (key2276, -2), (key2187, -2), (key2287, -2), (key2085, -2), (key2279, -2), (key2079, -2), (key2176, -2)]

def rawRow8997 : Integer.Sparse Key := [(key2343, 1), (key2279, 1), (key2341, 1), (key2176, 1), (key2274, 1), (key2174, 1), (key2347, 1), (key2287, 1), (key2341, 1), (key2079, 1), (key2274, 1), (key2077, 1), (key2347, 1), (key2187, 1), (key2343, 1), (key2085, 1), (key2174, 1), (key2077, 1), (key2287, 1), (key2187, 1), (key2279, 1), (key2085, 1), (key2176, 1), (key2079, 1), (key2279, -2), (key2276, -2), (key2176, -2), (key2287, -2), (key2276, -2), (key2079, -2), (key2287, -2), (key2187, -2), (key2279, -2), (key2085, -2), (key2176, -2), (key2079, -2)]

def rawRow8998 : Integer.Sparse Key := [(key2187, 1), (key2187, 1), (key2287, 1), (key2287, 1), (key2347, 1), (key2347, 1), (key2085, 1), (key2085, 1), (key2279, 1), (key2279, 1), (key2343, 1), (key2343, 1), (key2079, 1), (key2079, 1), (key2176, 1), (key2176, 1), (key2341, 1), (key2341, 1), (key2077, 1), (key2077, 1), (key2174, 1), (key2174, 1), (key2274, 1), (key2274, 1), (key2187, -2), (key2287, -2), (key2287, -2), (key2085, -2), (key2279, -2), (key2279, -2), (key2079, -2), (key2079, -2), (key2176, -2), (key2176, -2), (key2276, -2), (key2276, -2)]

def rawRow8999 : Integer.Sparse Key := [(key2287, 1), (key2347, 1), (key2187, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2287, -2), (key2187, -2), (key2287, -2), (key2279, -2), (key2085, -2), (key2279, -2), (key2176, -2), (key2276, -2), (key2079, -2), (key2276, -2), (key2079, -2), (key2176, -2)]

def rawRow9000 : Integer.Sparse Key := [(key2347, 1), (key2287, 1), (key2347, 1), (key2187, 1), (key2287, 1), (key2187, 1), (key2343, 1), (key2279, 1), (key2343, 1), (key2085, 1), (key2279, 1), (key2085, 1), (key2341, 1), (key2176, 1), (key2341, 1), (key2079, 1), (key2176, 1), (key2079, 1), (key2274, 1), (key2174, 1), (key2274, 1), (key2077, 1), (key2174, 1), (key2077, 1), (key2287, -2), (key2287, -2), (key2187, -2), (key2279, -2), (key2279, -2), (key2085, -2), (key2276, -2), (key2176, -2), (key2276, -2), (key2079, -2), (key2176, -2), (key2079, -2)]

def rawRow9001 : Integer.Sparse Key := [(key843, -6), (key843, -6), (key843, -6), (key844, -6), (key943, 2), (key943, 2), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key944, 2), (key945, 2)]

def rawRow9002 : Integer.Sparse Key := [(key843, -6), (key843, -6), (key844, -6), (key843, -6), (key943, 2), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key943, 2), (key945, 2), (key944, 2)]

def rawRow9003 : Integer.Sparse Key := [(key843, -6), (key844, -6), (key843, -6), (key843, -6), (key944, 2), (key943, 2), (key943, 2), (key945, 2), (key943, 2), (key943, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2)]

def rawRow9004 : Integer.Sparse Key := [(key844, -6), (key843, -6), (key843, -6), (key843, -6), (key945, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2), (key943, 2)]

def rawRow9005 : Integer.Sparse Key := [(key754, -6), (key943, -6), (key943, -6), (key945, -6), (key754, 2), (key754, 2), (key755, 2), (key843, 2), (key843, 2), (key844, 2), (key943, 2), (key944, 2), (key943, 2), (key945, 2), (key944, 2), (key945, 2)]

def rawRow9006 : Integer.Sparse Key := [(key754, -6), (key943, -6), (key945, -6), (key943, -6), (key754, 2), (key755, 2), (key754, 2), (key843, 2), (key844, 2), (key843, 2), (key944, 2), (key943, 2), (key945, 2), (key943, 2), (key945, 2), (key944, 2)]

def rawRow9007 : Integer.Sparse Key := [(key754, -6), (key945, -6), (key943, -6), (key943, -6), (key755, 2), (key754, 2), (key754, 2), (key844, 2), (key843, 2), (key843, 2), (key945, 2), (key945, 2), (key944, 2), (key944, 2), (key943, 2), (key943, 2)]

def rawRow9008 : Integer.Sparse Key := [(key943, -6), (key754, -6), (key943, -6), (key945, -6), (key843, 2), (key943, 2), (key944, 2), (key754, 2), (key943, 2), (key945, 2), (key754, 2), (key755, 2), (key843, 2), (key844, 2), (key944, 2), (key945, 2)]

def rawRow9009 : Integer.Sparse Key := [(key943, -6), (key754, -6), (key945, -6), (key943, -6), (key843, 2), (key944, 2), (key943, 2), (key754, 2), (key945, 2), (key943, 2), (key755, 2), (key754, 2), (key844, 2), (key843, 2), (key945, 2), (key944, 2)]

def rawRow9010 : Integer.Sparse Key := [(key943, -6), (key943, -6), (key754, -6), (key945, -6), (key943, 2), (key843, 2), (key944, 2), (key943, 2), (key754, 2), (key945, 2), (key843, 2), (key944, 2), (key754, 2), (key945, 2), (key755, 2), (key844, 2)]

def rawRow9011 : Integer.Sparse Key := [(key943, -6), (key943, -6), (key945, -6), (key754, -6), (key943, 2), (key944, 2), (key843, 2), (key943, 2), (key945, 2), (key754, 2), (key944, 2), (key843, 2), (key945, 2), (key754, 2), (key844, 2), (key755, 2)]

def rawRow9012 : Integer.Sparse Key := [(key943, -6), (key945, -6), (key754, -6), (key943, -6), (key944, 2), (key843, 2), (key943, 2), (key945, 2), (key754, 2), (key943, 2), (key844, 2), (key945, 2), (key755, 2), (key944, 2), (key754, 2), (key843, 2)]

def rawRow9013 : Integer.Sparse Key := [(key943, -6), (key945, -6), (key943, -6), (key754, -6), (key944, 2), (key943, 2), (key843, 2), (key945, 2), (key943, 2), (key754, 2), (key945, 2), (key844, 2), (key944, 2), (key755, 2), (key843, 2), (key754, 2)]

def rawRow9014 : Integer.Sparse Key := [(key945, -6), (key754, -6), (key943, -6), (key943, -6), (key844, 2), (key945, 2), (key945, 2), (key755, 2), (key944, 2), (key944, 2), (key754, 2), (key754, 2), (key843, 2), (key843, 2), (key943, 2), (key943, 2)]

def rawRow9015 : Integer.Sparse Key := [(key945, -6), (key943, -6), (key754, -6), (key943, -6), (key945, 2), (key844, 2), (key945, 2), (key944, 2), (key755, 2), (key944, 2), (key843, 2), (key943, 2), (key754, 2), (key943, 2), (key754, 2), (key843, 2)]

def rawRow9016 : Integer.Sparse Key := [(key945, -6), (key943, -6), (key943, -6), (key754, -6), (key945, 2), (key945, 2), (key844, 2), (key944, 2), (key944, 2), (key755, 2), (key943, 2), (key843, 2), (key943, 2), (key754, 2), (key843, 2), (key754, 2)]

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

def rawRow9157 : Integer.Sparse Key := [(key713, -6), (key715, -6), (key715, -6), (key715, -6), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key892, 2), (key890, 2), (key959, 2), (key892, 2), (key959, 2), (key892, 2), (key892, 2), (key959, 2)]

def rawRow9158 : Integer.Sparse Key := [(key715, -6), (key713, -6), (key715, -6), (key715, -6), (key892, 2), (key890, 2), (key892, 2), (key892, 2), (key890, 2), (key959, 2), (key890, 2), (key959, 2), (key892, 2), (key892, 2), (key959, 2), (key892, 2)]

def rawRow9159 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key713, -6), (key715, -6), (key892, 2), (key892, 2), (key890, 2), (key959, 2), (key959, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key959, 2), (key892, 2), (key892, 2)]

def rawRow9160 : Integer.Sparse Key := [(key715, -6), (key715, -6), (key715, -6), (key713, -6), (key959, 2), (key959, 2), (key959, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key890, 2), (key890, 2), (key890, 2)]

def rawRow9161 : Integer.Sparse Key := [(key959, -6), (key959, -6), (key959, -6), (key966, -6), (key715, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key892, 2), (key914, 2), (key914, 2), (key914, 2)]

def rawRow9162 : Integer.Sparse Key := [(key959, -6), (key959, -6), (key966, -6), (key959, -6), (key892, 2), (key892, 2), (key914, 2), (key715, 2), (key715, 2), (key892, 2), (key892, 2), (key914, 2), (key914, 2), (key715, 2), (key892, 2), (key892, 2)]

def rawRow9163 : Integer.Sparse Key := [(key959, -6), (key966, -6), (key959, -6), (key959, -6), (key892, 2), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key715, 2), (key914, 2), (key715, 2), (key892, 2), (key892, 2), (key715, 2), (key892, 2)]

def rawRow9164 : Integer.Sparse Key := [(key966, -6), (key959, -6), (key959, -6), (key959, -6), (key914, 2), (key892, 2), (key892, 2), (key914, 2), (key892, 2), (key914, 2), (key715, 2), (key892, 2), (key715, 2), (key892, 2), (key892, 2), (key715, 2)]

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

def rawRow9385 : Integer.Sparse Key := [(key989, -24), (key1024, 6), (key1102, 6), (key1102, 6), (key1102, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def combined245_part2 : Sparse := [([1, 2, -1, -1, 0, 0, 0], -9)]

end MUB6.TaoCertificate

end OAI
end


