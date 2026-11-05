-- Prove2me | Definitions.Def_OAIQ106E015
-- name    : OAIQ106E015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T18:46:23.663298+00:00
-- url     : https://prove2.me/theorems/e5dbaa4e-e4c0-4fff-bb4e-9849723a32c8
-- title:
--   Definitions bundle OAIQ106E015 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2854 declarations of OpenAI's Lean: 2854 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.row1000`, `OAI.MUB6.Certificate.GramRows.row1001`, `OAI.MUB6.Certificate.GramRows.row1002`, `OAI.MUB6.Certificate.GramRows.row1003`, `OAI.MUB6.Certificate.GramRows.row1004`, `OAI.MUB6.Certificate.GramRows.row1005`, `OAI.MUB6.Certificate.GramRows.row1006`, `OAI.MUB6.Certificate.GramRows.row1007`, `OAI.MUB6.Certificate.GramRows.row1008`, `OAI.MUB6.Certificate.GramRows.row1009`, `OAI.MUB6.Certificate.GramRows.row1010`, `OAI.MUB6.Certificate.GramRows.row1011`, `OAI.MUB6.Certificate.GramRows.row1012`, `OAI.MUB6.Certificate.GramRows.row1013`, `OAI.MUB6.Certificate.GramRows.row1014`, `OAI.MUB6.Certificate.GramRows.row1015`, `OAI.MUB6.Certificate.GramRows.row1016`, `OAI.MUB6.Certificate.GramRows.row1017`, `OAI.MUB6.Certificate.GramRows.row1018`, `OAI.MUB6.Certificate.GramRows.row1019`, `OAI.MUB6.Certificate.GramRows.row1020`, `OAI.MUB6.Certificate.GramRows.row1021`, `OAI.MUB6.Certificate.GramRows.row1022`, `OAI.MUB6.Certificate.GramRows.row1023`, `OAI.MUB6.Certificate.GramRows.row1024`, `OAI.MUB6.Certificate.GramRows.row1025`, `OAI.MUB6.Certificate.GramRows.row1026`, `OAI.MUB6.Certificate.GramRows.row1027`, `OAI.MUB6.Certificate.GramRows.row1028`, `OAI.MUB6.Certificate.GramRows.row1029`, `OAI.MUB6.Certificate.GramRows.row1030`, `OAI.MUB6.Certificate.GramRows.row1031`, `OAI.MUB6.Certificate.GramRows.row1032`, `OAI.MUB6.Certificate.GramRows.row1033`, `OAI.MUB6.Certificate.GramRows.row1034`, `OAI.MUB6.Certificate.GramRows.row1035`, `OAI.MUB6.Certificate.GramRows.row1036`, `OAI.MUB6.Certificate.GramRows.row1037`, `OAI.MUB6.Certificate.GramRows.row1038`, `OAI.MUB6.Certificate.GramRows.row1039` and 2814 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block17`, `MutuallyUnbiased_GramRows_Block18`, `MutuallyUnbiased_GramRows_Block19`, `MutuallyUnbiased_GramRows_Block20`, `MutuallyUnbiased_GramRows_Block21`, `MutuallyUnbiased_GramRows_Block22`, `MutuallyUnbiased_GramRows_Block23`, `MutuallyUnbiased_GramRows_Block24`, `MutuallyUnbiased_GramRows_Block25`, `MutuallyUnbiased_GramRows_Block26`, `MutuallyUnbiased_GramRows_Block27`, `MutuallyUnbiased_GramRows_Block28`, `MutuallyUnbiased_GramRows_Block29`, `MutuallyUnbiased_GramRows_Block30`, `MutuallyUnbiased_GramRows_Block31`, `MutuallyUnbiased_GramRows_Block32`, `MutuallyUnbiased_GramRows_Block33`, `MutuallyUnbiased_GramRows_Block34`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_GramRows_Block48`, `MutuallyUnbiased_GramRows_Block49`, `MutuallyUnbiased_GramRows_Block50`, `MutuallyUnbiased_GramRows_Block51`, `MutuallyUnbiased_GramRows_Block52`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block54`, `MutuallyUnbiased_GramRows_Block55`, `MutuallyUnbiased_GramRows_Block56`, `MutuallyUnbiased_GramRows_Block57`, `MutuallyUnbiased_GramRows_Block58`, `MutuallyUnbiased_GramRows_Block59`, `MutuallyUnbiased_GramRows_Block60`, `MutuallyUnbiased_GramRows_Block61`, `MutuallyUnbiased_GramRows_Block62`, `MutuallyUnbiased_GramRows_Block63`, `MutuallyUnbiased_GramRows_Block64`.
--
--   **Imports.** It imports the bundles `OAIQ106E000` and `OAIQ106E002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E016`, `OAIQ106E017`, `OAIQ106E019`, `OAIQ106E020`, `OAIQ106E022` and `OAIQ106E024`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E000
import Definitions.Def_OAIQ106E002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row660 : Integer.Sparse Key := [(key1422, -6), (key1453, 6), (key1571, 6), (key1653, -6), (key1786, -6), (key1811, 6)]

def row661 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row662 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row663 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row664 : Integer.Sparse Key := [(key1422, 6), (key1453, -6), (key1571, -6), (key1653, 6), (key1786, 6), (key1811, -6)]

def row665 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row666 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row667 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row668 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row669 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row670 : Integer.Sparse Key := [(key1422, -2), (key1453, 2), (key1571, 2), (key1653, -2), (key1786, -2), (key1811, 2)]

def row671 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

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

def row672 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row673 : Integer.Sparse Key := [(key1422, 2), (key1453, -2), (key1571, -2), (key1653, 2), (key1786, 2), (key1811, -2)]

def row674 : Integer.Sparse Key := [(key234, -6), (key246, 6), (key300, 6), (key314, -6), (key383, -6), (key404, 6)]

def row675 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row676 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row677 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row678 : Integer.Sparse Key := [(key234, 6), (key246, -6), (key300, -6), (key314, 12), (key404, -6)]

def row679 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

def row680 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

def row681 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, -4), (key404, 2)]

def row682 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

def row683 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

def row684 : Integer.Sparse Key := [(key234, -2), (key246, 2), (key300, 2), (key314, 2), (key383, -6), (key404, 2)]

def row685 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row686 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row687 : Integer.Sparse Key := [(key234, 2), (key246, -2), (key300, -2), (key314, 2), (key383, 2), (key404, -2)]

def row688 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

def row689 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

def row690 : Integer.Sparse Key := [(key2702, -4), (key2728, -2), (key2735, 2), (key2737, 2), (key2747, 2), (key2805, 4), (key2831, 2), (key2893, -2), (key2897, -2), (key2904, -2), (key2948, -2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, 2), (key2983, 2)]

def row691 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row692 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row693 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row694 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row695 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row696 : Integer.Sparse Key := [(key2667, -1), (key2673, 1), (key2702, 1), (key2728, 1), (key2735, -2), (key2737, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, -1), (key2904, 1), (key2938, -1), (key2943, 1), (key2948, 1), (key2960, 1), (key2972, -1), (key2983, -1), (key2997, -1), (key2998, 1)]

def row697 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

def row698 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

def row699 : Integer.Sparse Key := [(key2702, 4), (key2728, 2), (key2735, -2), (key2737, -2), (key2747, -2), (key2805, -4), (key2831, -2), (key2893, 2), (key2897, 2), (key2904, 2), (key2948, 2), (key2950, 2), (key2960, 2), (key2972, -2), (key2976, -2), (key2983, -2)]

def row700 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2831, 1), (key2893, -1), (key2904, -1), (key2948, -2), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

def row701 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2831, 1), (key2893, -1), (key2904, -1), (key2948, -2), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

def row702 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

def row703 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, -1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1)]

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

def row704 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1), (key3017, -2)]

def row705 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, -1), (key2728, -1), (key2735, 1), (key2747, 1), (key2805, 1), (key2829, -2), (key2831, 1), (key2893, -1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, 1), (key2997, -1), (key2998, 1), (key3017, -2)]

def row706 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row707 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row708 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row709 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row710 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row711 : Integer.Sparse Key := [(key2667, 1), (key2673, -1), (key2702, -1), (key2706, -2), (key2726, 1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, -1), (key2747, 1), (key2782, 1), (key2795, 1), (key2805, 1), (key2831, 1), (key2860, -2), (key2870, 1), (key2885, 1), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row712 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2948, 2), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row713 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2948, 2), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row714 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row715 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, 1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3023, 1), (key3026, -2), (key3030, 1)]

def row716 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

def row717 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2702, 1), (key2728, 1), (key2735, -1), (key2747, -1), (key2805, -1), (key2829, 2), (key2831, -1), (key2860, 1), (key2870, -2), (key2885, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1), (key3017, 2), (key3023, 1), (key3026, -2), (key3030, 1)]

def row718 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

def row719 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

def row720 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

def row721 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row722 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row723 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row724 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row725 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row726 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

def row727 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row728 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row729 : Integer.Sparse Key := [(key1289, 6), (key1309, -4), (key1350, -2), (key1384, -6), (key1417, 4), (key1471, 2), (key1539, 4), (key1566, -4), (key1895, 2), (key1902, -2)]

def row730 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row731 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row732 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row733 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row734 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

def row735 : Integer.Sparse Key := [(key1289, -2), (key1309, 2), (key1384, 2), (key1417, -4), (key1471, 2), (key1539, -2), (key1566, 4), (key1680, -2), (key1902, -2), (key1917, 2)]

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

def row736 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row737 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row738 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row739 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row740 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row741 : Integer.Sparse Key := [(key1289, -2), (key1309, 4), (key1350, -2), (key1384, 2), (key1417, -2), (key1539, -4), (key1566, 2), (key1680, 2), (key1895, 2), (key1917, -2)]

def row742 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row743 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row744 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row745 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row746 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row747 : Integer.Sparse Key := [(key1289, 2), (key1309, -2), (key1384, -2), (key1417, 4), (key1471, -2), (key1539, 2), (key1566, -4), (key1680, 2), (key1902, 2), (key1917, -2)]

def row748 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

def row749 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

def row750 : Integer.Sparse Key := [(key2608, -2), (key2614, -4), (key2624, 2), (key2630, 2), (key2638, 2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 2), (key2807, 2), (key2827, 2)]

def row751 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row752 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row753 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row754 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row755 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row756 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -2), (key2638, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1)]

def row757 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

def row758 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

def row759 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, -4), (key2698, 4), (key2704, 4), (key2724, 2), (key2752, 2), (key2801, -2), (key2807, -2), (key2827, -2)]

def row760 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row761 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row762 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2858, -1), (key2868, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row763 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2858, -1), (key2868, 1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row764 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row765 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 1), (key2663, 1), (key2669, 1), (key2698, -2), (key2704, -3), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, 1), (key2807, 2), (key2827, 1), (key2858, -1), (key2868, 1), (key3011, -1), (key3016, -1), (key3022, -1), (key3025, 1)]

def row766 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row767 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

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

def row768 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row769 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row770 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row771 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, 1), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, 1), (key2807, 1), (key2918, 1), (key2919, 1), (key3021, -1), (key3022, -1)]

def row772 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row773 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row774 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2918, 1), (key2922, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row775 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2918, 1), (key2922, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row776 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row777 : Integer.Sparse Key := [(key2608, 1), (key2614, 1), (key2624, -1), (key2630, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -2), (key2827, -1), (key2918, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, -1), (key3025, -1)]

def row778 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row779 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row780 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row781 : Integer.Sparse Key := [(key1033, 6), (key1041, -6), (key1111, -6), (key1127, 6), (key1193, 6), (key1199, -6)]

def row782 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row783 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row784 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row785 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row786 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row787 : Integer.Sparse Key := [(key1033, -2), (key1041, 2), (key1111, 2), (key1127, -2), (key1193, -2), (key1199, 2)]

def row788 : Integer.Sparse Key := [(key1033, -6), (key1041, 6), (key1111, 6), (key1127, -6), (key1193, -6), (key1199, 6)]

def row789 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row790 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row791 : Integer.Sparse Key := [(key1033, 2), (key1041, -2), (key1111, -2), (key1127, 2), (key1193, 2), (key1199, -2)]

def row792 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row793 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row794 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row795 : Integer.Sparse Key := [(key20, 6), (key31, -6), (key45, -6), (key70, 6), (key111, 6), (key133, -6)]

def row796 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row797 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row798 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row799 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

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

def row800 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row801 : Integer.Sparse Key := [(key20, -2), (key31, 2), (key45, 2), (key70, -2), (key111, -2), (key133, 2)]

def row802 : Integer.Sparse Key := [(key20, -6), (key31, 6), (key45, 6), (key70, -6), (key111, -6), (key133, 6)]

def row803 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row804 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row805 : Integer.Sparse Key := [(key20, 2), (key31, -2), (key45, -2), (key70, 2), (key111, 2), (key133, -2)]

def row806 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row807 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row808 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row809 : Integer.Sparse Key := [(key1001, 6), (key1015, -6), (key1036, -6), (key1071, 6), (key1123, 6), (key1150, -6)]

def row810 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row811 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row812 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row813 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row814 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row815 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1036, 2), (key1071, -2), (key1123, -2), (key1150, 2)]

def row816 : Integer.Sparse Key := [(key1001, -6), (key1015, 6), (key1036, 6), (key1071, -6), (key1123, -6), (key1150, 6)]

def row817 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row818 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row819 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1036, -2), (key1071, 2), (key1123, 2), (key1150, -2)]

def row820 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

def row821 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

def row822 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -2), (key193, -2), (key202, 2)]

def row823 : Integer.Sparse Key := [(key1, 6), (key7, -6), (key84, -6), (key151, 6), (key193, 6), (key202, -6)]

def row824 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

def row825 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

def row826 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 8), (key193, -4), (key202, -2)]

def row827 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

def row828 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

def row829 : Integer.Sparse Key := [(key1, -2), (key7, 2), (key84, 2), (key151, -8), (key193, 4), (key202, 2)]

def row830 : Integer.Sparse Key := [(key1, -6), (key7, 6), (key84, 6), (key151, -6), (key193, -6), (key202, 6)]

def row831 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

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

def row832 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

def row833 : Integer.Sparse Key := [(key1, 2), (key7, -2), (key84, -2), (key151, 2), (key193, 2), (key202, -2)]

def row834 : Integer.Sparse Key := [(key2785, -6), (key2793, 6), (key2808, 6), (key2828, -6), (key2859, -6), (key2869, 6)]

def row835 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row836 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row837 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row838 : Integer.Sparse Key := [(key2785, 6), (key2793, -6), (key2808, -6), (key2828, 6), (key2859, 6), (key2869, -6)]

def row839 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row840 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row841 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row842 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row843 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row844 : Integer.Sparse Key := [(key2785, -2), (key2793, 2), (key2808, 2), (key2828, -2), (key2859, -2), (key2869, 2)]

def row845 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row846 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row847 : Integer.Sparse Key := [(key2785, 2), (key2793, -2), (key2808, -2), (key2828, 2), (key2859, 2), (key2869, -2)]

def row848 : Integer.Sparse Key := [(key1287, -6), (key1307, 6), (key1382, 6), (key1415, -6), (key1537, -6), (key1564, 6)]

def row849 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row850 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row851 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row852 : Integer.Sparse Key := [(key1287, 6), (key1307, -6), (key1382, -6), (key1415, 6), (key1537, 6), (key1564, -6)]

def row853 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row854 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row855 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row856 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row857 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row858 : Integer.Sparse Key := [(key1287, -2), (key1307, 2), (key1382, 2), (key1415, -2), (key1537, -2), (key1564, 2)]

def row859 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row860 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row861 : Integer.Sparse Key := [(key1287, 2), (key1307, -2), (key1382, -2), (key1415, 2), (key1537, 2), (key1564, -2)]

def row862 : Integer.Sparse Key := [(key2610, -6), (key2626, 6), (key2665, 6), (key2700, -6), (key2780, -6), (key2803, 6)]

def row863 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

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

def row864 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row865 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row866 : Integer.Sparse Key := [(key2610, 6), (key2626, -6), (key2665, -6), (key2700, 6), (key2780, 6), (key2803, -6)]

def row867 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row868 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row869 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row870 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row871 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row872 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -2), (key2803, 2)]

def row873 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row874 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row875 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 2), (key2803, -2)]

def row876 : Integer.Sparse Key := [(key995, -6), (key1011, 6), (key1030, 6), (key1067, -6), (key1119, -6), (key1146, 6)]

def row877 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row878 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row879 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row880 : Integer.Sparse Key := [(key995, 6), (key1011, -6), (key1030, -6), (key1067, 6), (key1119, 6), (key1146, -6)]

def row881 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row882 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row883 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row884 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row885 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row886 : Integer.Sparse Key := [(key995, -2), (key1011, 2), (key1030, 2), (key1067, -2), (key1119, -2), (key1146, 2)]

def row887 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row888 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row889 : Integer.Sparse Key := [(key995, 2), (key1011, -2), (key1030, -2), (key1067, 2), (key1119, 2), (key1146, -2)]

def row890 : Integer.Sparse Key := [(key2606, -6), (key2622, 6), (key2661, 6), (key2696, -6), (key2776, -6), (key2799, 6)]

def row891 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row892 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row893 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row894 : Integer.Sparse Key := [(key2606, 6), (key2622, -6), (key2661, -6), (key2696, 12), (key2799, -6)]

def row895 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

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

def row896 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

def row897 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, -4), (key2799, 2)]

def row898 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

def row899 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

def row900 : Integer.Sparse Key := [(key2606, -2), (key2622, 2), (key2661, 2), (key2696, 2), (key2776, -6), (key2799, 2)]

def row901 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row902 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row903 : Integer.Sparse Key := [(key2606, 2), (key2622, -2), (key2661, -2), (key2696, 2), (key2776, 2), (key2799, -2)]

def row904 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row905 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row906 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row907 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row908 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row909 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1424, -1), (key1448, -1), (key1455, 1), (key1467, 1), (key1573, 1), (key1597, 1), (key1655, -1), (key1668, -1), (key1788, -2), (key1791, 1), (key1799, -1), (key1813, 2), (key1818, -1), (key1826, 1), (key1840, -1), (key1842, 1)]

def row910 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

def row911 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

def row912 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1424, -2), (key1458, 2), (key1573, 2), (key1660, -2), (key1788, 2), (key1791, -4), (key1813, -2), (key1818, 4), (key1840, 2), (key1842, -2)]

def row913 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row914 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row915 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row916 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row917 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row918 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1424, 1), (key1448, 1), (key1455, -1), (key1467, -1), (key1573, -1), (key1597, -1), (key1655, 1), (key1668, 1), (key1788, 2), (key1791, -1), (key1799, 1), (key1813, -2), (key1818, 1), (key1826, -1), (key1840, 1), (key1842, -1)]

def row919 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row920 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row921 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row922 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row923 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row924 : Integer.Sparse Key := [(key1296, -1), (key1303, 1), (key1316, 1), (key1330, -1), (key1340, -1), (key1346, 1), (key1391, -1), (key1398, 1), (key1455, -1), (key1458, 1), (key1546, 1), (key1560, -1), (key1655, 1), (key1660, -1), (key1775, -1), (key1781, 1), (key1788, -1), (key1791, 1), (key1813, 1), (key1818, -1), (key1840, -2), (key1842, 2)]

def row925 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

def row926 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

def row927 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1424, 2), (key1458, -2), (key1573, -2), (key1660, 2), (key1788, -2), (key1791, 4), (key1813, 2), (key1818, -4), (key1840, -2), (key1842, 2)]

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

def row928 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row929 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row930 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row931 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row932 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row933 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

def row934 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row935 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row936 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row937 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row938 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row939 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

def row940 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

def row941 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

def row942 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

def row943 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row944 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row945 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row946 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row947 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row948 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

def row949 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row950 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row951 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row952 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row953 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row954 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

def row955 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

def row956 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

def row957 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

def row958 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row959 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

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

def row960 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row961 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row962 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row963 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

def row964 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row965 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row966 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row967 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row968 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row969 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -1), (key1541, -1), (key1549, -2), (key1557, 1), (key1568, 1), (key1576, 2), (key1594, -1), (key1625, -1), (key1634, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row970 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

def row971 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

def row972 : Integer.Sparse Key := [(key1299, -2), (key1327, 2), (key1394, 2), (key1445, -2), (key1549, 2), (key1557, -4), (key1576, -2), (key1594, 4), (key1625, 2), (key1634, -2), (key1897, 2), (key1900, -2), (key1904, -2), (key1912, 2), (key1921, 2), (key1927, -2)]

def row973 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row974 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row975 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row976 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row977 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row978 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 1), (key1541, 1), (key1549, 2), (key1557, -1), (key1568, -1), (key1576, -2), (key1594, 1), (key1625, 1), (key1634, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row979 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row980 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row981 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row982 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row983 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row984 : Integer.Sparse Key := [(key1319, -1), (key1327, 1), (key1352, -1), (key1355, 1), (key1427, 1), (key1445, -1), (key1473, 1), (key1481, -1), (key1549, -1), (key1557, 1), (key1576, 1), (key1594, -1), (key1625, -2), (key1634, 2), (key1684, -1), (key1690, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row985 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row986 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row987 : Integer.Sparse Key := [(key1299, 2), (key1327, -2), (key1394, -2), (key1445, 2), (key1549, -2), (key1557, 4), (key1576, 2), (key1594, -4), (key1625, -2), (key1634, 2), (key1897, -2), (key1900, 2), (key1904, 2), (key1912, -2), (key1921, -2), (key1927, 2)]

def row988 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row989 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row990 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row991 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

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

def row992 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row993 : Integer.Sparse Key := [(key1319, 1), (key1327, -1), (key1352, 1), (key1355, -1), (key1427, -1), (key1445, 1), (key1473, -1), (key1481, 1), (key1549, 1), (key1557, -1), (key1576, -1), (key1594, 1), (key1625, 2), (key1634, -2), (key1684, 1), (key1690, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row994 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row995 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row996 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row997 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row998 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row999 : Integer.Sparse Key := [(key43, -2), (key48, 4), (key74, -2), (key212, -2), (key218, 2), (key426, 2), (key460, -2), (key486, -4), (key490, 2), (key659, 2)]

def row1000 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

def row1001 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

def row1002 : Integer.Sparse Key := [(key43, 6), (key48, -4), (key74, -2), (key206, -2), (key218, 2), (key426, -4), (key460, 4), (key486, 4), (key490, -6), (key663, 2)]

def row1003 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1004 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1005 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1006 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1007 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1008 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -2), (key105, -2), (key115, 6), (key137, -2), (key212, 2), (key218, -2), (key381, -6), (key432, 2), (key460, 2), (key486, -2), (key490, -2)]

def row1009 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1010 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1011 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1012 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key426, -2), (key432, 2), (key460, -6)]

def row1013 : Integer.Sparse Key := [(key18, -2), (key100, 4), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key212, 2), (key375, -2), (key381, 2), (key432, 2), (key460, -6)]

def row1014 : Integer.Sparse Key := [(key43, -2), (key100, 4), (key105, -2), (key115, -2), (key137, -2), (key195, 2), (key196, 2), (key200, 2), (key206, -2), (key212, 2), (key381, 2), (key432, 2), (key460, -6)]

def row1015 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

def row1016 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

def row1017 : Integer.Sparse Key := [(key35, -2), (key43, -6), (key48, 4), (key74, 2), (key115, -4), (key195, -4), (key196, 6), (key200, -2), (key206, 2), (key426, 4)]

def row1018 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2), (key426, 2)]

def row1019 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2), (key426, 2)]

def row1020 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2), (key426, 2)]

def row1021 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -6), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2), (key426, 2)]

def row1022 : Integer.Sparse Key := [(key18, 2), (key23, -2), (key48, -2), (key100, -4), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key375, 2)]

def row1023 : Integer.Sparse Key := [(key23, -2), (key43, 2), (key48, -2), (key100, -4), (key115, 2), (key137, 2), (key195, 4), (key196, -2), (key200, -2), (key206, 2)]

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

def row1024 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1025 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1026 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1027 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1028 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1029 : Integer.Sparse Key := [(key1293, -2), (key1313, 2), (key1388, 2), (key1421, -2), (key1543, -4), (key1553, 2), (key1570, 4), (key1590, -2), (key1621, -2), (key1630, 2)]

def row1030 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

def row1031 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

def row1032 : Integer.Sparse Key := [(key1293, -2), (key1323, 2), (key1388, 2), (key1441, -2), (key1543, 4), (key1553, -6), (key1570, -4), (key1590, 6), (key1621, 4), (key1630, -4)]

def row1033 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1034 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1035 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1036 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1037 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1038 : Integer.Sparse Key := [(key1293, 2), (key1313, -2), (key1388, -2), (key1421, 2), (key1543, 4), (key1553, -2), (key1570, -4), (key1590, 2), (key1621, 2), (key1630, -2)]

def row1039 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1040 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1041 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1042 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1043 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1044 : Integer.Sparse Key := [(key1313, -2), (key1323, 2), (key1421, 2), (key1441, -2), (key1543, -2), (key1553, 2), (key1570, 2), (key1590, -2), (key1621, -4), (key1630, 4)]

def row1045 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

def row1046 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

def row1047 : Integer.Sparse Key := [(key1293, 2), (key1323, -2), (key1388, -2), (key1441, 2), (key1543, -4), (key1553, 6), (key1570, 4), (key1590, -6), (key1621, -4), (key1630, 4)]

def row1048 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1049 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1050 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1051 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1052 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1053 : Integer.Sparse Key := [(key1313, 2), (key1323, -2), (key1421, -2), (key1441, 2), (key1543, 2), (key1553, -2), (key1570, -2), (key1590, 2), (key1621, 4), (key1630, -4)]

def row1054 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1055 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

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

def row1056 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1057 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1058 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1059 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -1), (key277, -1), (key278, 1), (key321, -1), (key331, -1), (key346, 1), (key347, 1), (key406, -1), (key411, 2), (key421, 1), (key435, 1), (key445, -1), (key487, -2), (key488, 1), (key489, -1), (key657, -1), (key658, -1), (key660, 1), (key662, 1)]

def row1060 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

def row1061 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

def row1062 : Integer.Sparse Key := [(key236, 2), (key241, -2), (key248, -2), (key263, 2), (key277, 2), (key278, -2), (key316, -2), (key346, 2), (key406, 4), (key411, -2), (key421, -2), (key435, -2), (key445, 2), (key487, 2), (key488, -4), (key661, 2)]

def row1063 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1064 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1065 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1066 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1067 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1068 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 3), (key277, -1), (key278, -1), (key321, 1), (key331, 1), (key346, -1), (key347, -1), (key406, 1), (key411, -2), (key421, -1), (key435, -1), (key445, 3), (key488, -1), (key489, -1), (key657, 1), (key658, 1), (key660, -1), (key661, 2), (key662, -1)]

def row1069 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1070 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1071 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key331, -1), (key346, 1), (key347, 1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1072 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key331, -1), (key346, 1), (key347, 1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1073 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1074 : Integer.Sparse Key := [(key236, -1), (key241, 1), (key248, 1), (key263, -3), (key277, 1), (key278, 1), (key302, -1), (key307, 1), (key316, 1), (key331, -1), (key346, 1), (key347, 1), (key385, -1), (key390, 1), (key400, -2), (key406, -1), (key411, 1), (key435, 2), (key445, -3), (key453, -1), (key488, 1), (key489, 1)]

def row1075 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

def row1076 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

def row1077 : Integer.Sparse Key := [(key236, -2), (key241, 2), (key248, 2), (key263, -2), (key277, -2), (key278, 2), (key316, 2), (key400, -2), (key406, -4), (key411, 2), (key421, 2), (key435, 2), (key445, -2), (key487, -2), (key488, 4), (key489, -2)]

def row1078 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1079 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1080 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key331, 1), (key346, 1), (key347, -1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1081 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key331, 1), (key346, 1), (key347, -1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1082 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1083 : Integer.Sparse Key := [(key236, 1), (key241, -1), (key248, -1), (key263, 1), (key277, 1), (key278, -1), (key302, 1), (key307, -1), (key316, -1), (key331, 1), (key346, 1), (key347, -1), (key385, 1), (key390, -1), (key406, 1), (key411, -1), (key435, -2), (key445, 1), (key453, 1), (key487, 2), (key488, -1), (key489, -1)]

def row1084 : Integer.Sparse Key := [(key2693, -2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2)]

def row1085 : Integer.Sparse Key := [(key2693, -2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2)]

def row1086 : Integer.Sparse Key := [(key2693, -4), (key3018, -2), (key3055, 2), (key3057, 2), (key3070, 2), (key3074, -2), (key3077, -2), (key3078, 2), (key3117, 2)]

def row1087 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

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

def row1088 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

def row1089 : Integer.Sparse Key := [(key2686, 2), (key2693, 2), (key2695, -4), (key2822, 2), (key2836, -2), (key3051, -2), (key3057, 2), (key3070, -2), (key3074, 2), (key3077, 2), (key3078, -2), (key3107, -2), (key3116, 2)]

def row1090 : Integer.Sparse Key := [(key2693, 2), (key2719, -2), (key2733, 2), (key3057, -2), (key3074, 2), (key3078, -2)]

def row1091 : Integer.Sparse Key := [(key2693, 2), (key2719, -2), (key2733, 2), (key3057, -2), (key3074, 2), (key3078, -2)]

def row1092 : Integer.Sparse Key := [(key2693, 4), (key2719, -2), (key2733, 2), (key3018, 2), (key3055, -2), (key3057, -2), (key3074, 2), (key3078, -2), (key3117, -2)]

def row1093 : Integer.Sparse Key := [(key2693, -6), (key2719, 6), (key2733, -6), (key2759, 6), (key3057, 6), (key3074, -6)]

def row1094 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

def row1095 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

def row1096 : Integer.Sparse Key := [(key2693, -2), (key2695, 2), (key2719, 2), (key2733, -2), (key2756, -2), (key2759, 2)]

def row1097 : Integer.Sparse Key := [(key2693, 6), (key2695, -6), (key2719, -6), (key2733, 6), (key2756, 6), (key2759, -6)]

def row1098 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1099 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1100 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1101 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1102 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1103 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1104 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1105 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1106 : Integer.Sparse Key := [(key1432, 2), (key1475, -2), (key1581, -2), (key1686, 2), (key1906, 2), (key1923, -2)]

def row1107 : Integer.Sparse Key := [(key1432, -6), (key1475, 6), (key1581, 6), (key1686, -6), (key1906, -6), (key1923, 6)]

def row1108 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1109 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1110 : Integer.Sparse Key := [(key1432, -2), (key1475, 2), (key1581, 2), (key1686, -2), (key1906, -2), (key1923, 2)]

def row1111 : Integer.Sparse Key := [(key1432, 6), (key1475, -6), (key1581, -6), (key1686, 6), (key1906, 6), (key1923, -6)]

def row1112 : Integer.Sparse Key := [(key2679, 1), (key2691, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3047, -1), (key3058, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3115, -2), (key3142, -2), (key3143, 2)]

def row1113 : Integer.Sparse Key := [(key2679, 1), (key2691, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3047, -1), (key3058, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3115, -2), (key3142, -2), (key3143, 2)]

def row1114 : Integer.Sparse Key := [(key2679, 1), (key2710, -2), (key2717, -4), (key2755, 2), (key2813, 2), (key2820, 4), (key3014, -2), (key3047, -1), (key3061, 2), (key3075, 2), (key3096, -2), (key3113, -2), (key3142, -2), (key3143, 2)]

def row1115 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

def row1116 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

def row1117 : Integer.Sparse Key := [(key2717, 2), (key2754, -2), (key2755, -4), (key2820, -2), (key3013, 2), (key3014, 4), (key3068, 2), (key3076, 2), (key3105, -2), (key3115, -2), (key3142, 2), (key3143, -2)]

def row1118 : Integer.Sparse Key := [(key2679, -1), (key2691, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3024, -2), (key3047, 1), (key3058, 1), (key3115, 2)]

def row1119 : Integer.Sparse Key := [(key2679, -1), (key2691, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3024, -2), (key3047, 1), (key3058, 1), (key3115, 2)]

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

def row1120 : Integer.Sparse Key := [(key2679, -1), (key2717, 2), (key2755, -2), (key2820, -2), (key2921, 2), (key3014, 2), (key3024, -2), (key3047, 1)]

def row1121 : Integer.Sparse Key := [(key2717, -6), (key2755, 6), (key2820, 6), (key2921, -6), (key3014, -6), (key3024, 6)]

def row1122 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row1123 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row1124 : Integer.Sparse Key := [(key2717, -2), (key2755, 2), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row1125 : Integer.Sparse Key := [(key2717, 6), (key2755, -6), (key2820, -6), (key2921, 6), (key3014, 6), (key3024, -6)]

def row1126 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1127 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1128 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1129 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1130 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1131 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1132 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1133 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1134 : Integer.Sparse Key := [(key1048, 2), (key1054, -2), (key1134, -2), (key1142, 2), (key1238, 2), (key1240, -2)]

def row1135 : Integer.Sparse Key := [(key1048, -6), (key1054, 6), (key1134, 6), (key1142, -6), (key1238, -6), (key1240, 6)]

def row1136 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1137 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1138 : Integer.Sparse Key := [(key1048, -2), (key1054, 2), (key1134, 2), (key1142, -2), (key1238, -2), (key1240, 2)]

def row1139 : Integer.Sparse Key := [(key1048, 6), (key1054, -6), (key1134, -6), (key1142, 6), (key1238, 6), (key1240, -6)]

def row1140 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1141 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1142 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1143 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1144 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1145 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1146 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1147 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1148 : Integer.Sparse Key := [(key3063, 2), (key3065, -2), (key3098, -2), (key3102, 2), (key3124, 2), (key3126, -2)]

def row1149 : Integer.Sparse Key := [(key3063, -6), (key3065, 6), (key3098, 6), (key3102, -6), (key3124, -6), (key3126, 6)]

def row1150 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1151 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

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

def row1152 : Integer.Sparse Key := [(key3063, -2), (key3065, 2), (key3098, 2), (key3102, -2), (key3124, -2), (key3126, 2)]

def row1153 : Integer.Sparse Key := [(key3063, 6), (key3065, -6), (key3098, -6), (key3102, 6), (key3124, 6), (key3126, -6)]

def row1154 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1155 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1156 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1157 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1158 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1159 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1160 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1161 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1162 : Integer.Sparse Key := [(key1405, 2), (key1410, -2), (key1433, -2), (key1439, 2), (key1477, 2), (key1479, -2)]

def row1163 : Integer.Sparse Key := [(key1405, -6), (key1410, 6), (key1433, 6), (key1439, -6), (key1477, -6), (key1479, 6)]

def row1164 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1165 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1166 : Integer.Sparse Key := [(key1405, -2), (key1410, 2), (key1433, 2), (key1439, -2), (key1477, -2), (key1479, 2)]

def row1167 : Integer.Sparse Key := [(key1405, 6), (key1410, -6), (key1433, -6), (key1439, 6), (key1477, 6), (key1479, -6)]

def row1168 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1169 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1170 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1171 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

def row1172 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

def row1173 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, -2), (key3092, 6), (key3093, -2)]

def row1174 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

def row1175 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

def row1176 : Integer.Sparse Key := [(key3081, 2), (key3083, -2), (key3086, -2), (key3089, 4), (key3093, -2)]

def row1177 : Integer.Sparse Key := [(key3081, -6), (key3083, 6), (key3086, 6), (key3089, -12), (key3093, 6)]

def row1178 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1179 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1180 : Integer.Sparse Key := [(key3081, -2), (key3083, 2), (key3086, 2), (key3089, -2), (key3092, -2), (key3093, 2)]

def row1181 : Integer.Sparse Key := [(key3081, 6), (key3083, -6), (key3086, -6), (key3089, 6), (key3092, 6), (key3093, -6)]

def row1182 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

def row1183 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

def row1184 : Integer.Sparse Key := [(key1424, -4), (key1448, -2), (key1455, 2), (key1458, 2), (key1467, 2), (key1573, 4), (key1597, 2), (key1655, -2), (key1660, -2), (key1668, -2), (key1788, -2), (key1791, -2), (key1799, -2), (key1813, 2), (key1818, 2), (key1826, 2)]

def row1185 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1186 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1187 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1188 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1189 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1190 : Integer.Sparse Key := [(key1391, -1), (key1398, 1), (key1424, 1), (key1448, 1), (key1455, -2), (key1458, 1), (key1467, -1), (key1546, 1), (key1560, -1), (key1573, -1), (key1597, -1), (key1655, 2), (key1660, -1), (key1668, 1), (key1775, -1), (key1781, 1), (key1788, 1), (key1799, 1), (key1813, -1), (key1826, -1), (key1840, -1), (key1842, 1)]

def row1191 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

def row1192 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

def row1193 : Integer.Sparse Key := [(key1424, 4), (key1448, 2), (key1455, -2), (key1458, -2), (key1467, -2), (key1573, -4), (key1597, -2), (key1655, 2), (key1660, 2), (key1668, 2), (key1788, 2), (key1791, 2), (key1799, 2), (key1813, -2), (key1818, -2), (key1826, -2)]

def row1194 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1195 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1196 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1197 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1198 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1199 : Integer.Sparse Key := [(key1391, 1), (key1398, -1), (key1424, -1), (key1448, -1), (key1455, 2), (key1458, -1), (key1467, 1), (key1546, -1), (key1560, 1), (key1573, 1), (key1597, 1), (key1655, -2), (key1660, 1), (key1668, -1), (key1775, 1), (key1781, -1), (key1788, -1), (key1799, -1), (key1813, 1), (key1826, 1), (key1840, 1), (key1842, -1)]

def row1200 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

def row1201 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

def row1202 : Integer.Sparse Key := [(key238, -6), (key250, 4), (key259, 2), (key304, 6), (key318, -4), (key327, -2), (key387, -4), (key396, -2), (key408, 4), (key417, 2)]

def row1203 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1204 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1205 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1206 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1207 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1208 : Integer.Sparse Key := [(key238, 2), (key250, -4), (key259, 2), (key304, -2), (key318, 4), (key327, -2), (key387, 2), (key408, -2), (key441, -2), (key449, 2)]

def row1209 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

def row1210 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

def row1211 : Integer.Sparse Key := [(key238, 6), (key250, -4), (key259, -2), (key304, -6), (key318, 4), (key327, 2), (key387, 4), (key396, 2), (key408, -4), (key417, -2)]

def row1212 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1213 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1214 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1215 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1216 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1217 : Integer.Sparse Key := [(key238, -2), (key250, 4), (key259, -2), (key304, 2), (key318, -4), (key327, 2), (key387, -2), (key408, 2), (key441, 2), (key449, -2)]

def row1218 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

def row1219 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

def row1220 : Integer.Sparse Key := [(key1291, -2), (key1299, -4), (key1311, 2), (key1319, 2), (key1327, 2), (key1386, 2), (key1394, 4), (key1419, -2), (key1427, -2), (key1445, -2), (key1541, -2), (key1549, -2), (key1557, -2), (key1568, 2), (key1576, 2), (key1594, 2)]

def row1221 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1222 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1223 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1224 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1225 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1226 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -2), (key1327, 1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, -1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -1), (key1625, -1), (key1634, 1), (key1684, -1), (key1690, 1)]

def row1227 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

def row1228 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

def row1229 : Integer.Sparse Key := [(key1291, 2), (key1299, 4), (key1311, -2), (key1319, -2), (key1327, -2), (key1386, -2), (key1394, -4), (key1419, 2), (key1427, 2), (key1445, 2), (key1541, 2), (key1549, 2), (key1557, 2), (key1568, -2), (key1576, -2), (key1594, -2)]

def row1230 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1231 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1232 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1233 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1234 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1235 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 2), (key1327, -1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, 1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 1), (key1625, 1), (key1634, -1), (key1684, 1), (key1690, -1)]

def row1236 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

def row1237 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

def row1238 : Integer.Sparse Key := [(key18, -2), (key23, -4), (key35, 6), (key375, 2), (key381, 4), (key486, -4), (key490, -2), (key654, -6), (key659, 4), (key663, 2)]

def row1239 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1240 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1241 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1242 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1243 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1244 : Integer.Sparse Key := [(key18, -2), (key23, 4), (key35, -2), (key381, -2), (key426, 2), (key460, -2), (key486, 2), (key654, 2), (key659, -4), (key663, 2)]

def row1245 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

def row1246 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

def row1247 : Integer.Sparse Key := [(key43, -2), (key48, -4), (key74, 6), (key206, 2), (key212, 4), (key218, -6), (key486, 4), (key490, 2), (key659, -4), (key663, -2)]

def row1248 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1249 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1250 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1251 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1252 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1253 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -2), (key105, -2), (key115, -2), (key137, 6), (key212, -6), (key381, 2), (key432, 2), (key460, 2), (key654, -2), (key659, -2), (key663, -2)]

def row1254 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

def row1255 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

def row1256 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1388, 6), (key1421, -4), (key1441, -2), (key1543, -4), (key1553, -2), (key1570, 4), (key1590, 2)]

def row1257 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1258 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1259 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1260 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1261 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1262 : Integer.Sparse Key := [(key1293, 2), (key1313, -4), (key1323, 2), (key1388, -2), (key1421, 4), (key1441, -2), (key1543, 2), (key1570, -2), (key1621, -2), (key1630, 2)]

def row1263 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

def row1264 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

def row1265 : Integer.Sparse Key := [(key1293, 6), (key1313, -4), (key1323, -2), (key1388, -6), (key1421, 4), (key1441, 2), (key1543, 4), (key1553, 2), (key1570, -4), (key1590, -2)]

def row1266 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1267 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1268 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1269 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1270 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1271 : Integer.Sparse Key := [(key1293, -2), (key1313, 4), (key1323, -2), (key1388, 2), (key1421, -4), (key1441, 2), (key1543, -2), (key1570, 2), (key1621, 2), (key1630, -2)]

def row1272 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row1273 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row1274 : Integer.Sparse Key := [(key316, -2), (key321, -2), (key331, -2), (key346, 4), (key347, 2), (key406, 2), (key411, 2), (key421, 2), (key487, -2), (key488, -2), (key489, -2), (key657, -4), (key658, -2), (key660, 2), (key661, 2), (key662, 2)]

def row1275 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1276 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1277 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1278 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1279 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

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

def row1280 : Integer.Sparse Key := [(key302, -1), (key307, 1), (key316, -1), (key321, 2), (key331, 1), (key346, -1), (key347, -1), (key385, 1), (key400, -1), (key411, -1), (key421, -1), (key435, 1), (key445, -1), (key487, 1), (key489, 1), (key655, -1), (key656, 1), (key657, 1), (key658, 1), (key660, -2), (key661, 1), (key662, -1)]

def row1281 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

def row1282 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

def row1283 : Integer.Sparse Key := [(key316, 2), (key321, 2), (key331, 2), (key346, -4), (key347, -2), (key406, -2), (key411, -2), (key421, -2), (key487, 2), (key488, 2), (key489, 2), (key657, 4), (key658, 2), (key660, -2), (key661, -2), (key662, -2)]

def row1284 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1285 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1286 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1287 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1288 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1289 : Integer.Sparse Key := [(key302, 1), (key307, -1), (key321, -3), (key331, 1), (key346, 1), (key347, 1), (key390, 1), (key400, 1), (key411, 1), (key421, 1), (key435, -1), (key453, 3), (key655, -1), (key656, -1), (key657, -1), (key658, -1), (key660, -1), (key661, -2), (key662, 1)]

def row1290 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

def row1291 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

def row1292 : Integer.Sparse Key := [(key1433, -2), (key1439, -4), (key1477, 2), (key1479, 4), (key1582, 2), (key1588, 4), (key1688, -6), (key1908, -2), (key1910, -4), (key1925, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1476 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

def row1477 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

def row1478 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

def row1485 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

def row1486 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

def row1487 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

def row1494 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

def row1495 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

def row1496 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

def row1503 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

def row1504 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

def row1505 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

def row1524 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 2), (key2641, -2), (key2660, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

def row1525 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

def row1526 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -4), (key2640, 1), (key2641, -2), (key2646, 1), (key2653, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2753, 2), (key2758, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2920, -2), (key2923, 2)]

def row1533 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -2), (key2641, 2), (key2660, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

def row1534 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -1), (key2641, 2), (key2646, -1), (key2653, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

def row1535 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, 4), (key2640, -1), (key2641, 2), (key2646, -1), (key2653, -2), (key2671, 2), (key2702, -2), (key2726, 2), (key2758, 2), (key2782, -4), (key2795, -2), (key2805, 2), (key2893, 2), (key2897, 2), (key2972, -2), (key2976, -2)]

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

def row1554 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

def row1555 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

def row1556 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

def row1563 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

def row1564 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

def row1565 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

def row1584 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

def row1585 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

def row1586 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

def row1593 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

def row1594 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

def row1595 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

def row1614 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

def row1615 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

def row1616 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

def row1623 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

def row1624 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

def row1625 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

def row1644 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

def row1645 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

def row1646 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

def row1653 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

def row1654 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

def row1655 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

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

def row1674 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

def row1675 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

def row1676 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

def row1683 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

def row1684 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

def row1685 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

def row1704 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

def row1705 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

def row1706 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

def row1713 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

def row1714 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

def row1715 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

def row1734 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

def row1735 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

def row1736 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

def row1743 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

def row1744 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

def row1745 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2867 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2868 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2869 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2870 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2871 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2872 : Integer.Sparse Key := [(key976, 4), (key983, -4), (key1090, -4), (key1168, 4), (key1182, 4), (key1219, -4)]

def row2873 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2874 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2875 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2876 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2877 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2878 : Integer.Sparse Key := [(key976, -2), (key983, 2), (key1090, 2), (key1168, -2), (key1182, -2), (key1219, 2)]

def row2879 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2880 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2881 : Integer.Sparse Key := [(key976, -4), (key983, 4), (key1090, 4), (key1168, -4), (key1182, -4), (key1219, 4)]

def row2882 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2883 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2884 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2885 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2886 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2887 : Integer.Sparse Key := [(key976, 2), (key983, -2), (key1090, -2), (key1168, 2), (key1182, 2), (key1219, -2)]

def row2888 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

def row2889 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

def row2890 : Integer.Sparse Key := [(key2379, -2), (key2382, 2), (key2393, -2), (key2395, 2), (key2473, 2), (key2483, 2), (key2507, -2), (key2526, -2), (key2539, -2), (key2545, -2), (key2555, 2), (key2565, 2)]

def row2891 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

def row2892 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

def row2893 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2539, 2), (key2545, 2), (key2555, -2), (key2565, -2)]

def row2894 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

def row2895 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

def row2896 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, 2), (key2395, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2544, -2), (key2555, -2), (key2565, -2), (key2848, -2), (key2882, 2), (key2891, -4), (key2912, 2), (key2914, 2)]

def row2897 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2544, -1), (key2545, 1), (key2555, -1), (key2565, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 2), (key2991, 2), (key3003, 2)]

def row2898 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, -1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2544, -1), (key2545, 1), (key2555, -1), (key2565, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 2), (key2991, 2), (key3003, 2)]

def row2899 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2395, 1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 2), (key2991, 1), (key3003, 2)]

def row2900 : Integer.Sparse Key := [(key2382, 1), (key2393, -1), (key2395, 1), (key2410, 1), (key2441, -2), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 2), (key2991, 1), (key3003, 2)]

def row2901 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2395, 1), (key2407, -1), (key2410, 1), (key2441, -1), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2602, -1), (key2771, 1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 1), (key2991, 1), (key3003, 2)]

def row2902 : Integer.Sparse Key := [(key2382, 1), (key2395, 1), (key2410, 1), (key2441, -1), (key2507, -1), (key2526, -1), (key2545, 1), (key2565, -1), (key2592, -1), (key2602, -1), (key2774, -1), (key2848, 1), (key2882, -1), (key2891, 1), (key2914, -2), (key2933, 1), (key2991, 1), (key3003, 2)]

def row2903 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row2904 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row2905 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, -2), (key2473, 2), (key2483, 2), (key2507, 2), (key2595, 4), (key2603, 2), (key2882, -2), (key2914, -2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row2906 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2595, -1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2912, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -2), (key2996, 1), (key3003, -1)]

def row2907 : Integer.Sparse Key := [(key2379, 1), (key2393, 1), (key2407, 1), (key2441, 1), (key2544, 1), (key2555, 1), (key2595, -1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2912, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -2), (key2996, 1), (key3003, -1)]

def row2908 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2592, 1), (key2595, -1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

def row2909 : Integer.Sparse Key := [(key2393, 1), (key2441, 1), (key2592, 1), (key2595, -1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2933, -1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

def row2910 : Integer.Sparse Key := [(key2379, 1), (key2407, 1), (key2595, -1), (key2602, 1), (key2603, -1), (key2771, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

def row2911 : Integer.Sparse Key := [(key2592, 1), (key2595, -1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, -1), (key2914, 1), (key2970, 1), (key2991, -1), (key2996, 1), (key3003, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3032 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

def row3033 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

def row3034 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2737, 2), (key2809, 2), (key2829, 2), (key2835, -4), (key2897, -2), (key2972, -2), (key2976, 4), (key2997, 2), (key2998, -2)]

def row3035 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3036 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3037 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3038 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3039 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3040 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2671, -1), (key2673, 1), (key2706, 1), (key2732, -2), (key2737, 1), (key2758, 2), (key2794, -1), (key2795, -1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2927, 2), (key2938, 1), (key2943, -1), (key2950, 1), (key2976, -1)]

def row3041 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

def row3042 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

def row3043 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2786, 2), (key2798, -2), (key2809, -2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2920, 2), (key2923, -4), (key2927, 2)]

def row3044 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3045 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3046 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3047 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3048 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3049 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, 1), (key2835, -1), (key2860, -1), (key2870, -1), (key2885, 2), (key2920, 1), (key2923, 1), (key2927, -2)]

def row3050 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

def row3051 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

def row3052 : Integer.Sparse Key := [(key1289, -2), (key1350, 2), (key1384, 2), (key1417, 4), (key1471, -6), (key1566, -4), (key1680, 4), (key1895, -2), (key1902, 6), (key1917, -4)]

def row3053 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3054 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3055 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3056 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3057 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3058 : Integer.Sparse Key := [(key1309, -2), (key1350, 2), (key1417, -2), (key1471, 2), (key1539, 2), (key1566, 2), (key1680, -4), (key1895, -2), (key1902, -2), (key1917, 4)]

def row3059 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

def row3060 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

def row3061 : Integer.Sparse Key := [(key1289, 2), (key1350, -2), (key1384, -2), (key1417, -4), (key1471, 6), (key1566, 4), (key1680, -4), (key1895, 2), (key1902, -6), (key1917, 4)]

def row3062 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3063 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3064 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3065 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3066 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3067 : Integer.Sparse Key := [(key1309, 2), (key1350, -2), (key1417, 2), (key1471, -2), (key1539, -2), (key1566, -2), (key1680, 4), (key1895, 2), (key1902, 2), (key1917, -4)]

def row3068 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

def row3069 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

def row3070 : Integer.Sparse Key := [(key2614, -2), (key2638, 2), (key2669, 2), (key2704, 2), (key2752, -4), (key2757, -2), (key2807, -2), (key2827, -2), (key2858, 2), (key2868, -2), (key3011, 4), (key3016, 2), (key3022, 2), (key3025, -2)]

def row3071 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3072 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3073 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3074 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3075 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3076 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2657, 1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, 1), (key2807, 1), (key2827, 1), (key2918, -2), (key2919, -1), (key2922, -1), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, 1), (key3025, 1)]

def row3077 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

def row3078 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

def row3079 : Integer.Sparse Key := [(key2614, 2), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2807, 2), (key2827, 2), (key2918, -2), (key2922, -2), (key3007, 2), (key3011, -4), (key3016, -2), (key3021, 2), (key3025, 2)]

def row3080 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3081 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3082 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3083 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3084 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3085 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2918, 2), (key2919, 1), (key2922, 1), (key3007, 1), (key3009, 1), (key3011, 1), (key3016, 1), (key3021, -2), (key3022, -1), (key3025, -1)]

def row3086 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3087 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3088 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3089 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3090 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3091 : Integer.Sparse Key := [(key1001, -2), (key1015, 2), (key1028, -2), (key1036, 4), (key1071, -2), (key1106, 2), (key1123, -4), (key1150, 2), (key1232, -2), (key1235, 2)]

def row3092 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

def row3093 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

def row3094 : Integer.Sparse Key := [(key993, -2), (key1015, 2), (key1028, 6), (key1036, -4), (key1071, -2), (key1106, -4), (key1123, 4), (key1232, 4), (key1235, -6), (key1242, 2)]

def row3095 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3096 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3097 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3098 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3099 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3100 : Integer.Sparse Key := [(key1001, 2), (key1015, -2), (key1028, 2), (key1036, -4), (key1071, 2), (key1106, -2), (key1123, 4), (key1150, -2), (key1232, 2), (key1235, -2)]

def row3101 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3102 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3103 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3104 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3105 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3106 : Integer.Sparse Key := [(key993, -2), (key1001, 2), (key1028, -2), (key1036, 2), (key1106, 4), (key1123, -2), (key1150, -2), (key1232, -4), (key1235, 2), (key1242, 2)]

def row3107 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row3108 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row3109 : Integer.Sparse Key := [(key993, 2), (key1015, -2), (key1028, -6), (key1036, 4), (key1071, 2), (key1106, 4), (key1123, -4), (key1232, -4), (key1235, 6), (key1242, -2)]

def row3110 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3111 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3112 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3113 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3114 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3115 : Integer.Sparse Key := [(key993, 2), (key1001, -2), (key1028, 2), (key1036, -2), (key1106, -4), (key1123, 2), (key1150, 2), (key1232, 4), (key1235, -2), (key1242, -2)]

def row3116 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3117 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3118 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3119 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3120 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3121 : Integer.Sparse Key := [(key2610, -2), (key2626, 2), (key2665, 2), (key2700, -2), (key2780, -4), (key2789, 2), (key2803, 4), (key2824, -2), (key2855, -2), (key2865, 2)]

def row3122 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

def row3123 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

def row3124 : Integer.Sparse Key := [(key2610, -2), (key2635, 2), (key2665, 2), (key2721, -2), (key2780, 4), (key2789, -6), (key2803, -4), (key2824, 6), (key2855, 4), (key2865, -4)]

def row3125 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3126 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3127 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3128 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3129 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3130 : Integer.Sparse Key := [(key2610, 2), (key2626, -2), (key2665, -2), (key2700, 2), (key2780, 4), (key2789, -2), (key2803, -4), (key2824, 2), (key2855, 2), (key2865, -2)]

def row3131 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3132 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3133 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3134 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3135 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3136 : Integer.Sparse Key := [(key2626, -2), (key2635, 2), (key2700, 2), (key2721, -2), (key2780, -2), (key2789, 2), (key2803, 2), (key2824, -2), (key2855, -4), (key2865, 4)]

def row3137 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

def row3138 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

def row3139 : Integer.Sparse Key := [(key2610, 2), (key2635, -2), (key2665, -2), (key2721, 2), (key2780, -4), (key2789, 6), (key2803, 4), (key2824, -6), (key2855, -4), (key2865, 4)]

def row3140 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3141 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3142 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3143 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3144 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3145 : Integer.Sparse Key := [(key2626, 2), (key2635, -2), (key2700, -2), (key2721, 2), (key2780, 2), (key2789, -2), (key2803, -2), (key2824, 2), (key2855, 4), (key2865, -4)]

def row3146 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3147 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3148 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3149 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3150 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3151 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1549, -1), (key1557, 1), (key1568, -1), (key1576, 2), (key1594, -1), (key1617, 1), (key1625, -2), (key1634, 1), (key1682, -1), (key1684, 1), (key1897, -1), (key1900, 1), (key1904, 1), (key1912, -1), (key1921, -1), (key1927, 1)]

def row3152 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

def row3153 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

def row3154 : Integer.Sparse Key := [(key1291, 2), (key1299, -2), (key1311, -2), (key1327, 2), (key1352, 2), (key1355, -2), (key1541, -2), (key1557, 2), (key1568, 4), (key1576, -2), (key1594, -2), (key1617, -2), (key1625, 2), (key1682, 2), (key1684, -4), (key1690, 2)]

def row3155 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3156 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3157 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3158 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3159 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3160 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1549, 1), (key1557, -1), (key1568, 1), (key1576, -2), (key1594, 1), (key1617, -1), (key1625, 2), (key1634, -1), (key1682, 1), (key1684, -1), (key1897, 1), (key1900, -1), (key1904, -1), (key1912, 1), (key1921, 1), (key1927, -1)]

def row3161 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3162 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3163 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3164 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3165 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3166 : Integer.Sparse Key := [(key1291, -1), (key1299, 1), (key1311, 1), (key1327, -1), (key1352, -1), (key1355, 1), (key1386, -1), (key1394, 1), (key1419, 1), (key1445, -1), (key1473, -1), (key1481, 1), (key1541, -1), (key1549, 1), (key1568, -1), (key1576, 1), (key1617, 2), (key1625, -1), (key1634, -1), (key1682, -2), (key1684, 1), (key1690, 1)]

def row3167 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

def row3168 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

def row3169 : Integer.Sparse Key := [(key1291, -2), (key1299, 2), (key1311, 2), (key1327, -2), (key1352, -2), (key1355, 2), (key1541, 2), (key1557, -2), (key1568, -4), (key1576, 2), (key1594, 2), (key1617, 2), (key1625, -2), (key1682, -2), (key1684, 4), (key1690, -2)]

def row3170 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3171 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3172 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3173 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3174 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3175 : Integer.Sparse Key := [(key1291, 1), (key1299, -1), (key1311, -1), (key1327, 1), (key1352, 1), (key1355, -1), (key1386, 1), (key1394, -1), (key1419, -1), (key1445, 1), (key1473, 1), (key1481, -1), (key1541, 1), (key1549, -1), (key1568, 1), (key1576, -1), (key1617, -2), (key1625, 1), (key1634, 1), (key1682, 2), (key1684, -1), (key1690, -1)]

def row3176 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row3177 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row3178 : Integer.Sparse Key := [(key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3115, -2)]

def row3179 : Integer.Sparse Key := [(key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3115, -2)]

def row3180 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2691, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3058, -2), (key3115, -2)]

def row3181 : Integer.Sparse Key := [(key2684, 2), (key2691, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3058, -2), (key3115, -2)]

def row3182 : Integer.Sparse Key := [(key2679, 4), (key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2813, 2), (key2921, -2), (key3024, 2), (key3053, -4), (key3105, -2)]

def row3183 : Integer.Sparse Key := [(key2679, 2), (key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2921, -2), (key3024, 2), (key3047, 2), (key3053, -4), (key3096, 2), (key3105, -2)]

def row3184 : Integer.Sparse Key := [(key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2921, -2), (key3024, 2), (key3047, 4), (key3053, -4), (key3096, 2), (key3105, -2)]

def row3185 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3014, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3142, 2), (key3143, -2)]

def row3186 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3014, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3142, 2), (key3143, -2)]

def row3187 : Integer.Sparse Key := [(key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3188 : Integer.Sparse Key := [(key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3189 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2691, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3058, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3190 : Integer.Sparse Key := [(key2684, -2), (key2691, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3058, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3191 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3192 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3193 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3194 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3195 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3196 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3197 : Integer.Sparse Key := [(key2679, -4), (key2710, 6), (key2813, -2), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3105, 2), (key3142, 2), (key3143, -2)]

def row3198 : Integer.Sparse Key := [(key2679, -2), (key2710, 6), (key3047, -2), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3096, -2), (key3105, 2), (key3142, 2), (key3143, -2)]

def row3199 : Integer.Sparse Key := [(key2710, 6), (key3047, -4), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3096, -2), (key3105, 2), (key3142, 2), (key3143, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3200 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3201 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3202 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3203 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3204 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3205 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3206 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3207 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3208 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3209 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3210 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3211 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3212 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

def row3213 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

def row3214 : Integer.Sparse Key := [(key1299, -2), (key1352, 2), (key1394, 2), (key1427, 2), (key1445, 2), (key1473, -4), (key1481, -2), (key1576, -2), (key1594, -2), (key1682, 2), (key1690, 2), (key1897, -2), (key1904, 4), (key1912, 2), (key1919, -2), (key1927, -2)]

def row3215 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3216 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3217 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3218 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3219 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3220 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3221 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3222 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3223 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3224 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3225 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3226 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3227 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

def row3228 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

def row3229 : Integer.Sparse Key := [(key1299, 2), (key1352, -2), (key1394, -2), (key1427, -2), (key1445, -2), (key1473, 4), (key1481, 2), (key1576, 2), (key1594, 2), (key1682, -2), (key1690, -2), (key1897, 2), (key1904, -4), (key1912, -2), (key1919, 2), (key1927, 2)]

def row3230 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3231 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3232 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3233 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3234 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3235 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3236 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3237 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3238 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3239 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3240 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3241 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3242 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

def row3243 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

def row3244 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

def row3245 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3246 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3247 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3248 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3249 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3250 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3251 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3252 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3253 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3254 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3255 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3256 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3257 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row3258 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row3259 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row3260 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3261 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3262 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3263 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3264 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3265 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3266 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3267 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3268 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3269 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3270 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3271 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2646, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2737, -1), (key2747, 1), (key2753, 1), (key2758, -1), (key2893, -1), (key2897, -1), (key2972, 2), (key2976, 1), (key2983, -1), (key2997, -1), (key3000, 1)]

def row3272 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

def row3273 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

def row3274 : Integer.Sparse Key := [(key2628, -2), (key2648, 2), (key2671, 2), (key2676, -2), (key2702, -2), (key2706, 2), (key2726, 2), (key2728, 2), (key2732, -4), (key2737, 2), (key2747, -2), (key2904, -2), (key2972, -2), (key2983, 4), (key2997, 2), (key3000, -2)]

def row3275 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3276 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3277 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3278 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3279 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3280 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, 1), (key2726, 2), (key2728, 1), (key2735, -1), (key2747, -1), (key2758, 2), (key2782, -1), (key2786, -2), (key2794, 1), (key2795, -1), (key2798, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2920, 1), (key2923, -2), (key2927, 1), (key2938, -1), (key2943, -1), (key2976, 1), (key2983, 1), (key2998, -1), (key3000, -1)]

def row3281 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3282 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3283 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3284 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3285 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3286 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2640, -1), (key2648, 1), (key2671, -1), (key2673, 1), (key2726, -1), (key2728, -1), (key2737, 1), (key2747, -1), (key2786, 1), (key2798, -2), (key2809, 1), (key2831, -1), (key2835, -2), (key2860, 1), (key2870, 1), (key2885, -2), (key2904, -1), (key2938, 1), (key2950, 1), (key2960, -1), (key2983, -1), (key3010, 2), (key3017, 2), (key3030, 2)]

def row3287 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

def row3288 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

def row3289 : Integer.Sparse Key := [(key2632, 2), (key2644, -2), (key2671, -2), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, 4), (key2786, 2), (key2798, -2), (key2870, 2), (key2885, -2), (key3008, -2), (key3010, 2), (key3023, 2), (key3026, -4), (key3030, 2)]

def row3290 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3291 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3292 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3293 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3294 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3295 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2640, 1), (key2644, -1), (key2671, 1), (key2676, -1), (key2726, 1), (key2732, -1), (key2786, -1), (key2798, 1), (key2809, -1), (key2835, 1), (key2860, -1), (key2870, -1), (key2885, 2), (key3008, 1), (key3010, -1), (key3012, 1), (key3017, -1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row3296 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3297 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3298 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3299 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3300 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3301 : Integer.Sparse Key := [(key2398, -2), (key2404, 4), (key2435, -2), (key2589, -2), (key2604, 2), (key2839, 2), (key2876, -2), (key2916, -4), (key2925, 2), (key3019, 2)]

def row3302 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

def row3303 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

def row3304 : Integer.Sparse Key := [(key2398, 6), (key2404, -4), (key2435, -2), (key2583, -2), (key2604, 2), (key2839, -4), (key2876, 4), (key2916, 4), (key2925, -6), (key3028, 2)]

def row3305 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3306 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3307 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3308 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3309 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3310 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3311 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3312 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3313 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3314 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3315 : Integer.Sparse Key := [(key2370, -2), (key2464, 4), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2845, 2), (key2876, -6)]

def row3316 : Integer.Sparse Key := [(key2398, -2), (key2464, 4), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2845, 2), (key2876, -6)]

def row3317 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

def row3318 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

def row3319 : Integer.Sparse Key := [(key2388, -2), (key2398, -6), (key2404, 4), (key2435, 2), (key2478, -4), (key2568, -4), (key2570, 6), (key2575, -2), (key2583, 2), (key2839, 4)]

def row3320 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2), (key2839, 2)]

def row3321 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2), (key2839, 2)]

def row3322 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2), (key2839, 2)]

def row3323 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -6), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2), (key2839, 2)]

def row3324 : Integer.Sparse Key := [(key2370, 2), (key2376, -2), (key2404, -2), (key2464, -4), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2762, 2)]

def row3325 : Integer.Sparse Key := [(key2376, -2), (key2398, 2), (key2404, -2), (key2464, -4), (key2478, 2), (key2501, 2), (key2568, 4), (key2570, -2), (key2575, -2), (key2583, 2)]

def row3326 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3327 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3328 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3329 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3330 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3331 : Integer.Sparse Key := [(key2588, -2), (key2599, 2), (key2763, -2), (key2767, 4), (key2840, 2), (key2875, -2), (key2888, -4), (key2909, 2), (key2930, -2), (key2967, 2)]

def row3332 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

def row3333 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

def row3334 : Integer.Sparse Key := [(key2584, -2), (key2599, 2), (key2763, 6), (key2767, -4), (key2840, -4), (key2875, 4), (key2888, 4), (key2909, -6), (key2930, -2), (key2988, 2)]

def row3335 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3336 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3337 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3338 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3339 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3340 : Integer.Sparse Key := [(key2588, 2), (key2599, -2), (key2763, 2), (key2767, -4), (key2840, -2), (key2875, 2), (key2888, 4), (key2909, -2), (key2930, 2), (key2967, -2)]

def row3341 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3342 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3343 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3344 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3345 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3346 : Integer.Sparse Key := [(key2584, -2), (key2588, 2), (key2763, -2), (key2767, 2), (key2840, 4), (key2875, -4), (key2888, -2), (key2909, 2), (key2967, -2), (key2988, 2)]

def row3347 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

def row3348 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

def row3349 : Integer.Sparse Key := [(key2584, 2), (key2599, -2), (key2763, -6), (key2767, 4), (key2840, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, 2), (key2988, -2)]

def row3350 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3351 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3352 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3353 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3354 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3355 : Integer.Sparse Key := [(key2584, 2), (key2588, -2), (key2763, 2), (key2767, -2), (key2840, -4), (key2875, 4), (key2888, 2), (key2909, -2), (key2967, 2), (key2988, -2)]

def row3356 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3357 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3358 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3359 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3360 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3361 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3362 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3363 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3364 : Integer.Sparse Key := [(key2613, -2), (key2637, 2), (key2668, 2), (key2723, -2), (key2783, 2), (key2791, -4), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3365 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3366 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3367 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3368 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3369 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3370 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, -1), (key2802, -1), (key2806, -2), (key2826, 1), (key2857, 1), (key2867, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3371 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3372 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3373 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3374 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3375 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3376 : Integer.Sparse Key := [(key2629, -1), (key2637, 1), (key2647, -1), (key2652, 1), (key2703, 1), (key2723, -1), (key2736, 1), (key2746, -1), (key2783, -1), (key2791, 1), (key2806, 1), (key2826, -1), (key2857, -2), (key2867, 2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row3377 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3378 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3379 : Integer.Sparse Key := [(key2613, 2), (key2637, -2), (key2668, -2), (key2723, 2), (key2783, -2), (key2791, 4), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3380 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3381 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3382 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3383 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3384 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3385 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, 1), (key2652, -1), (key2703, -1), (key2723, 1), (key2736, -1), (key2746, 1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, 1), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row3386 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3387 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3388 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3389 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3390 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3391 : Integer.Sparse Key := [(key2079, -2), (key2085, 2), (key2174, -2), (key2176, 4), (key2187, -2), (key2274, 2), (key2279, -4), (key2287, 2), (key2341, -2), (key2343, 2)]

def row3392 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3393 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3394 : Integer.Sparse Key := [(key2077, -2), (key2085, 2), (key2174, 6), (key2176, -4), (key2187, -2), (key2274, -4), (key2279, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3395 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3396 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3397 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3398 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3399 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3400 : Integer.Sparse Key := [(key2079, 2), (key2085, -2), (key2174, 2), (key2176, -4), (key2187, 2), (key2274, -2), (key2279, 4), (key2287, -2), (key2341, 2), (key2343, -2)]

def row3401 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3402 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3403 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3404 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3405 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3406 : Integer.Sparse Key := [(key2077, -2), (key2079, 2), (key2174, -2), (key2176, 2), (key2274, 4), (key2279, -2), (key2287, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row3407 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3408 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3409 : Integer.Sparse Key := [(key2077, 2), (key2085, -2), (key2174, -6), (key2176, 4), (key2187, 2), (key2274, 4), (key2279, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3410 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3411 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3412 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3413 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3414 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3415 : Integer.Sparse Key := [(key2077, 2), (key2079, -2), (key2174, 2), (key2176, -2), (key2274, -4), (key2279, 2), (key2287, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row3416 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3417 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3418 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3419 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3420 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3421 : Integer.Sparse Key := [(key2411, 2), (key2437, -2), (key2587, -1), (key2593, -1), (key2598, 1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, -1), (key2889, -2), (key2910, 1), (key2966, 2), (key2968, 1), (key2989, -1), (key2995, -1), (key3002, 1)]

def row3422 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

def row3423 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

def row3424 : Integer.Sparse Key := [(key2406, 4), (key2411, -2), (key2437, 2), (key2443, -4), (key2587, -2), (key2600, 2), (key2843, -2), (key2880, 2), (key2889, 2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, 2), (key3002, -2)]

def row3425 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3426 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3427 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3428 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3429 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3430 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, -2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, 2), (key2587, 1), (key2593, 1), (key2598, -1), (key2600, -1), (key2766, -2), (key2772, -2), (key2843, 1), (key2880, 1), (key2887, -1), (key2910, -1), (key2931, -2), (key2968, 1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row3431 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3432 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3433 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3434 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3435 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3436 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, 1), (key2484, -2), (key2503, 1), (key2509, -2), (key2524, -2), (key2571, 2), (key2576, 2), (key2580, 2), (key2593, 1), (key2600, 1), (key2772, 1), (key2880, -2), (key2889, 1), (key2910, -2), (key2931, 1), (key2968, 1), (key2989, -2)]

def row3437 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

def row3438 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

def row3439 : Integer.Sparse Key := [(key2378, 2), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, 2), (key2484, -2), (key2503, 2), (key2524, -2), (key2569, -2), (key2571, 4), (key2576, -4), (key2580, 2)]

def row3440 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3441 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3442 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3443 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3444 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3445 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, 1), (key2394, -1), (key2406, 1), (key2411, -1), (key2437, 1), (key2443, -1), (key2472, -2), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, 1), (key2524, 2), (key2569, 2), (key2580, -2)]

def row3446 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3447 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3448 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3449 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3450 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3451 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, -1), (key2724, -1), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, 1), (key3025, 1)]

def row3452 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

def row3453 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

def row3454 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2698, -2), (key2752, 2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, 2), (key2918, 2), (key2919, -4), (key3022, 2)]

def row3455 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3460 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2704, 1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2851, -1), (key2858, 3), (key2919, -1), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, -1), (key3022, 2), (key3025, -1)]

def row3461 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3462 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3463 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3464 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3465 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3466 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, -1), (key2784, 1), (key2792, -2), (key2801, -1), (key2807, 1), (key2851, 2), (key2858, -3), (key2868, -1), (key2919, 1), (key2922, 1)]

def row3467 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

def row3468 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

def row3469 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, 2), (key2792, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, -2), (key2918, -2), (key2919, 4), (key2922, -2)]

def row3470 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3471 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3472 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3473 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3474 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3475 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row3476 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

def row3477 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

def row3478 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2706, -2), (key2729, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, 2), (key2796, -4), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2898, 4), (key2905, -2), (key2913, -2)]

def row3479 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

def row3480 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

def row3481 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2786, -2), (key2796, 2), (key2809, 2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2898, -2), (key2905, 4), (key2913, -2)]

def row3482 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

def row3483 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

def row3484 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2706, 2), (key2729, -2), (key2738, -2), (key2748, 2), (key2786, -2), (key2794, -2), (key2796, 4), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2898, -4), (key2905, 2), (key2913, 2)]

def row3485 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

def row3486 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

def row3487 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2786, 2), (key2796, -2), (key2809, -2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2898, 2), (key2905, -4), (key2913, 2)]

def row3488 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

def row3489 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

def row3490 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, -2), (key1452, 2), (key1538, -4), (key1652, 4), (key1769, 6), (key1785, -2), (key1810, -4)]

def row3491 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

def row3492 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

def row3493 : Integer.Sparse Key := [(key1288, -2), (key1334, 2), (key1383, 2), (key1416, 4), (key1452, -6), (key1565, -4), (key1652, 4), (key1769, -2), (key1785, 6), (key1810, -4)]

def row3494 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

def row3495 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

def row3496 : Integer.Sparse Key := [(key1288, -2), (key1308, -4), (key1334, 6), (key1383, 2), (key1452, -2), (key1538, 4), (key1652, -4), (key1769, -6), (key1785, 2), (key1810, 4)]

def row3497 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row3498 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row3499 : Integer.Sparse Key := [(key1288, 2), (key1334, -2), (key1383, -2), (key1416, -4), (key1452, 6), (key1565, 4), (key1652, -4), (key1769, 2), (key1785, -6), (key1810, 4)]

def row3500 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row3501 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row3502 : Integer.Sparse Key := [(key2613, 2), (key2629, 2), (key2637, 2), (key2647, -4), (key2652, -2), (key2668, -2), (key2736, 2), (key2783, -2), (key2791, -2), (key2894, 2), (key2896, 2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row3503 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row3504 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row3505 : Integer.Sparse Key := [(key2613, -2), (key2647, 2), (key2668, 2), (key2703, 2), (key2723, 2), (key2736, -4), (key2746, -2), (key2806, -2), (key2826, -2), (key2894, 2), (key2903, 2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row3506 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

def row3507 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

def row3508 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, 2), (key2736, -2), (key2783, 2), (key2791, 2), (key2894, -2), (key2896, -2), (key2937, -4), (key2942, -2), (key2949, 2), (key2973, 2), (key2975, 2)]

def row3509 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row3510 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row3511 : Integer.Sparse Key := [(key2613, 2), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2806, 2), (key2826, 2), (key2894, -2), (key2903, -2), (key2937, 2), (key2949, -4), (key2959, -2), (key2973, 2), (key2982, 2)]

def row3512 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

def row3513 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

def row3514 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1069, 2), (key1107, -4), (key1148, 4), (key1191, 4), (key1197, 2), (key1210, -6)]

def row3515 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

def row3516 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

def row3517 : Integer.Sparse Key := [(key994, -2), (key1013, 2), (key1029, 6), (key1034, -4), (key1069, -2), (key1107, -4), (key1121, 4), (key1191, 4), (key1197, -6), (key1210, 2)]

def row3518 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row3519 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row3520 : Integer.Sparse Key := [(key994, -6), (key999, 4), (key1013, 2), (key1029, 2), (key1069, -2), (key1107, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

def row3521 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row3522 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row3523 : Integer.Sparse Key := [(key994, 2), (key1013, -2), (key1029, -6), (key1034, 4), (key1069, 2), (key1107, 4), (key1121, -4), (key1191, -4), (key1197, 6), (key1210, -2)]

def row3524 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

def row3525 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

def row3526 : Integer.Sparse Key := [(key2607, 2), (key2623, 4), (key2634, -6), (key2662, -2), (key2697, -4), (key2720, 6), (key2788, 2), (key2823, -2), (key2854, 4), (key2864, -4)]

def row3527 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

def row3528 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

def row3529 : Integer.Sparse Key := [(key2607, -2), (key2634, 2), (key2662, 2), (key2720, -2), (key2777, 4), (key2788, -6), (key2800, -4), (key2823, 6), (key2854, 4), (key2864, -4)]

def row3530 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

def row3531 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

def row3532 : Integer.Sparse Key := [(key2607, -2), (key2623, -4), (key2634, 6), (key2662, 2), (key2697, 4), (key2720, -6), (key2788, -2), (key2823, 2), (key2854, -4), (key2864, 4)]

def row3533 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

def row3534 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

def row3535 : Integer.Sparse Key := [(key2607, 2), (key2634, -2), (key2662, -2), (key2720, 2), (key2777, -4), (key2788, 6), (key2800, 4), (key2823, -6), (key2854, -4), (key2864, 4)]

def row3536 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

def row3537 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

def row3538 : Integer.Sparse Key := [(key1387, 2), (key1392, -2), (key1420, -2), (key1443, 2), (key1456, 2), (key1465, -2), (key1542, 4), (key1547, -2), (key1555, -2), (key1569, -2), (key1592, 2), (key1618, -2), (key1632, 2), (key1656, 2), (key1658, 2), (key1666, -4)]

def row3539 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

def row3540 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

def row3541 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1325, 2), (key1338, 2), (key1344, -2), (key1542, -2), (key1555, 2), (key1569, 4), (key1574, -2), (key1592, -2), (key1618, -2), (key1623, 2), (key1656, 2), (key1658, -4), (key1666, 2)]

def row3542 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

def row3543 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

def row3544 : Integer.Sparse Key := [(key1387, -2), (key1392, 2), (key1420, 2), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -4), (key1547, 2), (key1555, 2), (key1569, 2), (key1592, -2), (key1618, 2), (key1632, -2), (key1656, -2), (key1658, -2), (key1666, 4)]

def row3545 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

def row3546 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

def row3547 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1325, -2), (key1338, -2), (key1344, 2), (key1542, 2), (key1555, -2), (key1569, -4), (key1574, 2), (key1592, 2), (key1618, 2), (key1623, -2), (key1656, -2), (key1658, 4), (key1666, -2)]

def row3548 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

def row3549 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

def row3550 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, 2), (key3067, -2), (key3097, -6), (key3104, 6), (key3108, 4), (key3111, -4), (key3135, 2), (key3137, -2)]

def row3551 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

def row3552 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

def row3553 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -6), (key3067, 6), (key3071, 4), (key3073, -4), (key3097, 2), (key3104, -2), (key3135, -2), (key3137, 2)]

def row3554 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

def row3555 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

def row3556 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, -2), (key3067, 2), (key3097, 6), (key3104, -6), (key3108, -4), (key3111, 4), (key3135, -2), (key3137, 2)]

def row3557 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

def row3558 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

def row3559 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 6), (key3067, -6), (key3071, -4), (key3073, 4), (key3097, -2), (key3104, 2), (key3135, 2), (key3137, -2)]

def row3560 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

def row3561 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

def row3562 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, -2), (key1456, 2), (key1547, -2), (key1555, -2), (key1656, 2), (key1658, 2), (key1773, 4), (key1779, 2), (key1789, -2), (key1814, -2), (key1816, -2)]

def row3563 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

def row3564 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

def row3565 : Integer.Sparse Key := [(key1297, -2), (key1338, 2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1574, -2), (key1592, -2), (key1656, 2), (key1666, 2), (key1773, -2), (key1789, 4), (key1797, 2), (key1814, -2), (key1824, -2)]

def row3566 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

def row3567 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

def row3568 : Integer.Sparse Key := [(key1297, -2), (key1317, -2), (key1325, -2), (key1338, 4), (key1344, 2), (key1392, 2), (key1456, -2), (key1547, 2), (key1555, 2), (key1656, -2), (key1658, -2), (key1773, -4), (key1779, -2), (key1789, 2), (key1814, 2), (key1816, 2)]

def row3569 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row3570 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row3571 : Integer.Sparse Key := [(key1297, 2), (key1338, -2), (key1392, -2), (key1425, -2), (key1443, -2), (key1456, 4), (key1465, 2), (key1574, 2), (key1592, 2), (key1656, -2), (key1666, -2), (key1773, 2), (key1789, -4), (key1797, -2), (key1814, 2), (key1824, 2)]

def row3572 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

def row3573 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

def row3574 : Integer.Sparse Key := [(key993, 6), (key997, -4), (key1012, -2), (key1028, -2), (key1068, 2), (key1106, -4), (key1147, 4), (key1189, 4), (key1196, 2), (key1209, -6)]

def row3575 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

def row3576 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

def row3577 : Integer.Sparse Key := [(key993, -2), (key1012, 2), (key1028, 6), (key1032, -4), (key1068, -2), (key1106, -4), (key1120, 4), (key1189, 4), (key1196, -6), (key1209, 2)]

def row3578 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row3579 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row3580 : Integer.Sparse Key := [(key993, -6), (key997, 4), (key1012, 2), (key1028, 2), (key1068, -2), (key1106, 4), (key1147, -4), (key1189, -4), (key1196, -2), (key1209, 6)]

def row3581 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row3582 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

def row3583 : Integer.Sparse Key := [(key993, 2), (key1012, -2), (key1028, -6), (key1032, 4), (key1068, 2), (key1106, 4), (key1120, -4), (key1189, -4), (key1196, 6), (key1209, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3584 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

def row3585 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

def row3586 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, -4), (key2706, -2), (key2729, 2), (key2809, -2), (key2832, 2), (key2860, -2), (key2883, 2), (key2951, 2), (key2961, -2), (key2977, 4), (key2984, -2), (key2992, -2)]

def row3587 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

def row3588 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

def row3589 : Integer.Sparse Key := [(key2632, -2), (key2642, 2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, -4), (key2786, -2), (key2796, 2), (key2870, -2), (key2883, 2), (key2939, 2), (key2944, -2), (key2977, -2), (key2984, 4), (key2992, -2)]

def row3590 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

def row3591 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

def row3592 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, 4), (key2706, 2), (key2729, -2), (key2809, 2), (key2832, -2), (key2860, 2), (key2883, -2), (key2951, -2), (key2961, 2), (key2977, -4), (key2984, 2), (key2992, 2)]

def row3593 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

def row3594 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

def row3595 : Integer.Sparse Key := [(key2632, 2), (key2642, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, 4), (key2786, 2), (key2796, -2), (key2870, 2), (key2883, -2), (key2939, -2), (key2944, 2), (key2977, 2), (key2984, -4), (key2992, 2)]

def row3596 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

def row3597 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

def row3598 : Integer.Sparse Key := [(key2371, 6), (key2375, -4), (key2387, -2), (key2399, -2), (key2434, 2), (key2465, -4), (key2500, 4), (key2536, 4), (key2541, 2), (key2552, -6)]

def row3599 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

def row3600 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

def row3601 : Integer.Sparse Key := [(key2371, -2), (key2387, 2), (key2399, 6), (key2403, -4), (key2434, -2), (key2465, -4), (key2477, 4), (key2536, 4), (key2541, -6), (key2552, 2)]

def row3602 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row3603 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row3604 : Integer.Sparse Key := [(key2371, -6), (key2375, 4), (key2387, 2), (key2399, 2), (key2434, -2), (key2465, 4), (key2500, -4), (key2536, -4), (key2541, -2), (key2552, 6)]

def row3605 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row3606 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row3607 : Integer.Sparse Key := [(key2371, 2), (key2387, -2), (key2399, -6), (key2403, 4), (key2434, 2), (key2465, 4), (key2477, -4), (key2536, -4), (key2541, 6), (key2552, -2)]

def row3608 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

def row3609 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

def row3610 : Integer.Sparse Key := [(key2370, 6), (key2373, -4), (key2386, -2), (key2762, -2), (key2839, -4), (key2874, 4), (key2908, 2), (key2928, 2), (key2965, 4), (key2987, -6)]

def row3611 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

def row3612 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

def row3613 : Integer.Sparse Key := [(key2398, 6), (key2401, -4), (key2433, -2), (key2583, -2), (key2597, 2), (key2839, -4), (key2874, 4), (key2886, 4), (key2908, -6), (key2987, 2)]

def row3614 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

def row3615 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

def row3616 : Integer.Sparse Key := [(key2370, -6), (key2373, 4), (key2386, 2), (key2433, -2), (key2499, -4), (key2534, -4), (key2540, -2), (key2551, 6), (key2762, 2), (key2839, 4)]

def row3617 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

def row3618 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

def row3619 : Integer.Sparse Key := [(key2386, -2), (key2398, -6), (key2401, 4), (key2433, 2), (key2476, -4), (key2534, -4), (key2540, 6), (key2551, -2), (key2583, 2), (key2839, 4)]

def row3620 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

def row3621 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

def row3622 : Integer.Sparse Key := [(key2611, 2), (key2627, 2), (key2636, 2), (key2645, -4), (key2651, -2), (key2666, -2), (key2701, -2), (key2722, 4), (key2734, -2), (key2745, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2)]

def row3623 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

def row3624 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

def row3625 : Integer.Sparse Key := [(key2611, -2), (key2636, 2), (key2666, 2), (key2701, 2), (key2734, -4), (key2745, -2), (key2804, -2), (key2825, -2), (key2856, 2), (key2866, -2), (key2947, 4), (key2958, 2), (key2974, 2), (key2981, -2)]

def row3626 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

def row3627 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

def row3628 : Integer.Sparse Key := [(key2611, -2), (key2627, -2), (key2636, -2), (key2645, 4), (key2651, 2), (key2666, 2), (key2734, -2), (key2781, 2), (key2790, 2), (key2892, -2), (key2895, -2), (key2935, -4), (key2941, -2), (key2947, 2), (key2971, 2), (key2974, 2)]

def row3629 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

def row3630 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

def row3631 : Integer.Sparse Key := [(key2611, 2), (key2645, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2734, 4), (key2745, 2), (key2804, 2), (key2825, 2), (key2892, -2), (key2902, -2), (key2935, 2), (key2947, -4), (key2958, -2), (key2971, 2), (key2981, 2)]

def row3632 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

def row3633 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

def row3634 : Integer.Sparse Key := [(key2091, -2), (key2092, -4), (key2095, 6), (key2193, 2), (key2194, 4), (key2200, -6), (key2305, -4), (key2310, 4), (key2343, -2), (key2347, 2)]

def row3635 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

def row3636 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

def row3637 : Integer.Sparse Key := [(key2091, 6), (key2092, -4), (key2095, -2), (key2193, -2), (key2200, 2), (key2302, -4), (key2310, 4), (key2341, 4), (key2343, 2), (key2347, -6)]

def row3638 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

def row3639 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

def row3640 : Integer.Sparse Key := [(key2091, 2), (key2092, 4), (key2095, -6), (key2193, -2), (key2194, -4), (key2200, 6), (key2305, 4), (key2310, -4), (key2343, 2), (key2347, -2)]

def row3641 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3642 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3643 : Integer.Sparse Key := [(key2091, -2), (key2095, 2), (key2193, 6), (key2194, -4), (key2200, -2), (key2302, -4), (key2305, 4), (key2341, 4), (key2343, -6), (key2347, 2)]

def row3644 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

def row3645 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

def row3646 : Integer.Sparse Key := [(key2091, -6), (key2092, 4), (key2095, 2), (key2193, 2), (key2200, -2), (key2302, 4), (key2310, -4), (key2341, -4), (key2343, -2), (key2347, 6)]

def row3647 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3648 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3649 : Integer.Sparse Key := [(key2091, 2), (key2095, -2), (key2193, -6), (key2194, 4), (key2200, 2), (key2302, 4), (key2305, -4), (key2341, -4), (key2343, 6), (key2347, -2)]

def row3650 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

def row3651 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

def row3652 : Integer.Sparse Key := [(key2378, -4), (key2381, -2), (key2390, 2), (key2392, 4), (key2406, 4), (key2409, 2), (key2437, -2), (key2440, -4), (key2480, -2), (key2482, -2), (key2503, 2), (key2506, 2), (key2543, -2), (key2554, 2)]

def row3653 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row3654 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row3655 : Integer.Sparse Key := [(key2378, 4), (key2381, -2), (key2390, 2), (key2392, -4), (key2406, -2), (key2440, 2), (key2472, -2), (key2480, -2), (key2506, 2), (key2522, 2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row3656 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

def row3657 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

def row3658 : Integer.Sparse Key := [(key2378, 4), (key2381, 2), (key2390, -2), (key2392, -4), (key2406, -4), (key2409, -2), (key2437, 2), (key2440, 4), (key2480, 2), (key2482, 2), (key2503, -2), (key2506, -2), (key2543, 2), (key2554, -2)]

def row3659 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row3660 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row3661 : Integer.Sparse Key := [(key2378, -2), (key2392, 2), (key2406, 4), (key2409, -2), (key2437, 2), (key2440, -4), (key2472, -2), (key2482, 2), (key2503, -2), (key2522, 2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row3662 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

def row3663 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

def row3664 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, 2), (key2440, -2), (key2472, 2), (key2480, 2), (key2506, -2), (key2522, -2), (key2538, -2), (key2543, -4), (key2554, 4), (key2563, 2)]

def row3665 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

def row3666 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

def row3667 : Integer.Sparse Key := [(key2378, 2), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, 2), (key2482, -2), (key2503, 2), (key2522, -2), (key2538, -2), (key2543, 4), (key2554, -4), (key2563, 2)]

def row3668 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3669 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3670 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, 4), (key2802, 2), (key2806, 2), (key2826, -4), (key2857, -2), (key2867, 2), (key2896, -2), (key2903, 2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row3671 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

def row3672 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

def row3673 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2723, 2), (key2736, 2), (key2746, -2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2826, 2), (key2852, -2), (key2867, 2), (key2894, 2), (key2896, 2), (key2903, -4)]

def row3674 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3675 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3676 : Integer.Sparse Key := [(key2779, 2), (key2783, 2), (key2791, -4), (key2802, -2), (key2806, -2), (key2826, 4), (key2857, 2), (key2867, -2), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row3677 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

def row3678 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

def row3679 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2779, -2), (key2791, 2), (key2802, 4), (key2806, -2), (key2826, -2), (key2852, -2), (key2857, 2), (key2894, 2), (key2896, -4), (key2903, 2)]

def row3680 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row3681 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row3682 : Integer.Sparse Key := [(key2664, -2), (key2668, 2), (key2699, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, 2), (key2826, -2), (key2852, 2), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row3683 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

def row3684 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

def row3685 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2637, -2), (key2647, -2), (key2652, 2), (key2779, 2), (key2791, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, 2), (key2857, -2), (key2894, -2), (key2896, 4), (key2903, -2)]

def row3686 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

def row3687 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

def row3688 : Integer.Sparse Key := [(key2608, -2), (key2611, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2666, 4), (key2734, -4), (key2745, -2), (key2935, -4), (key2941, -2), (key2947, 4), (key2958, 2)]

def row3689 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

def row3690 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

def row3691 : Integer.Sparse Key := [(key2608, 2), (key2624, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2698, -4), (key2722, 4), (key2745, 2), (key2941, 2), (key2958, -2), (key2974, 4), (key2981, -4)]

def row3692 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

def row3693 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

def row3694 : Integer.Sparse Key := [(key2608, 2), (key2611, 4), (key2645, -4), (key2651, -2), (key2663, -2), (key2666, -4), (key2722, 4), (key2734, 4), (key2745, 4), (key2947, -4), (key2958, -2)]

def row3695 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

def row3696 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

def row3697 : Integer.Sparse Key := [(key2608, -2), (key2651, 2), (key2663, 2), (key2698, 4), (key2734, -4), (key2745, -4), (key2801, -4), (key2895, 4), (key2902, -4), (key2947, 4), (key2958, 2)]

def row3698 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

def row3699 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

def row3700 : Integer.Sparse Key := [(key2608, -2), (key2624, -4), (key2645, 4), (key2651, 2), (key2663, 2), (key2698, 4), (key2745, -2), (key2902, -4), (key2935, -4), (key2941, -2), (key2958, 2), (key2981, 4)]

def row3701 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

def row3702 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

def row3703 : Integer.Sparse Key := [(key2608, 2), (key2651, -2), (key2663, -2), (key2698, -4), (key2734, 4), (key2745, 2), (key2801, 4), (key2895, -4), (key2941, 2), (key2947, -4), (key2958, -2), (key2974, 4)]

def row3704 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3705 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3706 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3707 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3708 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3709 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3710 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

def row3711 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3712 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1424, -2), (key1457, 2), (key1573, 2), (key1659, -2), (key1788, 2), (key1790, -4), (key1813, -2), (key1817, 4), (key1839, 2), (key1841, -2)]

def row3713 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3714 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3715 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3716 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3717 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3718 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3719 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3720 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3721 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3722 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3723 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3724 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3725 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

def row3726 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

def row3727 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1424, 2), (key1457, -2), (key1573, -2), (key1659, 2), (key1788, -2), (key1790, 4), (key1813, 2), (key1817, -4), (key1839, -2), (key1841, 2)]

def row3728 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3729 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3730 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3731 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3732 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3733 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3734 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3735 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3736 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3737 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3738 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3739 : Integer.Sparse Key := [(key235, -2), (key247, 2), (key301, 2), (key315, -2), (key384, -4), (key393, 2), (key405, 4), (key416, -2), (key438, -2), (key448, 2)]

def row3740 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

def row3741 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

def row3742 : Integer.Sparse Key := [(key235, -2), (key256, 2), (key301, 2), (key326, -2), (key384, 4), (key393, -6), (key405, -4), (key416, 6), (key438, 4), (key448, -4)]

def row3743 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3744 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3745 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3746 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3747 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3748 : Integer.Sparse Key := [(key235, 2), (key247, -2), (key301, -2), (key315, 2), (key384, 4), (key393, -2), (key405, -4), (key416, 2), (key438, 2), (key448, -2)]

def row3749 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3750 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3751 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3752 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3753 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3754 : Integer.Sparse Key := [(key247, -2), (key256, 2), (key315, 2), (key326, -2), (key384, -2), (key393, 2), (key405, 2), (key416, -2), (key438, -4), (key448, 4)]

def row3755 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

def row3756 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

def row3757 : Integer.Sparse Key := [(key235, 2), (key256, -2), (key301, -2), (key326, 2), (key384, -4), (key393, 6), (key405, 4), (key416, -6), (key438, -4), (key448, 4)]

def row3758 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3759 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3760 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3761 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3762 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3763 : Integer.Sparse Key := [(key247, 2), (key256, -2), (key315, -2), (key326, 2), (key384, 2), (key393, -2), (key405, -2), (key416, 2), (key438, 4), (key448, -4)]

def row3764 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3765 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3766 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3767 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3768 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3769 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3770 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row3771 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row3772 : Integer.Sparse Key := [(key1298, -2), (key1326, 2), (key1393, 2), (key1444, -2), (key1548, 2), (key1556, -4), (key1575, -2), (key1593, 4), (key1624, 2), (key1633, -2), (key1896, 2), (key1899, -2), (key1903, -2), (key1911, 2), (key1920, 2), (key1926, -2)]

def row3773 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3774 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3775 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3776 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3777 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3778 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3779 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3780 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3781 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3782 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3783 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3784 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3785 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row3786 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row3787 : Integer.Sparse Key := [(key1298, 2), (key1326, -2), (key1393, -2), (key1444, 2), (key1548, -2), (key1556, 4), (key1575, 2), (key1593, -4), (key1624, -2), (key1633, 2), (key1896, -2), (key1899, 2), (key1903, 2), (key1911, -2), (key1920, -2), (key1926, 2)]

def row3788 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3789 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3790 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3791 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3792 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3793 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3794 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3795 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3796 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3797 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3798 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3799 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3800 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

def row3801 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

def row3802 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

def row3803 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3804 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3805 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3806 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3807 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3808 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3809 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3810 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3811 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3812 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3813 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3814 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3815 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

def row3816 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

def row3817 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

def row3818 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3819 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3820 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3821 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3822 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3823 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3824 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3825 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3826 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3827 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3828 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3829 : Integer.Sparse Key := [(key1290, -2), (key1310, 2), (key1385, 2), (key1418, -2), (key1540, -4), (key1552, 2), (key1567, 4), (key1589, -2), (key1620, -2), (key1629, 2)]

def row3830 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

def row3831 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

def row3832 : Integer.Sparse Key := [(key1290, -2), (key1322, 2), (key1385, 2), (key1440, -2), (key1540, 4), (key1552, -6), (key1567, -4), (key1589, 6), (key1620, 4), (key1629, -4)]

def row3833 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3834 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3835 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3836 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3837 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3838 : Integer.Sparse Key := [(key1290, 2), (key1310, -2), (key1385, -2), (key1418, 2), (key1540, 4), (key1552, -2), (key1567, -4), (key1589, 2), (key1620, 2), (key1629, -2)]

def row3839 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3840 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3841 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3842 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3843 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3844 : Integer.Sparse Key := [(key1310, -2), (key1322, 2), (key1418, 2), (key1440, -2), (key1540, -2), (key1552, 2), (key1567, 2), (key1589, -2), (key1620, -4), (key1629, 4)]

def row3845 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

def row3846 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

def row3847 : Integer.Sparse Key := [(key1290, 2), (key1322, -2), (key1385, -2), (key1440, 2), (key1540, -4), (key1552, 6), (key1567, 4), (key1589, -6), (key1620, -4), (key1629, 4)]

def row3848 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3849 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3850 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3851 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3852 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3853 : Integer.Sparse Key := [(key1310, 2), (key1322, -2), (key1418, -2), (key1440, 2), (key1540, 2), (key1552, -2), (key1567, -2), (key1589, 2), (key1620, 4), (key1629, -4)]

def row3854 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3855 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3856 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3857 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3858 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3859 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key389, -1), (key399, 1), (key407, -1), (key410, 2), (key420, -1), (key436, 1), (key444, -2), (key452, 1), (key468, -1), (key471, 1), (key569, -1), (key574, 1), (key579, 1), (key585, -1), (key597, -1), (key603, 1)]

def row3860 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

def row3861 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

def row3862 : Integer.Sparse Key := [(key237, 2), (key240, -2), (key249, -2), (key262, 2), (key268, 2), (key273, -2), (key386, -2), (key399, 2), (key407, 4), (key410, -2), (key420, -2), (key436, -2), (key444, 2), (key468, 2), (key471, -4), (key477, 2)]

def row3863 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3864 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3865 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3866 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3867 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3868 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key389, 1), (key399, -1), (key407, 1), (key410, -2), (key420, 1), (key436, -1), (key444, 2), (key452, -1), (key468, 1), (key471, -1), (key569, 1), (key574, -1), (key579, -1), (key585, 1), (key597, 1), (key603, -1)]

def row3869 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3870 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3871 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3872 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3873 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3874 : Integer.Sparse Key := [(key237, -1), (key240, 1), (key249, 1), (key262, -1), (key268, -1), (key273, 1), (key303, -1), (key306, 1), (key317, 1), (key330, -1), (key336, -1), (key342, 1), (key386, -1), (key389, 1), (key407, -1), (key410, 1), (key436, 2), (key444, -1), (key452, -1), (key468, -2), (key471, 1), (key477, 1)]

def row3875 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

def row3876 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

def row3877 : Integer.Sparse Key := [(key237, -2), (key240, 2), (key249, 2), (key262, -2), (key268, -2), (key273, 2), (key386, 2), (key399, -2), (key407, -4), (key410, 2), (key420, 2), (key436, 2), (key444, -2), (key468, -2), (key471, 4), (key477, -2)]

def row3878 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3879 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3880 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3881 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3882 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3883 : Integer.Sparse Key := [(key237, 1), (key240, -1), (key249, -1), (key262, 1), (key268, 1), (key273, -1), (key303, 1), (key306, -1), (key317, -1), (key330, 1), (key336, 1), (key342, -1), (key386, 1), (key389, -1), (key407, 1), (key410, -1), (key436, -2), (key444, 1), (key452, 1), (key468, 2), (key471, -1), (key477, -1)]

def row3884 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3885 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3886 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3887 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3888 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3889 : Integer.Sparse Key := [(key1406, -2), (key1409, 2), (key1434, 2), (key1438, -4), (key1476, -2), (key1478, 4), (key1587, 2), (key1687, -2), (key1909, -2), (key1924, 2)]

def row3890 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

def row3891 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

def row3892 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -6), (key1438, 4), (key1476, 6), (key1478, -4), (key1583, 2), (key1687, -2), (key1907, -2), (key1924, 2)]

def row3893 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3894 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3895 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3896 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3897 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3898 : Integer.Sparse Key := [(key1406, 2), (key1409, -2), (key1434, -2), (key1438, 4), (key1476, 2), (key1478, -4), (key1587, -2), (key1687, 2), (key1909, 2), (key1924, -2)]

def row3899 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3900 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3901 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3902 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3903 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3904 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 2), (key1438, -2), (key1476, -2), (key1478, 2), (key1583, 2), (key1587, -2), (key1907, -2), (key1909, 2)]

def row3905 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

def row3906 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

def row3907 : Integer.Sparse Key := [(key1406, -4), (key1409, 4), (key1434, 6), (key1438, -4), (key1476, -6), (key1478, 4), (key1583, -2), (key1687, 2), (key1907, 2), (key1924, -2)]

def row3908 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3909 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3910 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3911 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3912 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3913 : Integer.Sparse Key := [(key1406, 4), (key1409, -4), (key1434, -2), (key1438, 2), (key1476, 2), (key1478, -2), (key1583, -2), (key1587, 2), (key1907, 2), (key1909, -2)]

def row3914 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3915 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3916 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3917 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3918 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3919 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key249, 1), (key252, 1), (key303, 1), (key306, 1), (key317, -1), (key320, -2), (key330, -1), (key336, 1), (key342, 1), (key386, -1), (key389, -1), (key407, 1), (key410, 2), (key420, 1), (key468, -1), (key477, -1), (key579, -1), (key585, -1), (key594, 1), (key603, 1)]

def row3920 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

def row3921 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

def row3922 : Integer.Sparse Key := [(key240, -2), (key268, 2), (key306, 2), (key320, 2), (key330, 2), (key336, -4), (key342, -2), (key410, -2), (key420, -2), (key468, 2), (key477, 2), (key569, -2), (key579, 4), (key585, 2), (key594, -2), (key603, -2)]

def row3923 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3924 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3925 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3926 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3927 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3928 : Integer.Sparse Key := [(key237, 1), (key240, 1), (key249, -1), (key252, -1), (key303, -1), (key306, -1), (key317, 1), (key320, 2), (key330, 1), (key336, -1), (key342, -1), (key386, 1), (key389, 1), (key407, -1), (key410, -2), (key420, -1), (key468, 1), (key477, 1), (key579, 1), (key585, 1), (key594, -1), (key603, -1)]

def row3929 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3930 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3931 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3932 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3933 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3934 : Integer.Sparse Key := [(key252, -1), (key262, -1), (key268, 1), (key273, 1), (key320, -1), (key330, -1), (key336, 1), (key342, 1), (key389, 1), (key399, 1), (key410, 1), (key420, 1), (key468, -2), (key471, -1), (key477, -1), (key569, -1), (key574, -1), (key579, -1), (key585, -1), (key594, 2), (key597, 1), (key603, 1)]

def row3935 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

def row3936 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

def row3937 : Integer.Sparse Key := [(key240, 2), (key268, -2), (key306, -2), (key320, -2), (key330, -2), (key336, 4), (key342, 2), (key410, 2), (key420, 2), (key468, -2), (key477, -2), (key569, 2), (key579, -4), (key585, -2), (key594, 2), (key603, 2)]

def row3938 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3939 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3940 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3941 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3942 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3943 : Integer.Sparse Key := [(key252, 1), (key262, 1), (key268, -1), (key273, -1), (key320, 1), (key330, 1), (key336, -1), (key342, -1), (key389, -1), (key399, -1), (key410, -1), (key420, -1), (key468, 2), (key471, 1), (key477, 1), (key569, 1), (key574, 1), (key579, 1), (key585, 1), (key594, -2), (key597, -1), (key603, -1)]

def row3944 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3945 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3946 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3947 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3948 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3949 : Integer.Sparse Key := [(key43, -2), (key46, 4), (key71, -2), (key209, -2), (key214, 2), (key426, 2), (key457, -2), (key463, -4), (key480, 2), (key589, 2)]

def row3950 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

def row3951 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

def row3952 : Integer.Sparse Key := [(key43, 6), (key46, -4), (key71, -2), (key206, -2), (key214, 2), (key426, -4), (key457, 4), (key463, 4), (key480, -6), (key606, 2)]

def row3953 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3954 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3955 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3956 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3957 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3958 : Integer.Sparse Key := [(key43, 2), (key46, 2), (key71, 2), (key100, -2), (key103, -2), (key112, 6), (key134, -2), (key209, 2), (key214, -2), (key378, -6), (key429, 2), (key457, 2), (key463, -2), (key480, -2)]

def row3959 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3960 : Integer.Sparse Key := [(key18, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3961 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3962 : Integer.Sparse Key := [(key43, -2), (key100, 6), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key426, -2), (key429, 2), (key457, -6)]

def row3963 : Integer.Sparse Key := [(key18, -2), (key100, 4), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key209, 2), (key375, -2), (key378, 2), (key429, 2), (key457, -6)]

def row3964 : Integer.Sparse Key := [(key43, -2), (key100, 4), (key103, -2), (key112, -2), (key134, -2), (key171, 2), (key174, 2), (key179, 2), (key206, -2), (key209, 2), (key378, 2), (key429, 2), (key457, -6)]

def row3965 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

def row3966 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

def row3967 : Integer.Sparse Key := [(key32, -2), (key43, -6), (key46, 4), (key71, 2), (key112, -4), (key171, -4), (key174, 6), (key179, -2), (key206, 2), (key426, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3968 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2), (key426, 2)]

def row3969 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2), (key426, 2)]

def row3970 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2), (key426, 2)]

def row3971 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -6), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2), (key426, 2)]

def row3972 : Integer.Sparse Key := [(key18, 2), (key21, -2), (key46, -2), (key100, -4), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key375, 2)]

def row3973 : Integer.Sparse Key := [(key21, -2), (key43, 2), (key46, -2), (key100, -4), (key112, 2), (key134, 2), (key171, 4), (key174, -2), (key179, -2), (key206, 2)]

def row3974 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3975 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3976 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3977 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3978 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3979 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3980 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row3981 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row3982 : Integer.Sparse Key := [(key1316, -2), (key1339, 2), (key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1546, 2), (key1667, -2), (key1772, 2), (key1774, -4), (key1813, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row3983 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3984 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3985 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3986 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3987 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3988 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3989 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3990 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3991 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3992 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3993 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3994 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3995 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row3996 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row3997 : Integer.Sparse Key := [(key1316, 2), (key1339, -2), (key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1546, -2), (key1667, 2), (key1772, -2), (key1774, 4), (key1813, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row3998 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row3999 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4000 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4001 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4002 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4003 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4004 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4005 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4006 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4007 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4008 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4009 : Integer.Sparse Key := [(key1258, -2), (key1270, 2), (key1527, -2), (key1533, 4), (key1605, 2), (key1639, -2), (key1678, -4), (key1692, 2), (key1893, -2), (key1915, 2)]

def row4010 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

def row4011 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

def row4012 : Integer.Sparse Key := [(key1252, -2), (key1270, 2), (key1527, 6), (key1533, -4), (key1605, -4), (key1639, 4), (key1678, 4), (key1692, -6), (key1893, -2), (key1929, 2)]

def row4013 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4014 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4015 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4016 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4017 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4018 : Integer.Sparse Key := [(key1258, 2), (key1270, -2), (key1527, 2), (key1533, -4), (key1605, -2), (key1639, 2), (key1678, 4), (key1692, -2), (key1893, 2), (key1915, -2)]

def row4019 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4020 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4021 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4022 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4023 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4024 : Integer.Sparse Key := [(key1252, -2), (key1258, 2), (key1527, -2), (key1533, 2), (key1605, 4), (key1639, -4), (key1678, -2), (key1692, 2), (key1915, -2), (key1929, 2)]

def row4025 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

def row4026 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

def row4027 : Integer.Sparse Key := [(key1252, 2), (key1270, -2), (key1527, -6), (key1533, 4), (key1605, 4), (key1639, -4), (key1678, -4), (key1692, 6), (key1893, 2), (key1929, -2)]

def row4028 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4029 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4030 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4031 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4032 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4033 : Integer.Sparse Key := [(key1252, 2), (key1258, -2), (key1527, 2), (key1533, -2), (key1605, -4), (key1639, 4), (key1678, 2), (key1692, -2), (key1915, 2), (key1929, -2)]

def row4034 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4035 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4036 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4037 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4038 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4039 : Integer.Sparse Key := [(key1255, -2), (key1264, 2), (key1526, -2), (key1530, 4), (key1604, 2), (key1637, -2), (key1647, -4), (key1671, 2), (key1764, -2), (key1805, 2)]

def row4040 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

def row4041 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

def row4042 : Integer.Sparse Key := [(key1251, -2), (key1264, 2), (key1526, 6), (key1530, -4), (key1604, -4), (key1637, 4), (key1647, 4), (key1671, -6), (key1764, -2), (key1829, 2)]

def row4043 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4044 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4045 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4046 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4047 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4048 : Integer.Sparse Key := [(key1255, 2), (key1264, -2), (key1526, 2), (key1530, -4), (key1604, -2), (key1637, 2), (key1647, 4), (key1671, -2), (key1764, 2), (key1805, -2)]

def row4049 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4050 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4051 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4052 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4053 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4054 : Integer.Sparse Key := [(key1251, -2), (key1255, 2), (key1526, -2), (key1530, 2), (key1604, 4), (key1637, -4), (key1647, -2), (key1671, 2), (key1805, -2), (key1829, 2)]

def row4055 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

def row4056 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

def row4057 : Integer.Sparse Key := [(key1251, 2), (key1264, -2), (key1526, -6), (key1530, 4), (key1604, 4), (key1637, -4), (key1647, -4), (key1671, 6), (key1764, 2), (key1829, -2)]

def row4058 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4059 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4060 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4061 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4062 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4063 : Integer.Sparse Key := [(key1251, 2), (key1255, -2), (key1526, 2), (key1530, -2), (key1604, -4), (key1637, 4), (key1647, 2), (key1671, -2), (key1805, 2), (key1829, -2)]

def row4064 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4065 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4066 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4067 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4068 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4069 : Integer.Sparse Key := [(key1291, -1), (key1295, -1), (key1311, 1), (key1315, 1), (key1386, 1), (key1390, 1), (key1419, -1), (key1423, -1), (key1541, -1), (key1545, -2), (key1554, 1), (key1568, 1), (key1572, 2), (key1591, -1), (key1622, -1), (key1631, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4070 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row4071 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row4072 : Integer.Sparse Key := [(key1295, -2), (key1324, 2), (key1390, 2), (key1442, -2), (key1545, 2), (key1554, -4), (key1572, -2), (key1591, 4), (key1622, 2), (key1631, -2), (key1771, 2), (key1778, -2), (key1787, -2), (key1796, 2), (key1815, 2), (key1823, -2)]

def row4073 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4074 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4075 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4076 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4077 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4078 : Integer.Sparse Key := [(key1291, 1), (key1295, 1), (key1311, -1), (key1315, -1), (key1386, -1), (key1390, -1), (key1419, 1), (key1423, 1), (key1541, 1), (key1545, 2), (key1554, -1), (key1568, -1), (key1572, -2), (key1591, 1), (key1622, 1), (key1631, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4079 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4080 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4081 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4082 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4083 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4084 : Integer.Sparse Key := [(key1315, -1), (key1324, 1), (key1336, -1), (key1343, 1), (key1423, 1), (key1442, -1), (key1454, 1), (key1464, -1), (key1545, -1), (key1554, 1), (key1572, 1), (key1591, -1), (key1622, -2), (key1631, 2), (key1657, -1), (key1665, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4085 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row4086 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row4087 : Integer.Sparse Key := [(key1295, 2), (key1324, -2), (key1390, -2), (key1442, 2), (key1545, -2), (key1554, 4), (key1572, 2), (key1591, -4), (key1622, -2), (key1631, 2), (key1771, -2), (key1778, 2), (key1787, 2), (key1796, -2), (key1815, -2), (key1823, 2)]

def row4088 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4089 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4090 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4091 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4092 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4093 : Integer.Sparse Key := [(key1315, 1), (key1324, -1), (key1336, 1), (key1343, -1), (key1423, -1), (key1442, 1), (key1454, -1), (key1464, 1), (key1545, 1), (key1554, -1), (key1572, -1), (key1591, 1), (key1622, 2), (key1631, -2), (key1657, 1), (key1665, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4094 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4095 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4096 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4097 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4098 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4099 : Integer.Sparse Key := [(key747, -2), (key751, 2), (key830, -2), (key831, 4), (key840, -2), (key924, 2), (key928, -4), (key935, 2), (key960, -2), (key962, 2)]

def row4100 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

def row4101 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

def row4102 : Integer.Sparse Key := [(key746, -2), (key751, 2), (key830, 6), (key831, -4), (key840, -2), (key924, -4), (key928, 4), (key960, 4), (key962, -6), (key964, 2)]

def row4103 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4104 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4105 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4106 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4107 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4108 : Integer.Sparse Key := [(key747, 2), (key751, -2), (key830, 2), (key831, -4), (key840, 2), (key924, -2), (key928, 4), (key935, -2), (key960, 2), (key962, -2)]

def row4109 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4110 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4111 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4112 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4113 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4114 : Integer.Sparse Key := [(key746, -2), (key747, 2), (key830, -2), (key831, 2), (key924, 4), (key928, -2), (key935, -2), (key960, -4), (key962, 2), (key964, 2)]

def row4115 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

def row4116 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

def row4117 : Integer.Sparse Key := [(key746, 2), (key751, -2), (key830, -6), (key831, 4), (key840, 2), (key924, 4), (key928, -4), (key960, -4), (key962, 6), (key964, -2)]

def row4118 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4119 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4120 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4121 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4122 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4123 : Integer.Sparse Key := [(key746, 2), (key747, -2), (key830, 2), (key831, -2), (key924, -4), (key928, 2), (key935, 2), (key960, 4), (key962, -2), (key964, -2)]

def row4124 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4125 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4126 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4127 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4128 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4129 : Integer.Sparse Key := [(key1256, -1), (key1260, -1), (key1265, 1), (key1267, 1), (key1535, 2), (key1609, 1), (key1641, -1), (key1648, -1), (key1650, -2), (key1673, 1), (key1765, -2), (key1806, 2), (key1808, 1), (key1831, -1), (key1836, -1), (key1847, 1)]

def row4130 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

def row4131 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

def row4132 : Integer.Sparse Key := [(key1256, -2), (key1267, 2), (key1531, 4), (key1535, -2), (key1609, -2), (key1641, 2), (key1650, 2), (key1673, -4), (key1765, 2), (key1767, -4), (key1806, -2), (key1831, 4), (key1836, 2), (key1847, -2)]

def row4133 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4134 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4135 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4136 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4137 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4138 : Integer.Sparse Key := [(key1256, 1), (key1260, 1), (key1265, -1), (key1267, -1), (key1535, -2), (key1609, -1), (key1641, 1), (key1648, 1), (key1650, 2), (key1673, -1), (key1765, 2), (key1806, -2), (key1808, -1), (key1831, 1), (key1836, 1), (key1847, -1)]

def row4139 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4140 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4141 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4142 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4143 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4144 : Integer.Sparse Key := [(key1256, -1), (key1260, 1), (key1265, -1), (key1267, 1), (key1531, -1), (key1535, 1), (key1609, 2), (key1641, -2), (key1648, 1), (key1650, -1), (key1765, -1), (key1767, 1), (key1806, 1), (key1808, -1), (key1836, -2), (key1847, 2)]

def row4145 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

def row4146 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

def row4147 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

def row4148 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4149 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4150 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4151 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4152 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4153 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4154 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4155 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4156 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4157 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4158 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4159 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4160 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

def row4161 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

def row4162 : Integer.Sparse Key := [(key1292, 2), (key1298, -2), (key1312, -2), (key1326, 2), (key1351, 2), (key1354, -2), (key1420, -2), (key1472, 2), (key1569, 4), (key1575, -2), (key1618, -2), (key1624, 2), (key1681, 2), (key1683, -4), (key1903, -2), (key1920, 2)]

def row4163 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4164 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4165 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4166 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4167 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4168 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4169 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4170 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4171 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4172 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4173 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4174 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4175 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

def row4176 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

def row4177 : Integer.Sparse Key := [(key1292, -2), (key1298, 2), (key1312, 2), (key1326, -2), (key1351, -2), (key1354, 2), (key1420, 2), (key1472, -2), (key1569, -4), (key1575, 2), (key1618, 2), (key1624, -2), (key1681, -2), (key1683, 4), (key1903, 2), (key1920, -2)]

def row4178 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4179 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4180 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4181 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4182 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4183 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4184 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4185 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4186 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4187 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4188 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4189 : Integer.Sparse Key := [(key1295, -2), (key1336, 2), (key1390, 2), (key1454, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1771, -2), (key1787, 2)]

def row4190 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

def row4191 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

def row4192 : Integer.Sparse Key := [(key1291, -2), (key1343, 2), (key1386, 2), (key1464, -2), (key1541, 4), (key1554, -4), (key1568, -4), (key1591, 4), (key1657, 4), (key1665, -4), (key1778, -2), (key1796, 2)]

def row4193 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4194 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4195 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4196 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4197 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4198 : Integer.Sparse Key := [(key1295, 2), (key1336, -2), (key1390, -2), (key1454, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1771, 2), (key1787, -2)]

def row4199 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4200 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4201 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4202 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4203 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4204 : Integer.Sparse Key := [(key1311, -2), (key1324, 2), (key1419, 2), (key1442, -2), (key1541, -2), (key1554, 2), (key1568, 2), (key1591, -2), (key1657, -2), (key1665, 2), (key1815, -2), (key1823, 2)]

def row4205 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

def row4206 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

def row4207 : Integer.Sparse Key := [(key1291, 2), (key1343, -2), (key1386, -2), (key1464, 2), (key1541, -4), (key1554, 4), (key1568, 4), (key1591, -4), (key1657, -4), (key1665, 4), (key1778, 2), (key1796, -2)]

def row4208 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4209 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4210 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4211 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4212 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4213 : Integer.Sparse Key := [(key1311, 2), (key1324, -2), (key1419, -2), (key1442, 2), (key1541, 2), (key1554, -2), (key1568, -2), (key1591, 2), (key1657, 2), (key1665, -2), (key1815, 2), (key1823, -2)]

def row4214 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4215 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4216 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4217 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4218 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4219 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -1), (key267, -1), (key271, 1), (key319, -1), (key328, -1), (key335, 1), (key340, 1), (key406, -1), (key409, 2), (key418, 1), (key435, 1), (key442, -1), (key467, -2), (key469, 1), (key475, -1), (key578, -1), (key583, -1), (key593, 1), (key601, 1)]

def row4220 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

def row4221 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

def row4222 : Integer.Sparse Key := [(key236, 2), (key239, -2), (key248, -2), (key260, 2), (key267, 2), (key271, -2), (key316, -2), (key335, 2), (key406, 4), (key409, -2), (key418, -2), (key435, -2), (key442, 2), (key467, 2), (key469, -4), (key595, 2)]

def row4223 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4224 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4225 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4226 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4227 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4228 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 3), (key267, -1), (key271, -1), (key319, 1), (key328, 1), (key335, -1), (key340, -1), (key406, 1), (key409, -2), (key418, -1), (key435, -1), (key442, 3), (key469, -1), (key475, -1), (key578, 1), (key583, 1), (key593, -1), (key595, 2), (key601, -1)]

def row4229 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4230 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4231 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key328, -1), (key335, 1), (key340, 1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4232 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key328, -1), (key335, 1), (key340, 1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4233 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4234 : Integer.Sparse Key := [(key236, -1), (key239, 1), (key248, 1), (key260, -3), (key267, 1), (key271, 1), (key302, -1), (key305, 1), (key316, 1), (key328, -1), (key335, 1), (key340, 1), (key385, -1), (key388, 1), (key397, -2), (key406, -1), (key409, 1), (key435, 2), (key442, -3), (key450, -1), (key469, 1), (key475, 1)]

def row4235 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

def row4236 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

def row4237 : Integer.Sparse Key := [(key236, -2), (key239, 2), (key248, 2), (key260, -2), (key267, -2), (key271, 2), (key316, 2), (key397, -2), (key406, -4), (key409, 2), (key418, 2), (key435, 2), (key442, -2), (key467, -2), (key469, 4), (key475, -2)]

def row4238 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4239 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4240 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key328, 1), (key335, 1), (key340, -1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4241 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key328, 1), (key335, 1), (key340, -1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4242 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4243 : Integer.Sparse Key := [(key236, 1), (key239, -1), (key248, -1), (key260, 1), (key267, 1), (key271, -1), (key302, 1), (key305, -1), (key316, -1), (key328, 1), (key335, 1), (key340, -1), (key385, 1), (key388, -1), (key406, 1), (key409, -1), (key435, -2), (key442, 1), (key450, 1), (key467, 2), (key469, -1), (key475, -1)]

def row4244 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4245 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4246 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4247 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4248 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4249 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2794, -1), (key2796, 1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, 1), (key2883, -2), (key2898, -1), (key2905, -1), (key2913, 2)]

def row4250 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4251 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4252 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4253 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4254 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4255 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, 1), (key2832, -1), (key2860, -1), (key2870, -1), (key2883, 2), (key2898, 1), (key2905, 1), (key2913, -2)]

def row4256 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4257 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4258 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4259 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4260 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4261 : Integer.Sparse Key := [(key1308, -2), (key1334, 2), (key1416, -2), (key1452, 2), (key1538, 2), (key1565, 2), (key1652, -4), (key1769, -2), (key1785, -2), (key1810, 4)]

def row4262 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4263 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4264 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4265 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4266 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4267 : Integer.Sparse Key := [(key1308, 2), (key1334, -2), (key1416, 2), (key1452, -2), (key1538, -2), (key1565, -2), (key1652, 4), (key1769, 2), (key1785, 2), (key1810, -4)]

def row4268 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4269 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4270 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4271 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4272 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4273 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2647, 1), (key2652, 1), (key2703, -1), (key2723, -1), (key2736, 1), (key2746, 1), (key2783, 1), (key2791, 1), (key2806, 1), (key2826, 1), (key2894, -2), (key2896, -1), (key2903, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2959, -1), (key2973, 2), (key2975, 1), (key2982, 1)]

def row4274 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4275 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4276 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4277 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4278 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4279 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2647, -1), (key2652, -1), (key2703, 1), (key2723, 1), (key2736, -1), (key2746, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2826, -1), (key2894, 2), (key2896, 1), (key2903, 1), (key2937, 1), (key2942, 1), (key2949, 1), (key2959, 1), (key2973, -2), (key2975, -1), (key2982, -1)]

def row4280 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4281 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4282 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4283 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4284 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4285 : Integer.Sparse Key := [(key994, -2), (key999, 2), (key1029, -2), (key1034, 2), (key1107, 4), (key1121, -2), (key1148, -2), (key1191, -4), (key1197, 2), (key1210, 2)]

def row4286 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4287 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4288 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4289 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4290 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4291 : Integer.Sparse Key := [(key994, 2), (key999, -2), (key1029, 2), (key1034, -2), (key1107, -4), (key1121, 2), (key1148, 2), (key1191, 4), (key1197, -2), (key1210, -2)]

def row4292 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4293 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4294 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4295 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4296 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4297 : Integer.Sparse Key := [(key2623, -2), (key2634, 2), (key2697, 2), (key2720, -2), (key2777, -2), (key2788, 2), (key2800, 2), (key2823, -2), (key2854, -4), (key2864, 4)]

def row4298 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4299 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4300 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4301 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4302 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4303 : Integer.Sparse Key := [(key2623, 2), (key2634, -2), (key2697, -2), (key2720, 2), (key2777, 2), (key2788, -2), (key2800, -2), (key2823, 2), (key2854, 4), (key2864, -4)]

def row4304 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4305 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4306 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4307 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4308 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4309 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1325, -1), (key1338, -1), (key1344, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1443, -1), (key1456, -1), (key1465, 1), (key1542, -1), (key1547, 1), (key1569, -1), (key1574, 1), (key1618, 2), (key1623, -1), (key1632, -1), (key1656, -2), (key1658, 1), (key1666, 1)]

def row4310 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4311 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4312 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4313 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4314 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4315 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, 1), (key1574, -1), (key1618, -2), (key1623, 1), (key1632, 1), (key1656, 2), (key1658, -1), (key1666, -1)]

def row4316 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4317 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4318 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4319 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4320 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4321 : Integer.Sparse Key := [(key3048, -4), (key3052, 4), (key3062, 2), (key3067, -2), (key3071, -2), (key3073, 2), (key3097, 2), (key3104, -2), (key3108, -2), (key3111, 2)]

def row4322 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4323 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4324 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4325 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4326 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4327 : Integer.Sparse Key := [(key3048, 4), (key3052, -4), (key3062, -2), (key3067, 2), (key3071, 2), (key3073, -2), (key3097, -2), (key3104, 2), (key3108, 2), (key3111, -2)]

def row4328 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4329 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4330 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4331 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4332 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4333 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1338, 1), (key1344, 1), (key1425, -1), (key1443, -1), (key1456, 1), (key1465, 1), (key1547, 1), (key1555, 1), (key1574, 1), (key1592, 1), (key1656, -2), (key1658, -1), (key1666, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1797, -1), (key1814, 2), (key1816, 1), (key1824, 1)]

def row4334 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4335 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4336 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4337 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4338 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4339 : Integer.Sparse Key := [(key1317, 1), (key1325, 1), (key1338, -1), (key1344, -1), (key1425, 1), (key1443, 1), (key1456, -1), (key1465, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1592, -1), (key1656, 2), (key1658, 1), (key1666, 1), (key1773, 1), (key1779, 1), (key1789, 1), (key1797, 1), (key1814, -2), (key1816, -1), (key1824, -1)]

def row4340 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4341 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4342 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4343 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4344 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4345 : Integer.Sparse Key := [(key993, -2), (key997, 2), (key1028, -2), (key1032, 2), (key1106, 4), (key1120, -2), (key1147, -2), (key1189, -4), (key1196, 2), (key1209, 2)]

def row4346 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4347 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4348 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4349 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4350 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

def row4351 : Integer.Sparse Key := [(key993, 2), (key997, -2), (key1028, 2), (key1032, -2), (key1106, -4), (key1120, 2), (key1147, 2), (key1189, 4), (key1196, -2), (key1209, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4352 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4353 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4354 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4355 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4356 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4357 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, -1), (key2642, 1), (key2671, -1), (key2674, 1), (key2726, -1), (key2729, 1), (key2786, 1), (key2796, -1), (key2809, 1), (key2832, -1), (key2860, 1), (key2870, 1), (key2883, -2), (key2939, -1), (key2944, 1), (key2951, -1), (key2961, 1), (key2977, -1), (key2984, -1), (key2992, 2)]

def row4358 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4359 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4360 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4361 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4362 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4363 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, 1), (key2729, -1), (key2786, -1), (key2796, 1), (key2809, -1), (key2832, 1), (key2860, -1), (key2870, -1), (key2883, 2), (key2939, 1), (key2944, -1), (key2951, 1), (key2961, -1), (key2977, 1), (key2984, 1), (key2992, -2)]

def row4364 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4365 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4366 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4367 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4368 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4369 : Integer.Sparse Key := [(key2371, -2), (key2375, 2), (key2399, -2), (key2403, 2), (key2465, 4), (key2477, -2), (key2500, -2), (key2536, -4), (key2541, 2), (key2552, 2)]

def row4370 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4371 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4372 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4373 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4374 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4375 : Integer.Sparse Key := [(key2371, 2), (key2375, -2), (key2399, 2), (key2403, -2), (key2465, -4), (key2477, 2), (key2500, 2), (key2536, 4), (key2541, -2), (key2552, -2)]

def row4376 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4377 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4378 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4379 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4380 : Integer.Sparse Key := [(key2370, -2), (key2464, 4), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2842, 2), (key2874, -6)]

def row4381 : Integer.Sparse Key := [(key2398, -2), (key2464, 4), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2842, 2), (key2874, -6)]

def row4382 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2), (key2839, 2)]

def row4383 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2), (key2839, 2)]

def row4384 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2), (key2839, 2)]

def row4385 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -6), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2), (key2839, 2)]

def row4386 : Integer.Sparse Key := [(key2370, 2), (key2373, -2), (key2401, -2), (key2464, -4), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2762, 2)]

def row4387 : Integer.Sparse Key := [(key2373, -2), (key2398, 2), (key2401, -2), (key2464, -4), (key2476, 2), (key2499, 2), (key2534, 4), (key2540, -2), (key2551, -2), (key2583, 2)]

def row4388 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4389 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4390 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4391 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4392 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4393 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2645, 1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, 1), (key2804, 1), (key2825, 1), (key2892, -2), (key2895, -1), (key2902, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, 1), (key2981, 1)]

def row4394 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4395 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4396 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4397 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4398 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4399 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2825, -1), (key2892, 2), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2971, -2), (key2974, -1), (key2981, -1)]

def row4400 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4401 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4402 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4403 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4404 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4405 : Integer.Sparse Key := [(key2092, -2), (key2095, 2), (key2193, -2), (key2194, 4), (key2200, -2), (key2302, 2), (key2305, -4), (key2310, 2), (key2341, -2), (key2343, 2)]

def row4406 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4407 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4408 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4409 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4410 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4411 : Integer.Sparse Key := [(key2092, 2), (key2095, -2), (key2193, 2), (key2194, -4), (key2200, 2), (key2302, -2), (key2305, 4), (key2310, -2), (key2341, 2), (key2343, -2)]

def row4412 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4413 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4414 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4415 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4416 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4417 : Integer.Sparse Key := [(key2091, -2), (key2092, 2), (key2193, -2), (key2194, 2), (key2302, 4), (key2305, -2), (key2310, -2), (key2341, -4), (key2343, 2), (key2347, 2)]

def row4418 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4419 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4420 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4421 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4422 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4423 : Integer.Sparse Key := [(key2091, 2), (key2092, -2), (key2193, 2), (key2194, -2), (key2302, -4), (key2305, 2), (key2310, 2), (key2341, 4), (key2343, -2), (key2347, -2)]

def row4424 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4425 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4426 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4427 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4428 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4429 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, 1), (key2392, 1), (key2409, 2), (key2437, -2), (key2472, 1), (key2480, -1), (key2482, -2), (key2503, 2), (key2506, 1), (key2522, -1), (key2538, -1), (key2543, 1), (key2554, -1), (key2563, 1)]

def row4430 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4431 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4432 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4433 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4434 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4435 : Integer.Sparse Key := [(key2378, 1), (key2381, 1), (key2390, -1), (key2392, -1), (key2409, -2), (key2437, 2), (key2472, -1), (key2480, 1), (key2482, 2), (key2503, -2), (key2506, -1), (key2522, 1), (key2538, 1), (key2543, -1), (key2554, 1), (key2563, -1)]

def row4436 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4437 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4438 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4439 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4440 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4441 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, -1), (key2392, 1), (key2406, -1), (key2409, 1), (key2437, -1), (key2440, 1), (key2472, 2), (key2480, 1), (key2482, -1), (key2503, 1), (key2506, -1), (key2522, -2), (key2538, -2), (key2563, 2)]

def row4442 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4443 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4444 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4445 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4446 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4447 : Integer.Sparse Key := [(key2378, 1), (key2381, -1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, 1), (key2440, -1), (key2472, -2), (key2480, -1), (key2482, 1), (key2503, -1), (key2506, 1), (key2522, 2), (key2538, 2), (key2563, -2)]

def row4448 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4449 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4450 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4451 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4452 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4453 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2783, -1), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2852, 1), (key2857, -2), (key2867, 1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row4454 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4455 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4456 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4457 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4458 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4459 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2783, 1), (key2791, -1), (key2802, 1), (key2806, -2), (key2826, 1), (key2852, -1), (key2857, 2), (key2867, -1), (key2894, 1), (key2896, -1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row4460 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4461 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4462 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4463 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4464 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4465 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2723, -1), (key2736, -1), (key2746, 1), (key2779, -1), (key2783, 1), (key2802, -1), (key2806, 1), (key2852, 2), (key2857, -1), (key2867, -1), (key2894, -2), (key2896, 1), (key2903, 1)]

def row4466 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4467 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4468 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4469 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4470 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4471 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, 1), (key2867, 1), (key2894, 2), (key2896, -1), (key2903, -1)]

def row4472 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4473 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4474 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4475 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4476 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4477 : Integer.Sparse Key := [(key2611, -2), (key2645, 2), (key2666, 2), (key2698, -2), (key2722, -2), (key2801, 2), (key2895, -2), (key2902, 2)]

def row4478 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4479 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4480 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4481 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4482 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4483 : Integer.Sparse Key := [(key2611, 2), (key2636, -2), (key2666, -2), (key2698, 2), (key2701, 2), (key2722, 2), (key2781, -2), (key2801, -2), (key2895, 2), (key2974, -2)]

def row4484 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4485 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4486 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4487 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4488 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4489 : Integer.Sparse Key := [(key2624, -2), (key2636, 2), (key2698, -2), (key2722, -2), (key2778, 2), (key2790, 2), (key2801, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, -2), (key2971, 2), (key2974, 2), (key2981, 2)]

def row4490 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4491 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4492 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4493 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4494 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4495 : Integer.Sparse Key := [(key2624, 2), (key2645, -2), (key2698, 2), (key2734, -2), (key2778, -2), (key2801, -2), (key2895, 2), (key2902, 2), (key2935, 2), (key2947, 2), (key2974, -2), (key2981, -2)]

def row4496 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4497 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4498 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4499 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4500 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4501 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1545, -1), (key1554, 1), (key1568, -1), (key1572, 2), (key1591, -1), (key1617, 1), (key1622, -2), (key1631, 1), (key1654, -1), (key1657, 1), (key1771, -1), (key1778, 1), (key1787, 1), (key1796, -1), (key1815, -1), (key1823, 1)]

def row4502 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

def row4503 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

def row4504 : Integer.Sparse Key := [(key1291, 2), (key1295, -2), (key1311, -2), (key1324, 2), (key1336, 2), (key1343, -2), (key1541, -2), (key1554, 2), (key1568, 4), (key1572, -2), (key1591, -2), (key1617, -2), (key1622, 2), (key1654, 2), (key1657, -4), (key1665, 2)]

def row4505 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4506 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4507 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4508 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4509 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4510 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1545, 1), (key1554, -1), (key1568, 1), (key1572, -2), (key1591, 1), (key1617, -1), (key1622, 2), (key1631, -1), (key1654, 1), (key1657, -1), (key1771, 1), (key1778, -1), (key1787, -1), (key1796, 1), (key1815, 1), (key1823, -1)]

def row4511 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4512 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4513 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4514 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4515 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4516 : Integer.Sparse Key := [(key1291, -1), (key1295, 1), (key1311, 1), (key1324, -1), (key1336, -1), (key1343, 1), (key1386, -1), (key1390, 1), (key1419, 1), (key1442, -1), (key1454, -1), (key1464, 1), (key1541, -1), (key1545, 1), (key1568, -1), (key1572, 1), (key1617, 2), (key1622, -1), (key1631, -1), (key1654, -2), (key1657, 1), (key1665, 1)]

def row4517 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

def row4518 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

def row4519 : Integer.Sparse Key := [(key1291, -2), (key1295, 2), (key1311, 2), (key1324, -2), (key1336, -2), (key1343, 2), (key1541, 2), (key1554, -2), (key1568, -4), (key1572, 2), (key1591, 2), (key1617, 2), (key1622, -2), (key1654, -2), (key1657, 4), (key1665, -2)]

def row4520 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4521 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4522 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4523 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4524 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4525 : Integer.Sparse Key := [(key1291, 1), (key1295, -1), (key1311, -1), (key1324, 1), (key1336, 1), (key1343, -1), (key1386, 1), (key1390, -1), (key1419, -1), (key1442, 1), (key1454, 1), (key1464, -1), (key1541, 1), (key1545, -1), (key1568, 1), (key1572, -1), (key1617, -2), (key1622, 1), (key1631, 1), (key1654, 2), (key1657, -1), (key1665, -1)]

def row4526 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4527 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4528 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4529 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4530 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4531 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -1), (key2645, -1), (key2651, 1), (key2701, -1), (key2722, -1), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, 2), (key2825, 1), (key2851, 1), (key2856, -1), (key2892, -2), (key2895, 1), (key2902, -1), (key2947, -1), (key2958, -1), (key2971, 1), (key2981, 1)]

def row4532 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

def row4533 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

def row4534 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2636, 2), (key2645, 2), (key2651, -2), (key2698, -2), (key2734, 2), (key2801, 4), (key2804, -2), (key2825, -2), (key2851, -2), (key2856, 2), (key2892, 2), (key2895, -4), (key2974, 2)]

def row4535 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4536 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4537 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4538 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4539 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4540 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 3), (key2645, -1), (key2651, -1), (key2701, 1), (key2722, 1), (key2734, -1), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2851, -1), (key2856, 3), (key2895, -1), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, -1), (key2974, 2), (key2981, -1)]

def row4541 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4542 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4543 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4544 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4545 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4546 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2636, -3), (key2645, 1), (key2651, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, -1), (key2781, 1), (key2790, -2), (key2801, -1), (key2804, 1), (key2851, 2), (key2856, -3), (key2866, -1), (key2895, 1), (key2902, 1)]

def row4547 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

def row4548 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

def row4549 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2636, -2), (key2645, -2), (key2651, 2), (key2698, 2), (key2790, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2851, 2), (key2856, -2), (key2892, -2), (key2895, 4), (key2902, -2)]

def row4550 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4551 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4552 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4553 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4554 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4555 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2801, 1), (key2804, -1), (key2851, -2), (key2856, 1), (key2866, 1), (key2892, 2), (key2895, -1), (key2902, -1)]

def row4556 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4557 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4558 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4559 : Integer.Sparse Key := [(key1492, 6), (key1496, -6), (key1718, -6), (key1728, 6), (key1865, 6), (key1870, -6)]

def row4560 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4561 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4562 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4563 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4564 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4565 : Integer.Sparse Key := [(key1492, -2), (key1496, 2), (key1718, 2), (key1728, -2), (key1865, -2), (key1870, 2)]

def row4566 : Integer.Sparse Key := [(key1492, -6), (key1496, 6), (key1718, 6), (key1728, -6), (key1865, -6), (key1870, 6)]

def row4567 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4568 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4569 : Integer.Sparse Key := [(key1492, 2), (key1496, -2), (key1718, -2), (key1728, 2), (key1865, 2), (key1870, -2)]

def row4570 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4571 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4572 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4573 : Integer.Sparse Key := [(key281, 6), (key290, -6), (key350, -6), (key367, 6), (key516, 6), (key538, -6)]

def row4574 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4575 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4576 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4577 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4578 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4579 : Integer.Sparse Key := [(key281, -2), (key290, 2), (key350, 2), (key367, -2), (key516, -2), (key538, 2)]

def row4580 : Integer.Sparse Key := [(key281, -6), (key290, 6), (key350, 6), (key367, -6), (key516, -6), (key538, 6)]

def row4581 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4582 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4583 : Integer.Sparse Key := [(key281, 2), (key290, -2), (key350, -2), (key367, 2), (key516, 2), (key538, -2)]

def row4584 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4585 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4586 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4587 : Integer.Sparse Key := [(key1367, 6), (key1376, -6), (key1493, -6), (key1515, 6), (key1725, 6), (key1743, -6)]

def row4588 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4589 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4590 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4591 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4592 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4593 : Integer.Sparse Key := [(key1367, -2), (key1376, 2), (key1493, 2), (key1515, -2), (key1725, -2), (key1743, 2)]

def row4594 : Integer.Sparse Key := [(key1367, -6), (key1376, 6), (key1493, 6), (key1515, -6), (key1725, -6), (key1743, 6)]

def row4595 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4596 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4597 : Integer.Sparse Key := [(key1367, 2), (key1376, -2), (key1493, -2), (key1515, 2), (key1725, 2), (key1743, -2)]

def row4598 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

def row4599 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

def row4600 : Integer.Sparse Key := [(key29, -2), (key33, 2), (key495, 2), (key554, -2), (key665, -2), (key682, 2)]

def row4601 : Integer.Sparse Key := [(key29, 6), (key33, -6), (key495, -6), (key554, 6), (key665, 6), (key682, -6)]

def row4602 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

def row4603 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

def row4604 : Integer.Sparse Key := [(key29, 2), (key33, 4), (key109, -2), (key113, -4), (key149, 6), (key228, -6), (key500, 4), (key554, 2), (key665, -4), (key682, -2)]

def row4605 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

def row4606 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

def row4607 : Integer.Sparse Key := [(key109, 6), (key113, -4), (key149, -2), (key175, 4), (key185, 2), (key223, -2), (key228, 2), (key495, -4), (key500, 4), (key554, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4608 : Integer.Sparse Key := [(key33, 6), (key149, -6), (key175, -6), (key185, 6), (key223, -6), (key495, 6)]

def row4609 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

def row4610 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

def row4611 : Integer.Sparse Key := [(key33, -2), (key149, 2), (key175, 2), (key185, -2), (key223, 2), (key495, -2)]

def row4612 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4613 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4614 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4615 : Integer.Sparse Key := [(key1361, 6), (key1373, -6), (key1487, -6), (key1512, 6), (key1722, 6), (key1740, -6)]

def row4616 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4617 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4618 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4619 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4620 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4621 : Integer.Sparse Key := [(key1361, -2), (key1373, 2), (key1487, 2), (key1512, -2), (key1722, -2), (key1740, 2)]

def row4622 : Integer.Sparse Key := [(key1361, -6), (key1373, 6), (key1487, 6), (key1512, -6), (key1722, -6), (key1740, 6)]

def row4623 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4624 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4625 : Integer.Sparse Key := [(key1361, 2), (key1373, -2), (key1487, -2), (key1512, 2), (key1722, 2), (key1740, -2)]

def row4626 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

def row4627 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

def row4628 : Integer.Sparse Key := [(key351, -2), (key354, 2), (key508, 2), (key523, -2), (key668, -2), (key672, 2)]

def row4629 : Integer.Sparse Key := [(key351, 6), (key354, -6), (key508, -6), (key523, 6), (key668, 6), (key672, -6)]

def row4630 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

def row4631 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

def row4632 : Integer.Sparse Key := [(key351, 2), (key354, -2), (key439, -2), (key443, -2), (key458, 4), (key511, 2), (key523, 2), (key543, 2), (key596, -2), (key607, 2), (key668, -2), (key672, -2), (key678, -2)]

def row4633 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

def row4634 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

def row4635 : Integer.Sparse Key := [(key257, 2), (key261, -2), (key272, 2), (key282, -2), (key285, 2), (key295, -2), (key351, -2), (key354, 2), (key439, 4), (key443, -2), (key458, -2), (key470, 2), (key481, 2), (key508, -2), (key511, 2), (key523, -4)]

def row4636 : Integer.Sparse Key := [(key351, -6), (key398, 6), (key458, -6), (key470, -6), (key481, 6), (key508, 6)]

def row4637 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

def row4638 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

def row4639 : Integer.Sparse Key := [(key351, 2), (key398, -2), (key458, 2), (key470, 2), (key481, -2), (key508, -2)]

def row4640 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4641 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4642 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4643 : Integer.Sparse Key := [(key1502, 6), (key1504, -6), (key1734, -6), (key1737, 6), (key1945, 6), (key1947, -6)]

def row4644 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4645 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4646 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4647 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4648 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4649 : Integer.Sparse Key := [(key1502, -2), (key1504, 2), (key1734, 2), (key1737, -2), (key1945, -2), (key1947, 2)]

def row4650 : Integer.Sparse Key := [(key1502, -6), (key1504, 6), (key1734, 6), (key1737, -6), (key1945, -6), (key1947, 6)]

def row4651 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4652 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4653 : Integer.Sparse Key := [(key1502, 2), (key1504, -2), (key1734, -2), (key1737, 2), (key1945, 2), (key1947, -2)]

def row4654 : Integer.Sparse Key := [(key261, -3), (key285, 1), (key295, 2), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

def row4655 : Integer.Sparse Key := [(key257, -1), (key261, -3), (key272, 1), (key282, 1), (key285, 1), (key295, 1), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

def row4656 : Integer.Sparse Key := [(key257, -2), (key261, -2), (key272, 2), (key282, 2), (key354, 2), (key371, -2), (key523, -2), (key543, 2)]

def row4657 : Integer.Sparse Key := [(key261, 6), (key272, -6), (key354, -6), (key371, 6), (key523, 6), (key543, -6)]

def row4658 : Integer.Sparse Key := [(key261, 3), (key285, -1), (key295, -2), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

def row4659 : Integer.Sparse Key := [(key257, 1), (key261, 3), (key272, -1), (key282, -1), (key285, -1), (key295, -1), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

def row4660 : Integer.Sparse Key := [(key257, 2), (key261, 2), (key272, -2), (key282, -2), (key351, 2), (key354, 2), (key371, 2), (key394, -2), (key398, -4), (key470, 2), (key596, -2)]

def row4661 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

def row4662 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

def row4663 : Integer.Sparse Key := [(key261, -2), (key272, 2), (key398, 2), (key470, -2), (key573, -2), (key596, 2)]

def row4664 : Integer.Sparse Key := [(key261, -6), (key272, 6), (key398, 6), (key470, -6), (key573, -6), (key596, 6)]

def row4665 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

def row4666 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

def row4667 : Integer.Sparse Key := [(key261, 2), (key272, -2), (key398, -2), (key470, 2), (key573, 2), (key596, -2)]

def row4668 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4669 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4670 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4671 : Integer.Sparse Key := [(key223, 6), (key226, -6), (key495, -6), (key552, 6), (key620, 6), (key646, -6)]

def row4672 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4673 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4674 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4675 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4676 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4677 : Integer.Sparse Key := [(key223, -2), (key226, 2), (key495, 2), (key552, -2), (key620, -2), (key646, 2)]

def row4678 : Integer.Sparse Key := [(key223, -6), (key226, 6), (key495, 6), (key552, -6), (key620, -6), (key646, 6)]

def row4679 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4680 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4681 : Integer.Sparse Key := [(key223, 2), (key226, -2), (key495, -2), (key552, 2), (key620, 2), (key646, -2)]

def row4682 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4683 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4684 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4685 : Integer.Sparse Key := [(key1366, 6), (key1370, -6), (key1718, -6), (key1747, 6), (key1865, 6), (key1880, -6)]

def row4686 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4687 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4688 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4689 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4690 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4691 : Integer.Sparse Key := [(key1366, -2), (key1370, 2), (key1718, 2), (key1747, -2), (key1865, -2), (key1880, 2)]

def row4692 : Integer.Sparse Key := [(key1366, -6), (key1370, 6), (key1718, 6), (key1747, -6), (key1865, -6), (key1880, 6)]

def row4693 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4694 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4695 : Integer.Sparse Key := [(key1366, 2), (key1370, -2), (key1718, -2), (key1747, 2), (key1865, 2), (key1880, -2)]

def row4696 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4697 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4698 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4699 : Integer.Sparse Key := [(key1276, 6), (key1281, -6), (key1699, -6), (key1753, 6), (key1934, 6), (key1954, -6)]

def row4700 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4701 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4702 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4703 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4704 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4705 : Integer.Sparse Key := [(key1276, -2), (key1281, 2), (key1699, 2), (key1753, -2), (key1934, -2), (key1954, 2)]

def row4706 : Integer.Sparse Key := [(key1276, -6), (key1281, 6), (key1699, 6), (key1753, -6), (key1934, -6), (key1954, 6)]

def row4707 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4708 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4709 : Integer.Sparse Key := [(key1276, 2), (key1281, -2), (key1699, -2), (key1753, 2), (key1934, 2), (key1954, -2)]

def row4710 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4711 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4712 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4713 : Integer.Sparse Key := [(key1276, 6), (key1279, -6), (key1699, -6), (key1752, 6), (key1853, 6), (key1885, -6)]

def row4714 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4715 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4716 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4717 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4718 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4719 : Integer.Sparse Key := [(key1276, -2), (key1279, 2), (key1699, 2), (key1752, -2), (key1853, -2), (key1885, 2)]

def row4720 : Integer.Sparse Key := [(key1276, -6), (key1279, 6), (key1699, 6), (key1752, -6), (key1853, -6), (key1885, 6)]

def row4721 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4722 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4723 : Integer.Sparse Key := [(key1276, 2), (key1279, -2), (key1699, -2), (key1752, 2), (key1853, 2), (key1885, -2)]

def row4724 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4725 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4726 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4727 : Integer.Sparse Key := [(key1365, 6), (key1375, -6), (key1491, -6), (key1514, 6), (key1724, 6), (key1742, -6)]

def row4728 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4729 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4730 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4731 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4732 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4733 : Integer.Sparse Key := [(key1365, -2), (key1375, 2), (key1491, 2), (key1514, -2), (key1724, -2), (key1742, 2)]

def row4734 : Integer.Sparse Key := [(key1365, -6), (key1375, 6), (key1491, 6), (key1514, -6), (key1724, -6), (key1742, 6)]

def row4735 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4736 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4737 : Integer.Sparse Key := [(key1365, 2), (key1375, -2), (key1491, -2), (key1514, 2), (key1724, 2), (key1742, -2)]

def row4738 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4739 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4740 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4741 : Integer.Sparse Key := [(key741, 6), (key742, -6), (key900, -6), (key913, 6), (key951, 6), (key954, -6)]

def row4742 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4743 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4744 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4745 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4746 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4747 : Integer.Sparse Key := [(key741, -2), (key742, 2), (key900, 2), (key913, -2), (key951, -2), (key954, 2)]

def row4748 : Integer.Sparse Key := [(key741, -6), (key742, 6), (key900, 6), (key913, -6), (key951, -6), (key954, 6)]

def row4749 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4750 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4751 : Integer.Sparse Key := [(key741, 2), (key742, -2), (key900, -2), (key913, 2), (key951, 2), (key954, -2)]

def row4752 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4753 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4754 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4755 : Integer.Sparse Key := [(key1280, 6), (key1284, -6), (key1703, -6), (key1757, 6), (key1856, 6), (key1887, -6)]

def row4756 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4757 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4758 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4759 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4760 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4761 : Integer.Sparse Key := [(key1280, -2), (key1284, 2), (key1703, 2), (key1757, -2), (key1856, -2), (key1887, 2)]

def row4762 : Integer.Sparse Key := [(key1280, -6), (key1284, 6), (key1703, 6), (key1757, -6), (key1856, -6), (key1887, 6)]

def row4763 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4764 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4765 : Integer.Sparse Key := [(key1280, 2), (key1284, -2), (key1703, -2), (key1757, 2), (key1856, 2), (key1887, -2)]

def row4766 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4767 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4768 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4769 : Integer.Sparse Key := [(key1488, 6), (key1493, -6), (key1714, -6), (key1725, 6), (key1938, 6), (key1941, -6)]

def row4770 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4771 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4772 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4773 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4774 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4775 : Integer.Sparse Key := [(key1488, -2), (key1493, 2), (key1714, 2), (key1725, -2), (key1938, -2), (key1941, 2)]

def row4776 : Integer.Sparse Key := [(key1488, -6), (key1493, 6), (key1714, 6), (key1725, -6), (key1938, -6), (key1941, 6)]

def row4777 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4778 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4779 : Integer.Sparse Key := [(key1488, 2), (key1493, -2), (key1714, -2), (key1725, 2), (key1938, 2), (key1941, -2)]

def row4780 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4781 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4782 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4783 : Integer.Sparse Key := [(key1362, 6), (key1375, -6), (key1488, -6), (key1514, 6), (key1868, 6), (key1878, -6)]

def row4784 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4785 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4786 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4787 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4788 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4789 : Integer.Sparse Key := [(key1362, -2), (key1375, 2), (key1488, 2), (key1514, -2), (key1868, -2), (key1878, 2)]

def row4790 : Integer.Sparse Key := [(key1362, -6), (key1375, 6), (key1488, 6), (key1514, -6), (key1868, -6), (key1878, 6)]

def row4791 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4792 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4793 : Integer.Sparse Key := [(key1362, 2), (key1375, -2), (key1488, -2), (key1514, 2), (key1868, 2), (key1878, -2)]

def row4794 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4795 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4796 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4797 : Integer.Sparse Key := [(key351, 6), (key353, -6), (key508, -6), (key521, 6), (key628, 6), (key630, -6)]

def row4798 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4799 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4800 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4801 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4802 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4803 : Integer.Sparse Key := [(key351, -2), (key353, 2), (key508, 2), (key521, -2), (key628, -2), (key630, 2)]

def row4804 : Integer.Sparse Key := [(key351, -6), (key353, 6), (key508, 6), (key521, -6), (key628, -6), (key630, 6)]

def row4805 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4806 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4807 : Integer.Sparse Key := [(key351, 2), (key353, -2), (key508, -2), (key521, 2), (key628, 2), (key630, -2)]

def row4808 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4809 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4810 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4811 : Integer.Sparse Key := [(key1488, 6), (key1491, -6), (key1714, -6), (key1724, 6), (key1862, 6), (key1868, -6)]

def row4812 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4813 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4814 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4815 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4816 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4817 : Integer.Sparse Key := [(key1488, -2), (key1491, 2), (key1714, 2), (key1724, -2), (key1862, -2), (key1868, 2)]

def row4818 : Integer.Sparse Key := [(key1488, -6), (key1491, 6), (key1714, 6), (key1724, -6), (key1862, -6), (key1868, 6)]

def row4819 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4820 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4821 : Integer.Sparse Key := [(key1488, 2), (key1491, -2), (key1714, -2), (key1724, 2), (key1862, 2), (key1868, -2)]

def row4822 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

def row4823 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

def row4824 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -2), (key631, -2), (key647, 2)]

def row4825 : Integer.Sparse Key := [(key291, 6), (key294, -6), (key518, -6), (key553, 6), (key631, 6), (key647, -6)]

def row4826 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

def row4827 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

def row4828 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 8), (key631, -4), (key647, -2)]

def row4829 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

def row4830 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

def row4831 : Integer.Sparse Key := [(key291, -2), (key294, 2), (key518, 2), (key553, -8), (key631, 4), (key647, 2)]

def row4832 : Integer.Sparse Key := [(key291, -6), (key294, 6), (key518, 6), (key553, -6), (key631, -6), (key647, 6)]

def row4833 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

def row4834 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

def row4835 : Integer.Sparse Key := [(key291, 2), (key294, -2), (key518, -2), (key553, 2), (key631, 2), (key647, -2)]

def row4836 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4837 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4838 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4839 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4840 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4841 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4842 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

def row4843 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

def row4844 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

def row4845 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

def row4846 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

def row4847 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

def row4848 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

def row4849 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

def row4850 : Integer.Sparse Key := [(key1294, -2), (key1314, 2), (key1389, 2), (key1422, -6), (key1453, 4), (key1544, -2), (key1571, 6), (key1653, -4), (key1786, -4), (key1811, 4)]

def row4851 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

def row4852 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

def row4853 : Integer.Sparse Key := [(key1294, 2), (key1314, -2), (key1389, -2), (key1422, 6), (key1453, -4), (key1544, 2), (key1571, -6), (key1653, 4), (key1786, 4), (key1811, -4)]

def row4854 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

def row4855 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

def row4856 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2618, -2), (key2632, 2), (key2640, 2), (key2644, 2), (key2671, 4), (key2676, 2), (key2706, -2), (key2726, -2), (key2732, -2), (key2786, -2), (key2794, -2), (key2798, -2), (key2809, 2), (key2829, 2), (key2835, 2)]

def row4857 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2621, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

def row4858 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

def row4859 : Integer.Sparse Key := [(key2612, 2), (key2616, 2), (key2618, 2), (key2632, -2), (key2640, -2), (key2644, -2), (key2667, -4), (key2673, -2), (key2702, 2), (key2706, 2), (key2726, 2), (key2732, 2), (key2735, 2), (key2737, 2), (key2809, -2), (key2829, -2), (key2835, -2)]

def row4860 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -2), (key2831, 2), (key2860, -2), (key2870, 2), (key3017, -2), (key3023, -2), (key3026, 2)]

def row4861 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, 2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, 2)]

def row4862 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, 2), (key2667, 2), (key2702, -4), (key2706, -2), (key2728, -2), (key2735, 2), (key2747, 2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, 2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, 2)]

def row4863 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 2), (key2831, -2), (key2893, 2), (key2904, 2), (key2972, -2), (key2983, -2), (key3017, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4864 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 1), (key2831, -2), (key2893, 2), (key2904, 2), (key2948, 1), (key2960, 2), (key2972, -2), (key2983, -2)]

def row4865 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2628, -2), (key2667, -2), (key2702, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, 2), (key2805, -4), (key2829, 1), (key2831, -2), (key2893, 2), (key2904, 2), (key2948, 1), (key2960, 2), (key2972, -2), (key2983, -2)]

def row4866 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

def row4867 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

def row4868 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

def row4869 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

def row4870 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

def row4871 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

def row4872 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

def row4873 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

def row4874 : Integer.Sparse Key := [(key1006, -2), (key1019, 2), (key1033, -4), (key1041, 6), (key1076, -2), (key1111, 4), (key1127, -6), (key1155, 2), (key1193, -4), (key1199, 4)]

def row4875 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

def row4876 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

def row4877 : Integer.Sparse Key := [(key1006, 2), (key1019, -2), (key1033, 4), (key1041, -6), (key1076, 2), (key1111, -4), (key1127, 6), (key1155, -2), (key1193, 4), (key1199, -4)]

def row4878 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

def row4879 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

def row4880 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

def row4881 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

def row4882 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

def row4883 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

def row4884 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

def row4885 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

def row4886 : Integer.Sparse Key := [(key2615, -2), (key2631, 2), (key2670, 2), (key2705, -2), (key2785, -6), (key2793, 4), (key2808, 6), (key2828, -4), (key2859, -4), (key2869, 4)]

def row4887 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

def row4888 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

def row4889 : Integer.Sparse Key := [(key2615, 2), (key2631, -2), (key2670, -2), (key2705, 2), (key2785, 6), (key2793, -4), (key2808, -6), (key2828, 4), (key2859, 4), (key2869, -4)]

def row4890 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

def row4891 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

def row4892 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

def row4893 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

def row4894 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

def row4895 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

def row4896 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

def row4897 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

def row4898 : Integer.Sparse Key := [(key1296, -2), (key1303, 2), (key1316, 2), (key1330, -2), (key1340, -2), (key1346, 2), (key1775, -2), (key1781, 2), (key1788, -2), (key1791, 4), (key1799, -2), (key1813, 2), (key1818, -4), (key1826, 2), (key1840, -2), (key1842, 2)]

def row4899 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

def row4900 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

def row4901 : Integer.Sparse Key := [(key1296, 2), (key1303, -2), (key1316, -2), (key1330, 2), (key1340, 2), (key1346, -2), (key1775, 2), (key1781, -2), (key1788, 2), (key1791, -4), (key1799, 2), (key1813, -2), (key1818, 4), (key1826, -2), (key1840, 2), (key1842, -2)]

def row4902 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

def row4903 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

def row4904 : Integer.Sparse Key := [(key2719, -4), (key2733, -2), (key2756, 4), (key2759, 2), (key2822, 4), (key2836, 2), (key2924, -6), (key3015, -4), (key3018, -2), (key3027, 6)]

def row4905 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

def row4906 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

def row4907 : Integer.Sparse Key := [(key2719, 4), (key2733, 2), (key2756, -4), (key2759, -2), (key2822, -4), (key2836, -2), (key2924, 6), (key3015, 4), (key3018, 2), (key3027, -6)]

def row4908 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3018, -2), (key3027, 2)]

def row4909 : Integer.Sparse Key := [(key2693, -2), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3027, 2), (key3055, -2), (key3117, -2)]

def row4910 : Integer.Sparse Key := [(key2693, -2), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3027, 2), (key3055, -2), (key3117, -2)]

def row4911 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3018, 2), (key3070, -4), (key3074, 4), (key3146, 2), (key3147, -2)]

def row4912 : Integer.Sparse Key := [(key2693, 2), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3055, 2), (key3070, -4), (key3074, 4), (key3117, 2), (key3146, 2), (key3147, -2)]

def row4913 : Integer.Sparse Key := [(key2693, 2), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3055, 2), (key3070, -4), (key3074, 4), (key3117, 2), (key3146, 2), (key3147, -2)]

def row4914 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

def row4915 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

def row4916 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

def row4917 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

def row4918 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

def row4919 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

def row4920 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

def row4921 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

def row4922 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

def row4923 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

def row4924 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

def row4925 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

def row4926 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

def row4927 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

def row4928 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

def row4929 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

def row4930 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

def row4931 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

def row4932 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

def row4933 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

def row4934 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

def row4935 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

def row4936 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

def row4937 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

def row4938 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4939 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4940 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4941 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4942 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4943 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4944 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

def row4945 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

def row4946 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

def row4947 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

def row4948 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

def row4949 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

def row4950 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

def row4951 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

def row4952 : Integer.Sparse Key := [(key2374, -4), (key2380, -2), (key2391, 6), (key2770, 4), (key2775, 2), (key2917, -2), (key2926, -4), (key3006, -6), (key3020, 2), (key3029, 4)]

def row4953 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

def row4954 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

def row4955 : Integer.Sparse Key := [(key2374, -4), (key2380, 6), (key2391, -2), (key2775, -2), (key2847, 4), (key2884, -4), (key2917, 2), (key3006, 2), (key3020, -6), (key3029, 4)]

def row4956 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

def row4957 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

def row4958 : Integer.Sparse Key := [(key2402, -4), (key2408, -2), (key2439, 6), (key2591, 4), (key2596, 2), (key2605, -6), (key2917, 2), (key2926, 4), (key3020, -2), (key3029, -4)]

def row4959 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

def row4960 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

def row4961 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2596, -2), (key2605, 2), (key2847, 4), (key2884, -4), (key2917, -6), (key2926, 4), (key3020, 2)]

def row4962 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

def row4963 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

def row4964 : Integer.Sparse Key := [(key2374, 4), (key2391, 2), (key2468, -4), (key2481, -2), (key2505, 6), (key2596, -6), (key2775, 2), (key2884, 4), (key3006, -2), (key3029, -4)]

def row4965 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

def row4966 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

def row4967 : Integer.Sparse Key := [(key2402, 4), (key2439, 2), (key2468, -4), (key2481, 6), (key2505, -2), (key2596, 2), (key2605, -2), (key2775, -6), (key2884, 4), (key2926, -4)]

def row4968 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row4969 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row4970 : Integer.Sparse Key := [(key2591, -4), (key2594, -2), (key2601, 6), (key2770, 4), (key2773, 2), (key2890, -2), (key2911, -4), (key2932, -6), (key2969, 2), (key2990, 4)]

def row4971 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

def row4972 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

def row4973 : Integer.Sparse Key := [(key2591, -4), (key2594, 6), (key2601, -2), (key2773, -2), (key2847, 4), (key2881, -4), (key2890, 2), (key2932, 2), (key2969, -6), (key2990, 4)]

def row4974 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

def row4975 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

def row4976 : Integer.Sparse Key := [(key2591, 4), (key2594, 2), (key2601, -6), (key2770, -4), (key2773, -2), (key2890, 2), (key2911, 4), (key2932, 6), (key2969, -2), (key2990, -4)]

def row4977 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

def row4978 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

def row4979 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2770, -4), (key2773, 6), (key2847, 4), (key2881, -4), (key2890, -6), (key2911, 4), (key2932, -2), (key2969, 2)]

def row4980 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

def row4981 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

def row4982 : Integer.Sparse Key := [(key2591, 4), (key2594, -6), (key2601, 2), (key2773, 2), (key2847, -4), (key2881, 4), (key2890, -2), (key2932, -2), (key2969, 6), (key2990, -4)]

def row4983 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

def row4984 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

def row4985 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -6), (key2847, -4), (key2881, 4), (key2890, 6), (key2911, -4), (key2932, 2), (key2969, -2)]

def row4986 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

def row4987 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

def row4988 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2632, 2), (key2640, 2), (key2642, 2), (key2671, 4), (key2674, 2), (key2706, -2), (key2726, -2), (key2729, -2), (key2786, -2), (key2794, -2), (key2796, -2), (key2809, 2), (key2829, 2), (key2832, 2)]

def row4989 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

def row4990 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

def row4991 : Integer.Sparse Key := [(key2616, 2), (key2632, -4), (key2640, 2), (key2649, -2), (key2654, 2), (key2671, -2), (key2706, 4), (key2726, -2), (key2738, 2), (key2748, -2), (key2786, 2), (key2809, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4992 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

def row4993 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

def row4994 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2632, -2), (key2640, -2), (key2642, -2), (key2671, -4), (key2674, -2), (key2706, 2), (key2726, 2), (key2729, 2), (key2786, 2), (key2794, 2), (key2796, 2), (key2809, -2), (key2829, -2), (key2832, -2)]

def row4995 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row4996 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row4997 : Integer.Sparse Key := [(key2616, -2), (key2632, 2), (key2671, 2), (key2706, -2), (key2786, -4), (key2794, 2), (key2809, 4), (key2829, -2), (key2860, -2), (key2870, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row4998 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

def row4999 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

def row5000 : Integer.Sparse Key := [(key2616, -2), (key2632, 4), (key2640, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2706, -4), (key2726, 2), (key2738, -2), (key2748, 2), (key2786, -2), (key2809, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2)]

def row5001 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5002 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5003 : Integer.Sparse Key := [(key2616, 2), (key2632, -2), (key2671, -2), (key2706, 2), (key2786, 4), (key2794, -2), (key2809, -4), (key2829, 2), (key2860, 2), (key2870, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5004 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

def row5005 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

def row5006 : Integer.Sparse Key := [(key2078, -4), (key2082, -2), (key2087, 6), (key2175, 4), (key2179, 2), (key2189, -6), (key2281, -2), (key2289, 2), (key2330, -4), (key2333, 4)]

def row5007 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

def row5008 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

def row5009 : Integer.Sparse Key := [(key2078, -4), (key2082, 6), (key2087, -2), (key2179, -2), (key2189, 2), (key2275, 4), (key2281, 2), (key2289, -6), (key2328, -4), (key2333, 4)]

def row5010 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

def row5011 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

def row5012 : Integer.Sparse Key := [(key2078, 4), (key2082, 2), (key2087, -6), (key2175, -4), (key2179, -2), (key2189, 6), (key2281, 2), (key2289, -2), (key2330, 4), (key2333, -4)]

def row5013 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

def row5014 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

def row5015 : Integer.Sparse Key := [(key2082, -2), (key2087, 2), (key2175, -4), (key2179, 6), (key2189, -2), (key2275, 4), (key2281, -6), (key2289, 2), (key2328, -4), (key2330, 4)]

def row5016 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

def row5017 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

def row5018 : Integer.Sparse Key := [(key2078, 4), (key2082, -6), (key2087, 2), (key2179, 2), (key2189, -2), (key2275, -4), (key2281, -2), (key2289, 6), (key2328, 4), (key2333, -4)]

def row5019 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

def row5020 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

def row5021 : Integer.Sparse Key := [(key2082, 2), (key2087, -2), (key2175, 4), (key2179, -6), (key2189, 2), (key2275, -4), (key2281, 6), (key2289, -2), (key2328, 4), (key2330, -4)]

def row5022 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

def row5023 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

def row5024 : Integer.Sparse Key := [(key2379, -2), (key2382, -4), (key2393, 4), (key2395, 2), (key2771, 2), (key2774, 4), (key2891, -2), (key2912, -2), (key2914, -2), (key2933, -4), (key2934, -2), (key2970, 2), (key2991, 2), (key2993, 2)]

def row5025 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row5026 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row5027 : Integer.Sparse Key := [(key2379, -2), (key2382, 4), (key2393, -4), (key2395, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, 4), (key2914, -2), (key2933, 2), (key2970, -4), (key2991, 2), (key2996, -2), (key3003, 2)]

def row5028 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

def row5029 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

def row5030 : Integer.Sparse Key := [(key2407, -2), (key2410, -4), (key2441, 4), (key2445, 2), (key2592, 2), (key2595, 4), (key2602, -4), (key2603, -2), (key2891, 2), (key2912, 2), (key2914, 2), (key2970, -2), (key2991, -2), (key2993, -2)]

def row5031 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

def row5032 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

def row5033 : Integer.Sparse Key := [(key2407, -2), (key2410, 4), (key2441, -4), (key2445, 2), (key2595, -2), (key2602, 2), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, 2), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, 2)]

def row5034 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

def row5035 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

def row5036 : Integer.Sparse Key := [(key2379, 2), (key2393, 4), (key2473, -2), (key2483, -4), (key2507, 4), (key2526, 2), (key2595, -4), (key2603, -2), (key2774, 2), (key2882, 2), (key2914, 2), (key2933, -2), (key2991, -2), (key3003, -2)]

def row5037 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

def row5038 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

def row5039 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, -2), (key2483, 4), (key2507, -4), (key2526, 2), (key2595, 2), (key2602, -2), (key2774, -4), (key2882, 2), (key2912, -2), (key2934, -2), (key2993, 2), (key3003, -2)]

def row5040 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row5041 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row5042 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2732, -2), (key2753, 2), (key2758, 4), (key2809, 2), (key2829, 2), (key2835, 2), (key2920, -2), (key2923, -2), (key2927, -2), (key3012, -2), (key3017, -4), (key3023, 2), (key3026, 2), (key3030, 2)]

def row5043 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

def row5044 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

def row5045 : Integer.Sparse Key := [(key2671, -2), (key2676, 2), (key2726, -2), (key2732, 4), (key2758, -2), (key2786, 2), (key2798, -2), (key2835, -2), (key2870, 2), (key2885, -2), (key2923, 2), (key3008, -2), (key3010, 2), (key3017, 2), (key3026, -4), (key3030, 2)]

def row5046 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

def row5047 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

def row5048 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2732, 2), (key2753, -2), (key2758, -4), (key2809, -2), (key2829, -2), (key2835, -2), (key2920, 2), (key2923, 2), (key2927, 2), (key3012, 2), (key3017, 4), (key3023, -2), (key3026, -2), (key3030, -2)]

def row5049 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -2), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key3017, -2), (key3026, 2)]

def row5050 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -1), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key2948, -1), (key2960, -2), (key3026, 2)]

def row5051 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2732, -2), (key2758, 2), (key2829, -1), (key2835, 4), (key2870, 2), (key2885, -2), (key2923, -4), (key2927, 2), (key2948, -1), (key2960, -2), (key3026, 2)]

def row5052 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

def row5053 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

def row5054 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -4), (key2758, 2), (key2798, 2), (key2835, 2), (key2885, 2), (key2972, -2), (key2976, -2), (key2983, 4), (key3010, -2), (key3017, -2), (key3030, -2)]

def row5055 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 2), (key2835, -4), (key2885, 2), (key2927, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3017, 2)]

def row5056 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 1), (key2835, -4), (key2885, 2), (key2927, -2), (key2948, 1), (key2960, 2), (key2972, -2), (key2976, 4), (key2983, -2)]

def row5057 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, -2), (key2641, 2), (key2644, 2), (key2660, -2), (key2732, 2), (key2758, -2), (key2829, 1), (key2835, -4), (key2885, 2), (key2927, -2), (key2948, 1), (key2960, 2), (key2972, -2), (key2976, 4), (key2983, -2)]

def row5058 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

def row5059 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

def row5060 : Integer.Sparse Key := [(key2616, -4), (key2619, -2), (key2649, 2), (key2654, 4), (key2671, 4), (key2674, 2), (key2738, -2), (key2748, -4), (key2939, -2), (key2944, -4), (key2951, 2), (key2961, 4)]

def row5061 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

def row5062 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

def row5063 : Integer.Sparse Key := [(key2619, 2), (key2632, -4), (key2642, 4), (key2649, -2), (key2674, -2), (key2706, 4), (key2729, -4), (key2738, 2), (key2939, 2), (key2951, -2), (key2977, -4), (key2984, 4)]

def row5064 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

def row5065 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

def row5066 : Integer.Sparse Key := [(key2616, 4), (key2619, 2), (key2649, -2), (key2654, -4), (key2671, -4), (key2674, -2), (key2738, 2), (key2748, 4), (key2939, 2), (key2944, 4), (key2951, -2), (key2961, -4)]

def row5067 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

def row5068 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

def row5069 : Integer.Sparse Key := [(key2619, -2), (key2649, 2), (key2674, 2), (key2738, -2), (key2786, -4), (key2796, 4), (key2809, 4), (key2832, -4), (key2898, -4), (key2905, 4), (key2939, -2), (key2951, 2)]

def row5070 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

def row5071 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

def row5072 : Integer.Sparse Key := [(key2619, -2), (key2632, 4), (key2642, -4), (key2649, 2), (key2674, 2), (key2706, -4), (key2729, 4), (key2738, -2), (key2939, -2), (key2951, 2), (key2977, 4), (key2984, -4)]

def row5073 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

def row5074 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

def row5075 : Integer.Sparse Key := [(key2619, 2), (key2649, -2), (key2674, -2), (key2738, 2), (key2786, 4), (key2796, -4), (key2809, -4), (key2832, 4), (key2898, 4), (key2905, -4), (key2939, 2), (key2951, -2)]

def row5076 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

def row5077 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

def row5078 : Integer.Sparse Key := [(key1546, -2), (key1559, 2), (key1573, 2), (key1596, -2), (key1659, -2), (key1667, 2), (key1772, -2), (key1774, -2), (key1780, 4), (key1788, 2), (key1790, 2), (key1798, -4), (key1817, -2), (key1825, 2), (key1841, -2), (key1844, 2)]

def row5079 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row5080 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row5081 : Integer.Sparse Key := [(key1391, -2), (key1397, 2), (key1424, 2), (key1447, -2), (key1457, -2), (key1466, 2), (key1772, -2), (key1774, 4), (key1780, -2), (key1790, -2), (key1798, 2), (key1813, 2), (key1817, 2), (key1825, -4), (key1839, -2), (key1844, 2)]

def row5082 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

def row5083 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

def row5084 : Integer.Sparse Key := [(key1546, 2), (key1559, -2), (key1573, -2), (key1596, 2), (key1659, 2), (key1667, -2), (key1772, 2), (key1774, 2), (key1780, -4), (key1788, -2), (key1790, -2), (key1798, 4), (key1817, 2), (key1825, -2), (key1841, 2), (key1844, -2)]

def row5085 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

def row5086 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

def row5087 : Integer.Sparse Key := [(key1296, -2), (key1302, 2), (key1316, 2), (key1329, -2), (key1339, -2), (key1345, 2), (key1774, -2), (key1780, 2), (key1788, -2), (key1790, 4), (key1798, -2), (key1813, 2), (key1817, -4), (key1825, 2), (key1839, -2), (key1841, 2)]

def row5088 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row5089 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row5090 : Integer.Sparse Key := [(key1391, 2), (key1397, -2), (key1424, -2), (key1447, 2), (key1457, 2), (key1466, -2), (key1772, 2), (key1774, -4), (key1780, 2), (key1790, 2), (key1798, -2), (key1813, -2), (key1817, -2), (key1825, 4), (key1839, 2), (key1844, -2)]

def row5091 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

def row5092 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

def row5093 : Integer.Sparse Key := [(key1296, 2), (key1302, -2), (key1316, -2), (key1329, 2), (key1339, 2), (key1345, -2), (key1774, 2), (key1780, -2), (key1788, 2), (key1790, -4), (key1798, 2), (key1813, -2), (key1817, 4), (key1825, -2), (key1839, 2), (key1841, -2)]

def row5094 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

def row5095 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

def row5096 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2738, 2), (key2748, 4), (key2809, 2), (key2829, 2), (key2832, 2), (key2898, -2), (key2905, -2), (key2913, -2), (key2951, -2), (key2961, -4), (key2977, 2), (key2984, 2), (key2992, 2)]

def row5097 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

def row5098 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

def row5099 : Integer.Sparse Key := [(key2671, -2), (key2674, 2), (key2726, -2), (key2729, 4), (key2748, -2), (key2786, 2), (key2796, -2), (key2832, -2), (key2870, 2), (key2883, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2961, 2), (key2984, -4), (key2992, 2)]

def row5100 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

def row5101 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

def row5102 : Integer.Sparse Key := [(key2706, 2), (key2726, 2), (key2729, 2), (key2738, -2), (key2748, -4), (key2809, -2), (key2829, -2), (key2832, -2), (key2898, 2), (key2905, 2), (key2913, 2), (key2951, 2), (key2961, 4), (key2977, -2), (key2984, -2), (key2992, -2)]

def row5103 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

def row5104 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

def row5105 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, 2), (key2642, -2), (key2649, -2), (key2654, 2), (key2729, -2), (key2748, 2), (key2829, -2), (key2832, 4), (key2870, 2), (key2883, -2), (key2905, -4), (key2913, 2), (key2961, -2), (key2984, 2)]

def row5106 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

def row5107 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

def row5108 : Integer.Sparse Key := [(key2671, 2), (key2674, -2), (key2726, 2), (key2729, -4), (key2748, 2), (key2786, -2), (key2796, 2), (key2832, 2), (key2870, -2), (key2883, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2961, -2), (key2984, 4), (key2992, -2)]

def row5109 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

def row5110 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

def row5111 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, -2), (key2642, 2), (key2649, 2), (key2654, -2), (key2729, 2), (key2748, -2), (key2829, 2), (key2832, -4), (key2870, -2), (key2883, 2), (key2905, 4), (key2913, -2), (key2961, 2), (key2984, -2)]

def row5112 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

def row5113 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

def row5114 : Integer.Sparse Key := [(key1366, -4), (key1370, -2), (key1379, 6), (key1492, 4), (key1496, 2), (key1519, -6), (key1728, -2), (key1747, 2), (key1870, -4), (key1880, 4)]

def row5115 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

def row5116 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

def row5117 : Integer.Sparse Key := [(key1366, -4), (key1370, 6), (key1379, -2), (key1496, -2), (key1519, 2), (key1718, 4), (key1728, 2), (key1747, -6), (key1865, -4), (key1880, 4)]

def row5118 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

def row5119 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5120 : Integer.Sparse Key := [(key1366, 4), (key1370, 2), (key1379, -6), (key1492, -4), (key1496, -2), (key1519, 6), (key1728, 2), (key1747, -2), (key1870, 4), (key1880, -4)]

def row5121 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

def row5122 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

def row5123 : Integer.Sparse Key := [(key1370, -2), (key1379, 2), (key1492, -4), (key1496, 6), (key1519, -2), (key1718, 4), (key1728, -6), (key1747, 2), (key1865, -4), (key1870, 4)]

def row5124 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

def row5125 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

def row5126 : Integer.Sparse Key := [(key1366, 4), (key1370, -6), (key1379, 2), (key1496, 2), (key1519, -2), (key1718, -4), (key1728, -2), (key1747, 6), (key1865, 4), (key1880, -4)]

def row5127 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

def row5128 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

def row5129 : Integer.Sparse Key := [(key1370, 2), (key1379, -2), (key1492, 4), (key1496, -6), (key1519, 2), (key1718, -4), (key1728, 6), (key1747, -2), (key1865, 4), (key1870, -4)]

def row5130 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

def row5131 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

def row5132 : Integer.Sparse Key := [(key2617, -2), (key2620, -4), (key2633, 2), (key2643, 4), (key2672, 2), (key2675, 4), (key2707, -2), (key2730, -4), (key2787, -2), (key2797, -4), (key2810, 2), (key2833, 4)]

def row5133 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

def row5134 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

def row5135 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2643, -4), (key2655, 4), (key2672, -2), (key2707, 2), (key2739, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2899, -4), (key2906, 4)]

def row5136 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

def row5137 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

def row5138 : Integer.Sparse Key := [(key2617, 2), (key2620, 4), (key2633, -2), (key2643, -4), (key2672, -2), (key2675, -4), (key2707, 4), (key2730, 4), (key2739, 4), (key2810, -2), (key2833, -4)]

def row5139 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

def row5140 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

def row5141 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2672, 2), (key2707, -4), (key2730, -4), (key2749, 4), (key2810, 2), (key2833, 4), (key2962, -4), (key2978, -4), (key2985, 4)]

def row5142 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

def row5143 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

def row5144 : Integer.Sparse Key := [(key2617, -2), (key2633, 2), (key2643, 4), (key2655, -4), (key2672, 2), (key2707, -2), (key2749, 4), (key2787, -2), (key2797, -4), (key2810, 2), (key2899, 4), (key2978, -4)]

def row5145 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

def row5146 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

def row5147 : Integer.Sparse Key := [(key2617, 2), (key2633, -2), (key2672, -2), (key2707, 2), (key2730, 4), (key2749, -4), (key2787, 2), (key2810, -2), (key2833, -4), (key2906, 4), (key2962, 4), (key2985, -4)]

end MUB6.Certificate.GramRows

end OAI
end


