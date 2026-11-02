-- Prove2me | Definitions.Def_OAIQ106D106
-- name    : OAIQ106D106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:03:50.837899+00:00
-- url     : https://prove2.me/theorems/e5a35dd8-b00a-450f-8992-6c11dbca4baf
-- title:
--   Definitions bundle OAIQ106D106 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 117 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow6442`, `OAI.MUB6.Certificate.GramRows.rawRow6443`, `OAI.MUB6.Certificate.GramRows.rawRow6444`, `OAI.MUB6.Certificate.GramRows.rawRow6445`, `OAI.MUB6.Certificate.GramRows.rawRow6446`, `OAI.MUB6.Certificate.GramRows.rawRow6447`, `OAI.MUB6.Certificate.GramRows.rawRow6448`, `OAI.MUB6.Certificate.GramRows.rawRow6449`, `OAI.MUB6.Certificate.GramRows.rawRow6450`, `OAI.MUB6.Certificate.GramRows.rawRow6451`, `OAI.MUB6.Certificate.GramRows.rawRow6452`, `OAI.MUB6.Certificate.GramRows.rawRow6453`, `OAI.MUB6.Certificate.GramRows.rawRow6454`, `OAI.MUB6.Certificate.GramRows.rawRow6455`, `OAI.MUB6.Certificate.GramRows.rawRow6456`, `OAI.MUB6.Certificate.GramRows.rawRow6457`, `OAI.MUB6.Certificate.GramRows.rawRow6458`, `OAI.MUB6.Certificate.GramRows.rawRow6459`, `OAI.MUB6.Certificate.GramRows.rawRow6460`, `OAI.MUB6.Certificate.GramRows.rawRow6461`, `OAI.MUB6.Certificate.GramRows.rawRow6462`, `OAI.MUB6.Certificate.GramRows.rawRow6463`, `OAI.MUB6.Certificate.GramRows.rawRow6464`, `OAI.MUB6.Certificate.GramRows.rawRow6465`, `OAI.MUB6.Certificate.GramRows.rawRow6466`, `OAI.MUB6.Certificate.GramRows.rawRow6467`, `OAI.MUB6.Certificate.GramRows.rawRow6468`, `OAI.MUB6.Certificate.GramRows.rawRow6469`, `OAI.MUB6.Certificate.GramRows.rawRow6470`, `OAI.MUB6.Certificate.GramRows.rawRow6471`, `OAI.MUB6.Certificate.GramRows.rawRow6472`, `OAI.MUB6.Certificate.GramRows.rawRow6473`, `OAI.MUB6.Certificate.GramRows.rawRow6474`, `OAI.MUB6.Certificate.GramRows.rawRow6475`, `OAI.MUB6.Certificate.GramRows.rawRow6476`, `OAI.MUB6.Certificate.GramRows.rawRow6477`, `OAI.MUB6.Certificate.GramRows.rawRow6478`, `OAI.MUB6.Certificate.GramRows.rawRow6479`, `OAI.MUB6.Certificate.GramRows.rawRow6480`, `OAI.MUB6.Certificate.GramRows.rawRow6481` and 77 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block0.lean), [`MutuallyUnbiased_GramRows_Block17`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block17.lean), [`MutuallyUnbiased_GramRows_Block18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block18.lean), [`MutuallyUnbiased_GramRows_Block21`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block21.lean), [`MutuallyUnbiased_GramRows_Block74`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block74.lean), [`MutuallyUnbiased_GramRows_Block75`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block75.lean), [`MutuallyUnbiased_MixedData_Source0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedData/Source0.lean), [`MutuallyUnbiased_MixedSemantics_Values15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Values15.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D186`.
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

def rawRow65 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1596, 2), (key1546, 1), (key1546, 1), (key1667, -1), (key1667, -1), (key1559, -2), (key1659, 1), (key1659, 1), (key1424, 1), (key1424, 1), (key1447, -2), (key1316, -1), (key1316, -1), (key1825, 1), (key1825, 1), (key1329, 2), (key1817, -1), (key1817, -1), (key1391, -1), (key1391, -1), (key1466, 1), (key1466, 1), (key1296, 1), (key1296, 1), (key1798, -1), (key1798, -1), (key1345, -1), (key1345, -1), (key1780, 1), (key1780, 1), (key1397, 2), (key1457, -1), (key1457, -1), (key1302, -2), (key1790, 1), (key1790, 1), (key1339, 1), (key1339, 1), (key1774, -1), (key1774, -1)]

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

def rawRow664 : Integer.Sparse Key := [(key1571, -2), (key1571, -2), (key1571, -2), (key1786, 1), (key1786, 1), (key1786, 1), (key1786, 1), (key1786, 1), (key1786, 1), (key1422, 2), (key1422, 2), (key1422, 2), (key1811, -1), (key1811, -1), (key1811, -1), (key1811, -1), (key1811, -1), (key1811, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1453, -1), (key1653, 1), (key1653, 1), (key1653, 1), (key1653, 1), (key1653, 1), (key1653, 1)]

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

def rawRow689 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2737, 1), (key2735, 1), (key2747, 1), (key2735, 1), (key2747, 1), (key2737, 1), (key2805, 2), (key2831, 2), (key2805, 2), (key2897, -1), (key2893, -1), (key2904, -1), (key2893, -1), (key2904, -1), (key2897, -1), (key2950, -1), (key2948, -1), (key2960, -1), (key2948, -1), (key2960, -1), (key2950, -1), (key2976, 1), (key2972, 1), (key2983, 1), (key2972, 1), (key2983, 1), (key2976, 1)]

def rawRow690 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, 1), (key2747, 1), (key2737, 1), (key2737, 1), (key2735, 1), (key2735, 1), (key2831, 2), (key2805, 2), (key2805, 2), (key2904, -1), (key2904, -1), (key2897, -1), (key2897, -1), (key2893, -1), (key2893, -1), (key2960, -1), (key2960, -1), (key2950, -1), (key2950, -1), (key2948, -1), (key2948, -1), (key2983, 1), (key2983, 1), (key2976, 1), (key2976, 1), (key2972, 1), (key2972, 1)]

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

def rawRow795 : Integer.Sparse Key := [(key31, -6), (key20, 2), (key20, 2), (key20, 2), (key70, 6), (key45, -2), (key45, -2), (key45, -2), (key133, -2), (key133, -2), (key133, -2), (key111, 2), (key111, 2), (key111, 2)]

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

def rawRow6442 : Integer.Sparse Key := [(key2807, 1), (key2801, 1), (key2827, -2), (key2614, 1), (key2608, 1), (key2827, -2), (key2801, -2), (key3016, 1), (key3011, 1), (key2614, -2), (key2827, 1), (key2807, 1), (key2704, -1), (key2698, -1), (key3022, 1), (key3021, 1), (key2630, -1), (key2624, -1), (key2868, 1), (key2851, 1), (key2724, 1), (key2698, 1), (key3025, -1), (key3022, -1), (key2638, 1), (key2630, 1), (key2868, -1), (key2858, -1), (key2752, 2), (key2919, -1), (key2918, -1), (key2657, 2), (key2922, -1), (key2918, -1), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, 2), (key2919, 2)]

def rawRow6443 : Integer.Sparse Key := [(key2801, 1), (key2827, 1), (key2807, -2), (key2801, 1), (key2827, 1), (key2608, -2), (key3016, -2), (key2614, 1), (key2827, 1), (key2807, -2), (key2614, 1), (key2827, 1), (key2851, -1), (key3021, -1), (key2704, 1), (key2858, 1), (key2851, -1), (key3021, -1), (key2624, 1), (key3025, 1), (key2624, 1), (key3025, 1), (key2638, -1), (key2724, -1), (key2704, 1), (key2858, 1), (key2638, -1), (key2724, -1), (key2918, 2), (key2752, -1), (key2919, -1), (key2918, 2), (key2657, -1), (key2922, -1), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, 2), (key2757, 2)]

def rawRow6444 : Integer.Sparse Key := [(key2827, 1), (key2801, 1), (key2807, -2), (key2827, 1), (key2801, 1), (key3016, -2), (key2608, -2), (key2827, 1), (key2614, 1), (key2807, -2), (key2827, 1), (key2614, 1), (key3021, -1), (key2851, -1), (key2858, 1), (key2704, 1), (key3021, -1), (key2851, -1), (key3025, 1), (key2624, 1), (key3025, 1), (key2624, 1), (key2724, -1), (key2638, -1), (key2858, 1), (key2704, 1), (key2724, -1), (key2638, -1), (key2918, 2), (key2919, -1), (key2752, -1), (key2918, 2), (key2922, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, 2), (key2659, 2)]

def rawRow6445 : Integer.Sparse Key := [(key2807, 1), (key2827, 1), (key2801, -2), (key3011, 1), (key3016, 1), (key2614, -2), (key2827, -2), (key2608, 1), (key2801, 1), (key2827, -2), (key2614, 1), (key2807, 1), (key2858, -1), (key3022, -1), (key2698, 1), (key2851, 1), (key2868, -1), (key3025, -1), (key2630, 1), (key3021, 1), (key2638, 1), (key3022, 1), (key2624, -1), (key2698, -1), (key2724, 1), (key2868, 1), (key2630, -1), (key2704, -1), (key2919, 2), (key2752, -1), (key2918, -1), (key2922, 2), (key2657, -1), (key2918, -1), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, 2), (key2752, 2)]

def rawRow6446 : Integer.Sparse Key := [(key2827, 1), (key2807, 1), (key2801, -2), (key3016, 1), (key3011, 1), (key2827, -2), (key2614, -2), (key2801, 1), (key2608, 1), (key2827, -2), (key2807, 1), (key2614, 1), (key3022, -1), (key2858, -1), (key2851, 1), (key2698, 1), (key3025, -1), (key2868, -1), (key3021, 1), (key2630, 1), (key3022, 1), (key2638, 1), (key2698, -1), (key2624, -1), (key2868, 1), (key2724, 1), (key2704, -1), (key2630, -1), (key2919, 2), (key2918, -1), (key2752, -1), (key2922, 2), (key2918, -1), (key2657, -1), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2657, 2)]

def rawRow6447 : Integer.Sparse Key := [(key3011, 1), (key3011, 1), (key3016, -2), (key2614, 1), (key2614, 1), (key2807, -2), (key2807, -2), (key2827, 1), (key2827, 1), (key2608, -2), (key2801, 1), (key2801, 1), (key2724, -1), (key2724, -1), (key3025, 1), (key3025, 1), (key2638, -1), (key2638, -1), (key2858, 1), (key2858, 1), (key2704, 1), (key2704, 1), (key3021, -1), (key3021, -1), (key2624, 1), (key2624, 1), (key2851, -1), (key2851, -1), (key2757, 2), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, -1), (key2919, -1), (key2657, -1), (key2657, -1), (key2752, -1), (key2752, -1), (key2918, 2), (key2918, 2)]

def rawRow6448 : Integer.Sparse Key := [(key3011, 1), (key3016, 1), (key3011, -2), (key2807, 1), (key2827, 1), (key2614, -2), (key2827, -2), (key2614, 1), (key2807, 1), (key2801, -2), (key2608, 1), (key2801, 1), (key2868, -1), (key3025, -1), (key2724, 1), (key2868, 1), (key2858, -1), (key3022, -1), (key2638, 1), (key3022, 1), (key2630, 1), (key3021, 1), (key2630, -1), (key2704, -1), (key2698, 1), (key2851, 1), (key2624, -1), (key2698, -1), (key2922, 2), (key2757, -1), (key2922, -1), (key2919, 2), (key2659, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2657, -1), (key2918, -1), (key2657, 2), (key2752, 2)]

def rawRow6449 : Integer.Sparse Key := [(key3016, 1), (key3011, 1), (key3011, -2), (key2827, 1), (key2807, 1), (key2827, -2), (key2614, -2), (key2807, 1), (key2614, 1), (key2801, -2), (key2801, 1), (key2608, 1), (key3025, -1), (key2868, -1), (key2868, 1), (key2724, 1), (key3022, -1), (key2858, -1), (key3022, 1), (key2638, 1), (key3021, 1), (key2630, 1), (key2704, -1), (key2630, -1), (key2851, 1), (key2698, 1), (key2698, -1), (key2624, -1), (key2922, 2), (key2922, -1), (key2757, -1), (key2919, 2), (key2919, -1), (key2659, -1), (key2918, -1), (key2752, -1), (key2918, -1), (key2657, -1), (key2752, 2), (key2657, 2)]

def rawRow6450 : Integer.Sparse Key := [(key2624, 1), (key2630, 1), (key2638, -2), (key2698, 1), (key2704, 1), (key2851, -2), (key3021, -2), (key2858, 1), (key3022, 1), (key2724, -2), (key2868, 1), (key3025, 1), (key2608, -1), (key2614, -1), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, -1), (key2698, 1), (key2724, 1), (key2801, 1), (key2827, 1), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3022, -1), (key3025, -1), (key2614, 2), (key2630, -1), (key2638, -1), (key2669, 2), (key2704, -1), (key2724, -1), (key2784, -1), (key2792, -1), (key2807, -1), (key2827, -1), (key2858, 2), (key2868, 2)]

def rawRow6451 : Integer.Sparse Key := [(key2630, 1), (key2624, 1), (key2638, -2), (key2704, 1), (key2698, 1), (key3021, -2), (key2851, -2), (key3022, 1), (key2858, 1), (key2724, -2), (key3025, 1), (key2868, 1), (key2614, -1), (key2608, -1), (key2659, 1), (key2657, 1), (key2669, -1), (key2663, -1), (key2724, 1), (key2698, 1), (key2827, 1), (key2801, 1), (key2922, -1), (key2919, -1), (key3009, 1), (key3007, 1), (key3025, -1), (key3022, -1), (key2614, 2), (key2638, -1), (key2630, -1), (key2669, 2), (key2724, -1), (key2704, -1), (key2792, -1), (key2784, -1), (key2827, -1), (key2807, -1), (key2868, 2), (key2858, 2)]

def rawRow6452 : Integer.Sparse Key := [(key2630, 1), (key2638, 1), (key2624, -2), (key3021, 1), (key3022, 1), (key2704, -2), (key2858, -2), (key2698, 1), (key2851, 1), (key3025, -2), (key2724, 1), (key2868, 1), (key2657, -1), (key2659, -1), (key2608, 1), (key2624, 1), (key2724, -1), (key2757, -1), (key2669, 1), (key2752, 1), (key2792, 1), (key2919, 1), (key2778, -1), (key2801, -1), (key3016, 1), (key3025, 1), (key3007, -1), (key3011, -1), (key2638, 2), (key2614, -1), (key2630, -1), (key2724, 2), (key2669, -1), (key2704, -1), (key2827, -1), (key2868, -1), (key2792, -1), (key2858, -1), (key2784, 2), (key2807, 2)]

def rawRow6453 : Integer.Sparse Key := [(key2638, 1), (key2630, 1), (key2624, -2), (key3022, 1), (key3021, 1), (key2858, -2), (key2704, -2), (key2851, 1), (key2698, 1), (key3025, -2), (key2868, 1), (key2724, 1), (key2659, -1), (key2657, -1), (key2624, 1), (key2608, 1), (key2757, -1), (key2724, -1), (key2752, 1), (key2669, 1), (key2919, 1), (key2792, 1), (key2801, -1), (key2778, -1), (key3025, 1), (key3016, 1), (key3011, -1), (key3007, -1), (key2638, 2), (key2630, -1), (key2614, -1), (key2724, 2), (key2704, -1), (key2669, -1), (key2868, -1), (key2827, -1), (key2858, -1), (key2792, -1), (key2807, 2), (key2784, 2)]

def rawRow6454 : Integer.Sparse Key := [(key2698, 1), (key2704, 1), (key2724, -2), (key2624, 1), (key2630, 1), (key2851, -2), (key3021, -2), (key2868, 1), (key3025, 1), (key2638, -2), (key2858, 1), (key3022, 1), (key2663, -1), (key2669, -1), (key2724, 1), (key2757, 1), (key2608, -1), (key2614, -1), (key2801, 1), (key2827, 1), (key2698, 1), (key2724, 1), (key3022, -1), (key3025, -1), (key2657, 1), (key2659, 1), (key2919, -1), (key2922, -1), (key2669, 2), (key2784, -1), (key2792, -1), (key2614, 2), (key2807, -1), (key2827, -1), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, 2), (key2868, 2)]

def rawRow6455 : Integer.Sparse Key := [(key2704, 1), (key2698, 1), (key2724, -2), (key2630, 1), (key2624, 1), (key3021, -2), (key2851, -2), (key3025, 1), (key2868, 1), (key2638, -2), (key3022, 1), (key2858, 1), (key2669, -1), (key2663, -1), (key2757, 1), (key2724, 1), (key2614, -1), (key2608, -1), (key2827, 1), (key2801, 1), (key2724, 1), (key2698, 1), (key3025, -1), (key3022, -1), (key2659, 1), (key2657, 1), (key2922, -1), (key2919, -1), (key2669, 2), (key2792, -1), (key2784, -1), (key2614, 2), (key2827, -1), (key2807, -1), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, 2), (key2858, 2)]

def rawRow6456 : Integer.Sparse Key := [(key2698, 1), (key2724, 1), (key2704, -2), (key2851, 1), (key2868, 1), (key2624, -2), (key3025, -2), (key2630, 1), (key3021, 1), (key2858, -2), (key2638, 1), (key3022, 1), (key2698, -1), (key2724, -1), (key2669, 1), (key2752, 1), (key2801, -1), (key2827, -1), (key2608, 1), (key3016, 1), (key2624, 1), (key3025, 1), (key2638, -1), (key2724, -1), (key2752, 1), (key2919, 1), (key2659, -1), (key2757, -1), (key2784, 2), (key2669, -1), (key2792, -1), (key2807, 2), (key2614, -1), (key2827, -1), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, 2), (key2724, 2)]

def rawRow6457 : Integer.Sparse Key := [(key2724, 1), (key2698, 1), (key2704, -2), (key2868, 1), (key2851, 1), (key3025, -2), (key2624, -2), (key3021, 1), (key2630, 1), (key2858, -2), (key3022, 1), (key2638, 1), (key2724, -1), (key2698, -1), (key2752, 1), (key2669, 1), (key2827, -1), (key2801, -1), (key3016, 1), (key2608, 1), (key3025, 1), (key2624, 1), (key2724, -1), (key2638, -1), (key2919, 1), (key2752, 1), (key2757, -1), (key2659, -1), (key2784, 2), (key2792, -1), (key2669, -1), (key2807, 2), (key2827, -1), (key2614, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, 2), (key2638, 2)]

def rawRow6458 : Integer.Sparse Key := [(key2851, 1), (key2868, 1), (key2858, -2), (key2698, 1), (key2724, 1), (key2624, -2), (key3025, -2), (key2638, 1), (key3022, 1), (key2704, -2), (key2630, 1), (key3021, 1), (key2801, -1), (key2827, -1), (key2792, 1), (key2919, 1), (key2698, -1), (key2724, -1), (key2624, 1), (key3025, 1), (key2608, 1), (key3016, 1), (key2659, -1), (key2757, -1), (key2669, 1), (key2792, 1), (key2638, -1), (key2724, -1), (key2807, 2), (key2704, -1), (key2858, -1), (key2784, 2), (key2630, -1), (key2868, -1), (key2669, -1), (key2792, -1), (key2614, -1), (key2827, -1), (key2638, 2), (key2724, 2)]

def rawRow6459 : Integer.Sparse Key := [(key2868, 1), (key2851, 1), (key2858, -2), (key2724, 1), (key2698, 1), (key3025, -2), (key2624, -2), (key3022, 1), (key2638, 1), (key2704, -2), (key3021, 1), (key2630, 1), (key2827, -1), (key2801, -1), (key2919, 1), (key2792, 1), (key2724, -1), (key2698, -1), (key3025, 1), (key2624, 1), (key3016, 1), (key2608, 1), (key2757, -1), (key2659, -1), (key2792, 1), (key2669, 1), (key2724, -1), (key2638, -1), (key2807, 2), (key2858, -1), (key2704, -1), (key2784, 2), (key2868, -1), (key2630, -1), (key2792, -1), (key2669, -1), (key2827, -1), (key2614, -1), (key2724, 2), (key2638, 2)]

def rawRow6460 : Integer.Sparse Key := [(key2858, 1), (key2868, 1), (key2851, -2), (key3022, 1), (key3025, 1), (key2638, -2), (key2724, -2), (key2624, 1), (key2698, 1), (key3021, -2), (key2630, 1), (key2704, 1), (key2919, -1), (key2922, -1), (key2778, 1), (key2801, 1), (key3022, -1), (key3025, -1), (key2638, 1), (key2724, 1), (key2659, 1), (key2757, 1), (key2608, -1), (key2663, -1), (key2724, 1), (key2827, 1), (key2614, -1), (key2669, -1), (key2858, 2), (key2704, -1), (key2807, -1), (key2868, 2), (key2630, -1), (key2784, -1), (key2724, -1), (key2827, -1), (key2638, -1), (key2792, -1), (key2614, 2), (key2669, 2)]

def rawRow6461 : Integer.Sparse Key := [(key2868, 1), (key2858, 1), (key2851, -2), (key3025, 1), (key3022, 1), (key2724, -2), (key2638, -2), (key2698, 1), (key2624, 1), (key3021, -2), (key2704, 1), (key2630, 1), (key2922, -1), (key2919, -1), (key2801, 1), (key2778, 1), (key3025, -1), (key3022, -1), (key2724, 1), (key2638, 1), (key2757, 1), (key2659, 1), (key2663, -1), (key2608, -1), (key2827, 1), (key2724, 1), (key2669, -1), (key2614, -1), (key2858, 2), (key2807, -1), (key2704, -1), (key2868, 2), (key2784, -1), (key2630, -1), (key2827, -1), (key2724, -1), (key2792, -1), (key2638, -1), (key2669, 2), (key2614, 2)]

def rawRow6462 : Integer.Sparse Key := [(key3021, 1), (key3022, 1), (key3025, -2), (key2630, 1), (key2638, 1), (key2704, -2), (key2858, -2), (key2724, 1), (key2868, 1), (key2624, -2), (key2698, 1), (key2851, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3025, 1), (key2657, -1), (key2659, -1), (key2752, 1), (key2919, 1), (key2669, 1), (key2792, 1), (key2724, -1), (key2827, -1), (key2608, 1), (key2624, 1), (key2778, -1), (key2801, -1), (key2724, 2), (key2827, -1), (key2868, -1), (key2638, 2), (key2792, -1), (key2858, -1), (key2614, -1), (key2630, -1), (key2669, -1), (key2704, -1), (key2784, 2), (key2807, 2)]

def rawRow6463 : Integer.Sparse Key := [(key3022, 1), (key3021, 1), (key3025, -2), (key2638, 1), (key2630, 1), (key2858, -2), (key2704, -2), (key2868, 1), (key2724, 1), (key2624, -2), (key2851, 1), (key2698, 1), (key3009, -1), (key3007, -1), (key3025, 1), (key3016, 1), (key2659, -1), (key2657, -1), (key2919, 1), (key2752, 1), (key2792, 1), (key2669, 1), (key2827, -1), (key2724, -1), (key2624, 1), (key2608, 1), (key2801, -1), (key2778, -1), (key2724, 2), (key2868, -1), (key2827, -1), (key2638, 2), (key2858, -1), (key2792, -1), (key2630, -1), (key2614, -1), (key2704, -1), (key2669, -1), (key2807, 2), (key2784, 2)]

def rawRow6464 : Integer.Sparse Key := [(key3022, 1), (key3025, 1), (key3021, -2), (key2858, 1), (key2868, 1), (key2638, -2), (key2724, -2), (key2630, 1), (key2704, 1), (key2851, -2), (key2624, 1), (key2698, 1), (key3022, -1), (key3025, -1), (key3007, 1), (key3011, 1), (key2919, -1), (key2922, -1), (key2659, 1), (key2757, 1), (key2638, 1), (key2724, 1), (key2614, -1), (key2669, -1), (key2778, 1), (key2801, 1), (key2608, -1), (key2663, -1), (key2868, 2), (key2724, -1), (key2827, -1), (key2858, 2), (key2638, -1), (key2792, -1), (key2704, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2614, 2), (key2669, 2)]

def rawRow6465 : Integer.Sparse Key := [(key3025, 1), (key3022, 1), (key3021, -2), (key2868, 1), (key2858, 1), (key2724, -2), (key2638, -2), (key2704, 1), (key2630, 1), (key2851, -2), (key2698, 1), (key2624, 1), (key3025, -1), (key3022, -1), (key3011, 1), (key3007, 1), (key2922, -1), (key2919, -1), (key2757, 1), (key2659, 1), (key2724, 1), (key2638, 1), (key2669, -1), (key2614, -1), (key2801, 1), (key2778, 1), (key2663, -1), (key2608, -1), (key2868, 2), (key2827, -1), (key2724, -1), (key2858, 2), (key2792, -1), (key2638, -1), (key2807, -1), (key2704, -1), (key2784, -1), (key2630, -1), (key2669, 2), (key2614, 2)]

def rawRow6466 : Integer.Sparse Key := [(key2657, 1), (key2657, 1), (key2659, -2), (key2752, 1), (key2752, 1), (key2918, -2), (key2918, -2), (key2919, 1), (key2919, 1), (key2757, -2), (key2922, 1), (key2922, 1), (key2614, -1), (key2614, -1), (key2638, 1), (key2638, 1), (key2669, -1), (key2669, -1), (key2784, 1), (key2784, 1), (key2807, 1), (key2807, 1), (key2858, -1), (key2858, -1), (key2724, 1), (key2724, 1), (key2868, -1), (key2868, -1), (key2608, 2), (key2624, -1), (key2624, -1), (key2663, 2), (key2698, -1), (key2698, -1), (key2778, -1), (key2778, -1), (key2801, -1), (key2801, -1), (key2851, 2), (key2851, 2)]

def rawRow6467 : Integer.Sparse Key := [(key2657, 1), (key2659, 1), (key2657, -2), (key2918, 1), (key2919, 1), (key2752, -2), (key2919, -2), (key2752, 1), (key2918, 1), (key2922, -2), (key2757, 1), (key2922, 1), (key2630, -1), (key2638, -1), (key2614, 1), (key2630, 1), (key2784, -1), (key2792, -1), (key2669, 1), (key2792, 1), (key2704, 1), (key2858, 1), (key2704, -1), (key2807, -1), (key2827, 1), (key2868, 1), (key2724, -1), (key2827, -1), (key2624, 2), (key2608, -1), (key2624, -1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2851, -1), (key2778, 2), (key2801, 2)]

def rawRow6468 : Integer.Sparse Key := [(key2659, 1), (key2657, 1), (key2657, -2), (key2919, 1), (key2918, 1), (key2919, -2), (key2752, -2), (key2918, 1), (key2752, 1), (key2922, -2), (key2922, 1), (key2757, 1), (key2638, -1), (key2630, -1), (key2630, 1), (key2614, 1), (key2792, -1), (key2784, -1), (key2792, 1), (key2669, 1), (key2858, 1), (key2704, 1), (key2807, -1), (key2704, -1), (key2868, 1), (key2827, 1), (key2827, -1), (key2724, -1), (key2624, 2), (key2624, -1), (key2608, -1), (key2698, 2), (key2698, -1), (key2663, -1), (key2851, -1), (key2801, -1), (key2851, -1), (key2778, -1), (key2801, 2), (key2778, 2)]

def rawRow6469 : Integer.Sparse Key := [(key2752, 1), (key2752, 1), (key2757, -2), (key2657, 1), (key2657, 1), (key2918, -2), (key2918, -2), (key2922, 1), (key2922, 1), (key2659, -2), (key2919, 1), (key2919, 1), (key2669, -1), (key2669, -1), (key2724, 1), (key2724, 1), (key2614, -1), (key2614, -1), (key2807, 1), (key2807, 1), (key2784, 1), (key2784, 1), (key2868, -1), (key2868, -1), (key2638, 1), (key2638, 1), (key2858, -1), (key2858, -1), (key2663, 2), (key2698, -1), (key2698, -1), (key2608, 2), (key2801, -1), (key2801, -1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, 2), (key2851, 2)]

def rawRow6470 : Integer.Sparse Key := [(key2752, 1), (key2757, 1), (key2752, -2), (key2918, 1), (key2922, 1), (key2657, -2), (key2922, -2), (key2657, 1), (key2918, 1), (key2919, -2), (key2659, 1), (key2919, 1), (key2704, -1), (key2724, -1), (key2669, 1), (key2704, 1), (key2807, -1), (key2827, -1), (key2614, 1), (key2827, 1), (key2630, 1), (key2868, 1), (key2630, -1), (key2784, -1), (key2792, 1), (key2858, 1), (key2638, -1), (key2792, -1), (key2698, 2), (key2663, -1), (key2698, -1), (key2801, 2), (key2608, -1), (key2801, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, 2), (key2698, 2)]

def rawRow6471 : Integer.Sparse Key := [(key2757, 1), (key2752, 1), (key2752, -2), (key2922, 1), (key2918, 1), (key2922, -2), (key2657, -2), (key2918, 1), (key2657, 1), (key2919, -2), (key2919, 1), (key2659, 1), (key2724, -1), (key2704, -1), (key2704, 1), (key2669, 1), (key2827, -1), (key2807, -1), (key2827, 1), (key2614, 1), (key2868, 1), (key2630, 1), (key2784, -1), (key2630, -1), (key2858, 1), (key2792, 1), (key2792, -1), (key2638, -1), (key2698, 2), (key2698, -1), (key2663, -1), (key2801, 2), (key2801, -1), (key2608, -1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, 2), (key2624, 2)]

def rawRow6472 : Integer.Sparse Key := [(key2918, 1), (key2919, 1), (key2922, -2), (key2657, 1), (key2659, 1), (key2752, -2), (key2919, -2), (key2757, 1), (key2922, 1), (key2657, -2), (key2752, 1), (key2918, 1), (key2784, -1), (key2792, -1), (key2827, 1), (key2868, 1), (key2630, -1), (key2638, -1), (key2704, 1), (key2858, 1), (key2669, 1), (key2792, 1), (key2724, -1), (key2827, -1), (key2614, 1), (key2630, 1), (key2704, -1), (key2807, -1), (key2778, 2), (key2801, -1), (key2851, -1), (key2624, 2), (key2698, -1), (key2851, -1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, 2), (key2801, 2)]

def rawRow6473 : Integer.Sparse Key := [(key2919, 1), (key2918, 1), (key2922, -2), (key2659, 1), (key2657, 1), (key2919, -2), (key2752, -2), (key2922, 1), (key2757, 1), (key2657, -2), (key2918, 1), (key2752, 1), (key2792, -1), (key2784, -1), (key2868, 1), (key2827, 1), (key2638, -1), (key2630, -1), (key2858, 1), (key2704, 1), (key2792, 1), (key2669, 1), (key2827, -1), (key2724, -1), (key2630, 1), (key2614, 1), (key2807, -1), (key2704, -1), (key2778, 2), (key2851, -1), (key2801, -1), (key2624, 2), (key2851, -1), (key2698, -1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, 2), (key2778, 2)]

def rawRow6474 : Integer.Sparse Key := [(key2918, 1), (key2922, 1), (key2919, -2), (key2752, 1), (key2757, 1), (key2657, -2), (key2922, -2), (key2659, 1), (key2919, 1), (key2752, -2), (key2657, 1), (key2918, 1), (key2807, -1), (key2827, -1), (key2792, 1), (key2858, 1), (key2704, -1), (key2724, -1), (key2630, 1), (key2868, 1), (key2614, 1), (key2827, 1), (key2638, -1), (key2792, -1), (key2669, 1), (key2704, 1), (key2630, -1), (key2784, -1), (key2801, 2), (key2778, -1), (key2851, -1), (key2698, 2), (key2624, -1), (key2851, -1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, 2), (key2698, 2)]

def rawRow6475 : Integer.Sparse Key := [(key2922, 1), (key2918, 1), (key2919, -2), (key2757, 1), (key2752, 1), (key2922, -2), (key2657, -2), (key2919, 1), (key2659, 1), (key2752, -2), (key2918, 1), (key2657, 1), (key2827, -1), (key2807, -1), (key2858, 1), (key2792, 1), (key2724, -1), (key2704, -1), (key2868, 1), (key2630, 1), (key2827, 1), (key2614, 1), (key2792, -1), (key2638, -1), (key2704, 1), (key2669, 1), (key2784, -1), (key2630, -1), (key2801, 2), (key2851, -1), (key2778, -1), (key2698, 2), (key2851, -1), (key2624, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, 2), (key2624, 2)]

def rawRow6476 : Integer.Sparse Key := [(key2919, 1), (key2922, 1), (key2918, -2), (key2919, 1), (key2922, 1), (key2659, -2), (key2757, -2), (key2657, 1), (key2752, 1), (key2918, -2), (key2657, 1), (key2752, 1), (key2858, -1), (key2868, -1), (key2784, 1), (key2807, 1), (key2858, -1), (key2868, -1), (key2638, 1), (key2724, 1), (key2638, 1), (key2724, 1), (key2614, -1), (key2669, -1), (key2784, 1), (key2807, 1), (key2614, -1), (key2669, -1), (key2851, 2), (key2778, -1), (key2801, -1), (key2851, 2), (key2624, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, 2), (key2663, 2)]

def rawRow6477 : Integer.Sparse Key := [(key2922, 1), (key2919, 1), (key2918, -2), (key2922, 1), (key2919, 1), (key2757, -2), (key2659, -2), (key2752, 1), (key2657, 1), (key2918, -2), (key2752, 1), (key2657, 1), (key2868, -1), (key2858, -1), (key2807, 1), (key2784, 1), (key2868, -1), (key2858, -1), (key2724, 1), (key2638, 1), (key2724, 1), (key2638, 1), (key2669, -1), (key2614, -1), (key2807, 1), (key2784, 1), (key2669, -1), (key2614, -1), (key2851, 2), (key2801, -1), (key2778, -1), (key2851, 2), (key2698, -1), (key2624, -1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, 2), (key2608, 2)]

def rawRow6478 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -1), (key2632, -1), (key2640, 2), (key2640, 2), (key2644, -1), (key2644, -1), (key2658, 2), (key2660, -1), (key2660, -1), (key2671, 1), (key2671, 1), (key2676, -2), (key2706, 1), (key2706, 1), (key2726, -2), (key2726, -2), (key2732, 1), (key2732, 1), (key2753, -2), (key2758, 1), (key2758, 1), (key2794, -1), (key2794, -1), (key2798, 1), (key2798, 1), (key2829, 1), (key2829, 1), (key2835, -1), (key2835, -1), (key2860, -1), (key2860, -1), (key2870, 1), (key2870, 1), (key2920, 1), (key2920, 1), (key2923, -1), (key2923, -1)]

def rawRow6479 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2616, 2), (key2640, -1), (key2644, -1), (key2632, 2), (key2644, 2), (key2632, -1), (key2640, -1), (key2660, 2), (key2658, -1), (key2660, -1), (key2671, 1), (key2676, 1), (key2671, -2), (key2726, 1), (key2732, 1), (key2706, -2), (key2732, -2), (key2706, 1), (key2726, 1), (key2758, -2), (key2753, 1), (key2758, 1), (key2786, -1), (key2798, -1), (key2786, 1), (key2794, 1), (key2809, 1), (key2835, 1), (key2809, -1), (key2829, -1), (key2870, -1), (key2885, -1), (key2860, 1), (key2885, 1), (key2923, 1), (key2927, 1), (key2920, -1), (key2927, -1)]

def rawRow6480 : Integer.Sparse Key := [(key2618, -1), (key2612, -1), (key2616, 2), (key2644, -1), (key2640, -1), (key2644, 2), (key2632, 2), (key2640, -1), (key2632, -1), (key2660, 2), (key2660, -1), (key2658, -1), (key2676, 1), (key2671, 1), (key2671, -2), (key2732, 1), (key2726, 1), (key2732, -2), (key2706, -2), (key2726, 1), (key2706, 1), (key2758, -2), (key2758, 1), (key2753, 1), (key2798, -1), (key2786, -1), (key2794, 1), (key2786, 1), (key2835, 1), (key2809, 1), (key2829, -1), (key2809, -1), (key2885, -1), (key2870, -1), (key2885, 1), (key2860, 1), (key2927, 1), (key2923, 1), (key2927, -1), (key2920, -1)]

def rawRow6481 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2641, 2), (key2612, -1), (key2616, -1), (key2640, 2), (key2640, 2), (key2660, -1), (key2660, -1), (key2621, 2), (key2644, -1), (key2644, -1), (key2706, 1), (key2706, 1), (key2753, -2), (key2671, 1), (key2671, 1), (key2726, -2), (key2726, -2), (key2758, 1), (key2758, 1), (key2676, -2), (key2732, 1), (key2732, 1), (key2860, -1), (key2860, -1), (key2920, 1), (key2920, 1), (key2870, 1), (key2870, 1), (key2923, -1), (key2923, -1), (key2794, -1), (key2794, -1), (key2829, 1), (key2829, 1), (key2798, 1), (key2798, 1), (key2835, -1), (key2835, -1)]

def rawRow6482 : Integer.Sparse Key := [(key2628, -1), (key2641, -1), (key2628, 2), (key2646, -1), (key2653, -1), (key2612, 2), (key2653, 2), (key2616, -1), (key2640, -1), (key2644, 2), (key2621, -1), (key2644, -1), (key2706, 1), (key2753, 1), (key2706, -2), (key2726, 1), (key2758, 1), (key2671, -2), (key2758, -2), (key2671, 1), (key2726, 1), (key2732, -2), (key2676, 1), (key2732, 1), (key2809, -1), (key2920, -1), (key2809, 1), (key2860, 1), (key2786, 1), (key2923, 1), (key2786, -1), (key2870, -1), (key2829, -1), (key2927, -1), (key2794, 1), (key2927, 1), (key2835, 1), (key2885, 1), (key2798, -1), (key2885, -1)]

def rawRow6483 : Integer.Sparse Key := [(key2641, -1), (key2628, -1), (key2628, 2), (key2653, -1), (key2646, -1), (key2653, 2), (key2612, 2), (key2640, -1), (key2616, -1), (key2644, 2), (key2644, -1), (key2621, -1), (key2753, 1), (key2706, 1), (key2706, -2), (key2758, 1), (key2726, 1), (key2758, -2), (key2671, -2), (key2726, 1), (key2671, 1), (key2732, -2), (key2732, 1), (key2676, 1), (key2920, -1), (key2809, -1), (key2860, 1), (key2809, 1), (key2923, 1), (key2786, 1), (key2870, -1), (key2786, -1), (key2927, -1), (key2829, -1), (key2927, 1), (key2794, 1), (key2885, 1), (key2835, 1), (key2885, -1), (key2798, -1)]

def rawRow6484 : Integer.Sparse Key := [(key2646, -1), (key2648, -1), (key2653, 2), (key2612, -1), (key2618, -1), (key2628, 2), (key2648, 2), (key2641, -1), (key2653, -1), (key2616, 2), (key2632, -1), (key2640, -1), (key2726, 1), (key2732, 1), (key2758, -2), (key2671, 1), (key2676, 1), (key2706, -2), (key2732, -2), (key2753, 1), (key2758, 1), (key2671, -2), (key2706, 1), (key2726, 1), (key2870, -1), (key2885, -1), (key2923, 1), (key2927, 1), (key2860, 1), (key2885, 1), (key2920, -1), (key2927, -1), (key2786, -1), (key2798, -1), (key2809, 1), (key2835, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2829, -1)]

def rawRow6485 : Integer.Sparse Key := [(key2648, -1), (key2646, -1), (key2653, 2), (key2618, -1), (key2612, -1), (key2648, 2), (key2628, 2), (key2653, -1), (key2641, -1), (key2616, 2), (key2640, -1), (key2632, -1), (key2732, 1), (key2726, 1), (key2758, -2), (key2676, 1), (key2671, 1), (key2732, -2), (key2706, -2), (key2758, 1), (key2753, 1), (key2671, -2), (key2726, 1), (key2706, 1), (key2885, -1), (key2870, -1), (key2927, 1), (key2923, 1), (key2885, 1), (key2860, 1), (key2927, -1), (key2920, -1), (key2798, -1), (key2786, -1), (key2835, 1), (key2809, 1), (key2794, 1), (key2786, 1), (key2829, -1), (key2809, -1)]

def rawRow6486 : Integer.Sparse Key := [(key2646, -1), (key2653, -1), (key2648, 2), (key2628, -1), (key2641, -1), (key2612, 2), (key2653, 2), (key2618, -1), (key2648, -1), (key2632, 2), (key2616, -1), (key2640, -1), (key2726, 1), (key2758, 1), (key2732, -2), (key2706, 1), (key2753, 1), (key2671, -2), (key2758, -2), (key2676, 1), (key2732, 1), (key2706, -2), (key2671, 1), (key2726, 1), (key2829, -1), (key2927, -1), (key2835, 1), (key2885, 1), (key2794, 1), (key2927, 1), (key2798, -1), (key2885, -1), (key2809, -1), (key2920, -1), (key2786, 1), (key2923, 1), (key2809, 1), (key2860, 1), (key2786, -1), (key2870, -1)]

def rawRow6487 : Integer.Sparse Key := [(key2653, -1), (key2646, -1), (key2648, 2), (key2641, -1), (key2628, -1), (key2653, 2), (key2612, 2), (key2648, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2616, -1), (key2758, 1), (key2726, 1), (key2732, -2), (key2753, 1), (key2706, 1), (key2758, -2), (key2671, -2), (key2732, 1), (key2676, 1), (key2706, -2), (key2726, 1), (key2671, 1), (key2927, -1), (key2829, -1), (key2885, 1), (key2835, 1), (key2927, 1), (key2794, 1), (key2885, -1), (key2798, -1), (key2920, -1), (key2809, -1), (key2923, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, -1), (key2786, -1)]

def rawRow6488 : Integer.Sparse Key := [(key2648, -1), (key2653, -1), (key2646, 2), (key2648, -1), (key2653, -1), (key2618, 2), (key2641, 2), (key2612, -1), (key2628, -1), (key2640, 2), (key2616, -1), (key2632, -1), (key2732, 1), (key2758, 1), (key2726, -2), (key2732, 1), (key2758, 1), (key2676, -2), (key2753, -2), (key2671, 1), (key2706, 1), (key2726, -2), (key2671, 1), (key2706, 1), (key2835, -1), (key2923, -1), (key2829, 1), (key2870, 1), (key2798, 1), (key2920, 1), (key2794, -1), (key2860, -1), (key2835, -1), (key2923, -1), (key2798, 1), (key2920, 1), (key2829, 1), (key2870, 1), (key2794, -1), (key2860, -1)]

def rawRow6489 : Integer.Sparse Key := [(key2653, -1), (key2648, -1), (key2646, 2), (key2653, -1), (key2648, -1), (key2641, 2), (key2618, 2), (key2628, -1), (key2612, -1), (key2640, 2), (key2632, -1), (key2616, -1), (key2758, 1), (key2732, 1), (key2726, -2), (key2758, 1), (key2732, 1), (key2753, -2), (key2676, -2), (key2706, 1), (key2671, 1), (key2726, -2), (key2706, 1), (key2671, 1), (key2923, -1), (key2835, -1), (key2870, 1), (key2829, 1), (key2920, 1), (key2798, 1), (key2860, -1), (key2794, -1), (key2923, -1), (key2835, -1), (key2920, 1), (key2798, 1), (key2870, 1), (key2829, 1), (key2860, -1), (key2794, -1)]

def rawRow6490 : Integer.Sparse Key := [(key2938, -1), (key2943, -1), (key2936, 2), (key2997, -1), (key2998, -1), (key2950, 2), (key2976, 2), (key2948, -1), (key2972, -1), (key3000, 2), (key2960, -1), (key2983, -1), (key2648, 1), (key2653, 1), (key2646, -2), (key2997, 1), (key2998, 1), (key2737, -2), (key2897, -2), (key2735, 1), (key2893, 1), (key3000, -2), (key2747, 1), (key2904, 1), (key2618, -1), (key2641, -1), (key2612, 1), (key2628, 1), (key2673, 1), (key2795, 1), (key2667, -1), (key2782, -1), (key2950, -1), (key2976, -1), (key2737, 1), (key2897, 1), (key2960, 1), (key2983, 1), (key2747, -1), (key2904, -1)]

def rawRow6491 : Integer.Sparse Key := [(key2943, -1), (key2938, -1), (key2936, 2), (key2998, -1), (key2997, -1), (key2976, 2), (key2950, 2), (key2972, -1), (key2948, -1), (key3000, 2), (key2983, -1), (key2960, -1), (key2653, 1), (key2648, 1), (key2646, -2), (key2998, 1), (key2997, 1), (key2897, -2), (key2737, -2), (key2893, 1), (key2735, 1), (key3000, -2), (key2904, 1), (key2747, 1), (key2641, -1), (key2618, -1), (key2628, 1), (key2612, 1), (key2795, 1), (key2673, 1), (key2782, -1), (key2667, -1), (key2976, -1), (key2950, -1), (key2897, 1), (key2737, 1), (key2983, 1), (key2960, 1), (key2904, -1), (key2747, -1)]

def rawRow6492 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2950, 2), (key2972, -1), (key2983, -1), (key2936, 2), (key3000, 2), (key2938, -1), (key2997, -1), (key2976, 2), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2737, -2), (key2893, 1), (key2904, 1), (key2646, -2), (key3000, -2), (key2648, 1), (key2997, 1), (key2897, -2), (key2653, 1), (key2998, 1), (key2667, -1), (key2747, -1), (key2673, 1), (key2737, 1), (key2612, 1), (key2960, 1), (key2618, -1), (key2950, -1), (key2782, -1), (key2904, -1), (key2628, 1), (key2983, 1), (key2795, 1), (key2897, 1), (key2641, -1), (key2976, -1)]

def rawRow6493 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2950, 2), (key2983, -1), (key2972, -1), (key3000, 2), (key2936, 2), (key2997, -1), (key2938, -1), (key2976, 2), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key2737, -2), (key2904, 1), (key2893, 1), (key3000, -2), (key2646, -2), (key2997, 1), (key2648, 1), (key2897, -2), (key2998, 1), (key2653, 1), (key2747, -1), (key2667, -1), (key2737, 1), (key2673, 1), (key2960, 1), (key2612, 1), (key2950, -1), (key2618, -1), (key2904, -1), (key2782, -1), (key2983, 1), (key2628, 1), (key2897, 1), (key2795, 1), (key2976, -1), (key2641, -1)]

def rawRow6494 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2976, 2), (key2948, -1), (key2960, -1), (key2936, 2), (key3000, 2), (key2943, -1), (key2998, -1), (key2950, 2), (key2938, -1), (key2997, -1), (key2893, 1), (key2904, 1), (key2897, -2), (key2735, 1), (key2747, 1), (key2646, -2), (key3000, -2), (key2653, 1), (key2998, 1), (key2737, -2), (key2648, 1), (key2997, 1), (key2782, -1), (key2904, -1), (key2795, 1), (key2897, 1), (key2628, 1), (key2983, 1), (key2641, -1), (key2976, -1), (key2667, -1), (key2747, -1), (key2612, 1), (key2960, 1), (key2673, 1), (key2737, 1), (key2618, -1), (key2950, -1)]

def rawRow6495 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2976, 2), (key2960, -1), (key2948, -1), (key3000, 2), (key2936, 2), (key2998, -1), (key2943, -1), (key2950, 2), (key2997, -1), (key2938, -1), (key2904, 1), (key2893, 1), (key2897, -2), (key2747, 1), (key2735, 1), (key3000, -2), (key2646, -2), (key2998, 1), (key2653, 1), (key2737, -2), (key2997, 1), (key2648, 1), (key2904, -1), (key2782, -1), (key2897, 1), (key2795, 1), (key2983, 1), (key2628, 1), (key2976, -1), (key2641, -1), (key2747, -1), (key2667, -1), (key2960, 1), (key2612, 1), (key2737, 1), (key2673, 1), (key2950, -1), (key2618, -1)]

def rawRow6496 : Integer.Sparse Key := [(key2997, -1), (key2998, -1), (key3000, 2), (key2938, -1), (key2943, -1), (key2950, 2), (key2976, 2), (key2960, -1), (key2983, -1), (key2936, 2), (key2948, -1), (key2972, -1), (key2997, 1), (key2998, 1), (key3000, -2), (key2648, 1), (key2653, 1), (key2737, -2), (key2897, -2), (key2747, 1), (key2904, 1), (key2646, -2), (key2735, 1), (key2893, 1), (key2950, -1), (key2976, -1), (key2960, 1), (key2983, 1), (key2737, 1), (key2897, 1), (key2747, -1), (key2904, -1), (key2618, -1), (key2641, -1), (key2673, 1), (key2795, 1), (key2612, 1), (key2628, 1), (key2667, -1), (key2782, -1)]

def rawRow6497 : Integer.Sparse Key := [(key2998, -1), (key2997, -1), (key3000, 2), (key2943, -1), (key2938, -1), (key2976, 2), (key2950, 2), (key2983, -1), (key2960, -1), (key2936, 2), (key2972, -1), (key2948, -1), (key2998, 1), (key2997, 1), (key3000, -2), (key2653, 1), (key2648, 1), (key2897, -2), (key2737, -2), (key2904, 1), (key2747, 1), (key2646, -2), (key2893, 1), (key2735, 1), (key2976, -1), (key2950, -1), (key2983, 1), (key2960, 1), (key2897, 1), (key2737, 1), (key2904, -1), (key2747, -1), (key2641, -1), (key2618, -1), (key2795, 1), (key2673, 1), (key2628, 1), (key2612, 1), (key2782, -1), (key2667, -1)]

def rawRow6518 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2619, 2), (key2632, -1), (key2632, -1), (key2640, 2), (key2640, 2), (key2642, -1), (key2642, -1), (key2649, 2), (key2654, -1), (key2654, -1), (key2671, 1), (key2671, 1), (key2674, -2), (key2706, 1), (key2706, 1), (key2726, -2), (key2726, -2), (key2729, 1), (key2729, 1), (key2738, -2), (key2748, 1), (key2748, 1), (key2794, -1), (key2794, -1), (key2796, 1), (key2796, 1), (key2829, 1), (key2829, 1), (key2832, -1), (key2832, -1), (key2860, -1), (key2860, -1), (key2870, 1), (key2870, 1), (key2898, 1), (key2898, 1), (key2905, -1), (key2905, -1)]

def rawRow6519 : Integer.Sparse Key := [(key2616, -1), (key2619, -1), (key2616, 2), (key2640, -1), (key2642, -1), (key2632, 2), (key2642, 2), (key2632, -1), (key2640, -1), (key2654, 2), (key2649, -1), (key2654, -1), (key2671, 1), (key2674, 1), (key2671, -2), (key2726, 1), (key2729, 1), (key2706, -2), (key2729, -2), (key2706, 1), (key2726, 1), (key2748, -2), (key2738, 1), (key2748, 1), (key2786, -1), (key2796, -1), (key2786, 1), (key2794, 1), (key2809, 1), (key2832, 1), (key2809, -1), (key2829, -1), (key2870, -1), (key2883, -1), (key2860, 1), (key2883, 1), (key2905, 1), (key2913, 1), (key2898, -1), (key2913, -1)]

def rawRow6520 : Integer.Sparse Key := [(key2619, -1), (key2616, -1), (key2616, 2), (key2642, -1), (key2640, -1), (key2642, 2), (key2632, 2), (key2640, -1), (key2632, -1), (key2654, 2), (key2654, -1), (key2649, -1), (key2674, 1), (key2671, 1), (key2671, -2), (key2729, 1), (key2726, 1), (key2729, -2), (key2706, -2), (key2726, 1), (key2706, 1), (key2748, -2), (key2748, 1), (key2738, 1), (key2796, -1), (key2786, -1), (key2794, 1), (key2786, 1), (key2832, 1), (key2809, 1), (key2829, -1), (key2809, -1), (key2883, -1), (key2870, -1), (key2883, 1), (key2860, 1), (key2913, 1), (key2905, 1), (key2913, -1), (key2898, -1)]

def rawRow6521 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2649, 2), (key2616, -1), (key2616, -1), (key2640, 2), (key2640, 2), (key2654, -1), (key2654, -1), (key2619, 2), (key2642, -1), (key2642, -1), (key2706, 1), (key2706, 1), (key2738, -2), (key2671, 1), (key2671, 1), (key2726, -2), (key2726, -2), (key2748, 1), (key2748, 1), (key2674, -2), (key2729, 1), (key2729, 1), (key2860, -1), (key2860, -1), (key2898, 1), (key2898, 1), (key2870, 1), (key2870, 1), (key2905, -1), (key2905, -1), (key2794, -1), (key2794, -1), (key2829, 1), (key2829, 1), (key2796, 1), (key2796, 1), (key2832, -1), (key2832, -1)]

def rawRow6522 : Integer.Sparse Key := [(key2632, -1), (key2649, -1), (key2632, 2), (key2640, -1), (key2654, -1), (key2616, 2), (key2654, 2), (key2616, -1), (key2640, -1), (key2642, 2), (key2619, -1), (key2642, -1), (key2706, 1), (key2738, 1), (key2706, -2), (key2726, 1), (key2748, 1), (key2671, -2), (key2748, -2), (key2671, 1), (key2726, 1), (key2729, -2), (key2674, 1), (key2729, 1), (key2809, -1), (key2898, -1), (key2809, 1), (key2860, 1), (key2786, 1), (key2905, 1), (key2786, -1), (key2870, -1), (key2829, -1), (key2913, -1), (key2794, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2796, -1), (key2883, -1)]

def rawRow6523 : Integer.Sparse Key := [(key2649, -1), (key2632, -1), (key2632, 2), (key2654, -1), (key2640, -1), (key2654, 2), (key2616, 2), (key2640, -1), (key2616, -1), (key2642, 2), (key2642, -1), (key2619, -1), (key2738, 1), (key2706, 1), (key2706, -2), (key2748, 1), (key2726, 1), (key2748, -2), (key2671, -2), (key2726, 1), (key2671, 1), (key2729, -2), (key2729, 1), (key2674, 1), (key2898, -1), (key2809, -1), (key2860, 1), (key2809, 1), (key2905, 1), (key2786, 1), (key2870, -1), (key2786, -1), (key2913, -1), (key2829, -1), (key2913, 1), (key2794, 1), (key2883, 1), (key2832, 1), (key2883, -1), (key2796, -1)]

def rawRow6524 : Integer.Sparse Key := [(key2640, -1), (key2642, -1), (key2654, 2), (key2616, -1), (key2619, -1), (key2632, 2), (key2642, 2), (key2649, -1), (key2654, -1), (key2616, 2), (key2632, -1), (key2640, -1), (key2726, 1), (key2729, 1), (key2748, -2), (key2671, 1), (key2674, 1), (key2706, -2), (key2729, -2), (key2738, 1), (key2748, 1), (key2671, -2), (key2706, 1), (key2726, 1), (key2870, -1), (key2883, -1), (key2905, 1), (key2913, 1), (key2860, 1), (key2883, 1), (key2898, -1), (key2913, -1), (key2786, -1), (key2796, -1), (key2809, 1), (key2832, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2829, -1)]

def rawRow6525 : Integer.Sparse Key := [(key2642, -1), (key2640, -1), (key2654, 2), (key2619, -1), (key2616, -1), (key2642, 2), (key2632, 2), (key2654, -1), (key2649, -1), (key2616, 2), (key2640, -1), (key2632, -1), (key2729, 1), (key2726, 1), (key2748, -2), (key2674, 1), (key2671, 1), (key2729, -2), (key2706, -2), (key2748, 1), (key2738, 1), (key2671, -2), (key2726, 1), (key2706, 1), (key2883, -1), (key2870, -1), (key2913, 1), (key2905, 1), (key2883, 1), (key2860, 1), (key2913, -1), (key2898, -1), (key2796, -1), (key2786, -1), (key2832, 1), (key2809, 1), (key2794, 1), (key2786, 1), (key2829, -1), (key2809, -1)]

def rawRow6526 : Integer.Sparse Key := [(key2640, -1), (key2654, -1), (key2642, 2), (key2632, -1), (key2649, -1), (key2616, 2), (key2654, 2), (key2619, -1), (key2642, -1), (key2632, 2), (key2616, -1), (key2640, -1), (key2726, 1), (key2748, 1), (key2729, -2), (key2706, 1), (key2738, 1), (key2671, -2), (key2748, -2), (key2674, 1), (key2729, 1), (key2706, -2), (key2671, 1), (key2726, 1), (key2829, -1), (key2913, -1), (key2832, 1), (key2883, 1), (key2794, 1), (key2913, 1), (key2796, -1), (key2883, -1), (key2809, -1), (key2898, -1), (key2786, 1), (key2905, 1), (key2809, 1), (key2860, 1), (key2786, -1), (key2870, -1)]

def rawRow6527 : Integer.Sparse Key := [(key2654, -1), (key2640, -1), (key2642, 2), (key2649, -1), (key2632, -1), (key2654, 2), (key2616, 2), (key2642, -1), (key2619, -1), (key2632, 2), (key2640, -1), (key2616, -1), (key2748, 1), (key2726, 1), (key2729, -2), (key2738, 1), (key2706, 1), (key2748, -2), (key2671, -2), (key2729, 1), (key2674, 1), (key2706, -2), (key2726, 1), (key2671, 1), (key2913, -1), (key2829, -1), (key2883, 1), (key2832, 1), (key2913, 1), (key2794, 1), (key2883, -1), (key2796, -1), (key2898, -1), (key2809, -1), (key2905, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, -1), (key2786, -1)]

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

def rawRow6528 : Integer.Sparse Key := [(key2642, -1), (key2654, -1), (key2640, 2), (key2642, -1), (key2654, -1), (key2619, 2), (key2649, 2), (key2616, -1), (key2632, -1), (key2640, 2), (key2616, -1), (key2632, -1), (key2729, 1), (key2748, 1), (key2726, -2), (key2729, 1), (key2748, 1), (key2674, -2), (key2738, -2), (key2671, 1), (key2706, 1), (key2726, -2), (key2671, 1), (key2706, 1), (key2832, -1), (key2905, -1), (key2829, 1), (key2870, 1), (key2796, 1), (key2898, 1), (key2794, -1), (key2860, -1), (key2832, -1), (key2905, -1), (key2796, 1), (key2898, 1), (key2829, 1), (key2870, 1), (key2794, -1), (key2860, -1)]

def rawRow6529 : Integer.Sparse Key := [(key2654, -1), (key2642, -1), (key2640, 2), (key2654, -1), (key2642, -1), (key2649, 2), (key2619, 2), (key2632, -1), (key2616, -1), (key2640, 2), (key2632, -1), (key2616, -1), (key2748, 1), (key2729, 1), (key2726, -2), (key2748, 1), (key2729, 1), (key2738, -2), (key2674, -2), (key2706, 1), (key2671, 1), (key2726, -2), (key2706, 1), (key2671, 1), (key2905, -1), (key2832, -1), (key2870, 1), (key2829, 1), (key2898, 1), (key2796, 1), (key2860, -1), (key2794, -1), (key2905, -1), (key2832, -1), (key2898, 1), (key2796, 1), (key2870, 1), (key2829, 1), (key2860, -1), (key2794, -1)]

def rawRow6530 : Integer.Sparse Key := [(key2729, -1), (key2748, -1), (key2726, 2), (key2883, -1), (key2913, -1), (key2832, 2), (key2905, 2), (key2829, -1), (key2870, -1), (key2992, 2), (key2961, -1), (key2984, -1), (key2642, 1), (key2654, 1), (key2640, -2), (key2883, 1), (key2913, 1), (key2796, -2), (key2898, -2), (key2794, 1), (key2860, 1), (key2992, -2), (key2944, 1), (key2977, 1), (key2619, -1), (key2649, -1), (key2616, 1), (key2632, 1), (key2674, 1), (key2738, 1), (key2671, -1), (key2706, -1), (key2832, -1), (key2905, -1), (key2796, 1), (key2898, 1), (key2961, 1), (key2984, 1), (key2944, -1), (key2977, -1)]

def rawRow6531 : Integer.Sparse Key := [(key2748, -1), (key2729, -1), (key2726, 2), (key2913, -1), (key2883, -1), (key2905, 2), (key2832, 2), (key2870, -1), (key2829, -1), (key2992, 2), (key2984, -1), (key2961, -1), (key2654, 1), (key2642, 1), (key2640, -2), (key2913, 1), (key2883, 1), (key2898, -2), (key2796, -2), (key2860, 1), (key2794, 1), (key2992, -2), (key2977, 1), (key2944, 1), (key2649, -1), (key2619, -1), (key2632, 1), (key2616, 1), (key2738, 1), (key2674, 1), (key2706, -1), (key2671, -1), (key2905, -1), (key2832, -1), (key2898, 1), (key2796, 1), (key2984, 1), (key2961, 1), (key2977, -1), (key2944, -1)]

def rawRow6532 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2832, 2), (key2870, -1), (key2984, -1), (key2726, 2), (key2992, 2), (key2729, -1), (key2883, -1), (key2905, 2), (key2748, -1), (key2913, -1), (key2794, 1), (key2944, 1), (key2796, -2), (key2860, 1), (key2977, 1), (key2640, -2), (key2992, -2), (key2642, 1), (key2883, 1), (key2898, -2), (key2654, 1), (key2913, 1), (key2671, -1), (key2944, -1), (key2674, 1), (key2796, 1), (key2616, 1), (key2961, 1), (key2619, -1), (key2832, -1), (key2706, -1), (key2977, -1), (key2632, 1), (key2984, 1), (key2738, 1), (key2898, 1), (key2649, -1), (key2905, -1)]

def rawRow6533 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2832, 2), (key2984, -1), (key2870, -1), (key2992, 2), (key2726, 2), (key2883, -1), (key2729, -1), (key2905, 2), (key2913, -1), (key2748, -1), (key2944, 1), (key2794, 1), (key2796, -2), (key2977, 1), (key2860, 1), (key2992, -2), (key2640, -2), (key2883, 1), (key2642, 1), (key2898, -2), (key2913, 1), (key2654, 1), (key2944, -1), (key2671, -1), (key2796, 1), (key2674, 1), (key2961, 1), (key2616, 1), (key2832, -1), (key2619, -1), (key2977, -1), (key2706, -1), (key2984, 1), (key2632, 1), (key2898, 1), (key2738, 1), (key2905, -1), (key2649, -1)]

def rawRow6534 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2905, 2), (key2829, -1), (key2961, -1), (key2726, 2), (key2992, 2), (key2748, -1), (key2913, -1), (key2832, 2), (key2729, -1), (key2883, -1), (key2860, 1), (key2977, 1), (key2898, -2), (key2794, 1), (key2944, 1), (key2640, -2), (key2992, -2), (key2654, 1), (key2913, 1), (key2796, -2), (key2642, 1), (key2883, 1), (key2706, -1), (key2977, -1), (key2738, 1), (key2898, 1), (key2632, 1), (key2984, 1), (key2649, -1), (key2905, -1), (key2671, -1), (key2944, -1), (key2616, 1), (key2961, 1), (key2674, 1), (key2796, 1), (key2619, -1), (key2832, -1)]

def rawRow6535 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2905, 2), (key2961, -1), (key2829, -1), (key2992, 2), (key2726, 2), (key2913, -1), (key2748, -1), (key2832, 2), (key2883, -1), (key2729, -1), (key2977, 1), (key2860, 1), (key2898, -2), (key2944, 1), (key2794, 1), (key2992, -2), (key2640, -2), (key2913, 1), (key2654, 1), (key2796, -2), (key2883, 1), (key2642, 1), (key2977, -1), (key2706, -1), (key2898, 1), (key2738, 1), (key2984, 1), (key2632, 1), (key2905, -1), (key2649, -1), (key2944, -1), (key2671, -1), (key2961, 1), (key2616, 1), (key2796, 1), (key2674, 1), (key2832, -1), (key2619, -1)]

def rawRow6536 : Integer.Sparse Key := [(key2883, -1), (key2913, -1), (key2992, 2), (key2729, -1), (key2748, -1), (key2832, 2), (key2905, 2), (key2961, -1), (key2984, -1), (key2726, 2), (key2829, -1), (key2870, -1), (key2883, 1), (key2913, 1), (key2992, -2), (key2642, 1), (key2654, 1), (key2796, -2), (key2898, -2), (key2944, 1), (key2977, 1), (key2640, -2), (key2794, 1), (key2860, 1), (key2832, -1), (key2905, -1), (key2961, 1), (key2984, 1), (key2796, 1), (key2898, 1), (key2944, -1), (key2977, -1), (key2619, -1), (key2649, -1), (key2674, 1), (key2738, 1), (key2616, 1), (key2632, 1), (key2671, -1), (key2706, -1)]

def rawRow6537 : Integer.Sparse Key := [(key2913, -1), (key2883, -1), (key2992, 2), (key2748, -1), (key2729, -1), (key2905, 2), (key2832, 2), (key2984, -1), (key2961, -1), (key2726, 2), (key2870, -1), (key2829, -1), (key2913, 1), (key2883, 1), (key2992, -2), (key2654, 1), (key2642, 1), (key2898, -2), (key2796, -2), (key2977, 1), (key2944, 1), (key2640, -2), (key2860, 1), (key2794, 1), (key2905, -1), (key2832, -1), (key2984, 1), (key2961, 1), (key2898, 1), (key2796, 1), (key2977, -1), (key2944, -1), (key2649, -1), (key2619, -1), (key2738, 1), (key2674, 1), (key2632, 1), (key2616, 1), (key2706, -1), (key2671, -1)]

def rawRow6558 : Integer.Sparse Key := [(key2379, -4), (key2382, 2), (key2382, 2), (key2393, 2), (key2393, 2), (key2395, -4), (key2771, 2), (key2774, -1), (key2774, -1), (key2848, 2), (key2882, -1), (key2882, -1), (key2891, -1), (key2891, -1), (key2912, -1), (key2912, -1), (key2914, 2), (key2914, 2), (key2933, -1), (key2933, -1), (key2934, 2), (key2970, -1), (key2970, -1), (key2991, 2), (key2991, 2), (key2993, -1), (key2993, -1), (key2996, 2), (key3003, -1), (key3003, -1)]

def rawRow6559 : Integer.Sparse Key := [(key2382, -4), (key2379, 2), (key2382, 2), (key2393, 2), (key2395, 2), (key2393, -4), (key2774, 2), (key2771, -1), (key2774, -1), (key2882, 2), (key2848, -1), (key2882, -1), (key2912, -1), (key2914, -1), (key2891, -1), (key2914, -1), (key2891, 2), (key2912, 2), (key2933, -1), (key2934, -1), (key2933, 2), (key2991, -1), (key2993, -1), (key2970, 2), (key2993, 2), (key2970, -1), (key2991, -1), (key3003, 2), (key2996, -1), (key3003, -1)]

def rawRow6560 : Integer.Sparse Key := [(key2382, -4), (key2382, 2), (key2379, 2), (key2395, 2), (key2393, 2), (key2393, -4), (key2774, 2), (key2774, -1), (key2771, -1), (key2882, 2), (key2882, -1), (key2848, -1), (key2914, -1), (key2912, -1), (key2914, -1), (key2891, -1), (key2912, 2), (key2891, 2), (key2934, -1), (key2933, -1), (key2933, 2), (key2993, -1), (key2991, -1), (key2993, 2), (key2970, 2), (key2991, -1), (key2970, -1), (key3003, 2), (key3003, -1), (key2996, -1)]

def rawRow6561 : Integer.Sparse Key := [(key2379, -4), (key2393, 2), (key2393, 2), (key2382, 2), (key2382, 2), (key2395, -4), (key2848, 2), (key2891, -1), (key2891, -1), (key2771, 2), (key2912, -1), (key2912, -1), (key2774, -1), (key2774, -1), (key2882, -1), (key2882, -1), (key2914, 2), (key2914, 2), (key2970, -1), (key2970, -1), (key2996, 2), (key2933, -1), (key2933, -1), (key2991, 2), (key2991, 2), (key3003, -1), (key3003, -1), (key2934, 2), (key2993, -1), (key2993, -1)]

def rawRow6562 : Integer.Sparse Key := [(key2393, -4), (key2379, 2), (key2393, 2), (key2382, 2), (key2395, 2), (key2382, -4), (key2891, 2), (key2848, -1), (key2891, -1), (key2912, 2), (key2771, -1), (key2912, -1), (key2882, -1), (key2914, -1), (key2774, -1), (key2914, -1), (key2774, 2), (key2882, 2), (key2970, -1), (key2996, -1), (key2970, 2), (key2991, -1), (key3003, -1), (key2933, 2), (key3003, 2), (key2933, -1), (key2991, -1), (key2993, 2), (key2934, -1), (key2993, -1)]

def rawRow6563 : Integer.Sparse Key := [(key2393, -4), (key2393, 2), (key2379, 2), (key2395, 2), (key2382, 2), (key2382, -4), (key2891, 2), (key2891, -1), (key2848, -1), (key2912, 2), (key2912, -1), (key2771, -1), (key2914, -1), (key2882, -1), (key2914, -1), (key2774, -1), (key2882, 2), (key2774, 2), (key2996, -1), (key2970, -1), (key2970, 2), (key3003, -1), (key2991, -1), (key3003, 2), (key2933, 2), (key2991, -1), (key2933, -1), (key2993, 2), (key2993, -1), (key2934, -1)]

def rawRow6564 : Integer.Sparse Key := [(key2382, -4), (key2393, 2), (key2395, 2), (key2379, 2), (key2382, 2), (key2393, -4), (key2882, 2), (key2912, -1), (key2914, -1), (key2774, 2), (key2891, -1), (key2914, -1), (key2771, -1), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, 2), (key2991, -1), (key2993, -1), (key3003, 2), (key2933, -1), (key2934, -1), (key2970, 2), (key2993, 2), (key2996, -1), (key3003, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

def rawRow6565 : Integer.Sparse Key := [(key2382, -4), (key2395, 2), (key2393, 2), (key2382, 2), (key2379, 2), (key2393, -4), (key2882, 2), (key2914, -1), (key2912, -1), (key2774, 2), (key2914, -1), (key2891, -1), (key2774, -1), (key2771, -1), (key2882, -1), (key2848, -1), (key2912, 2), (key2891, 2), (key2993, -1), (key2991, -1), (key3003, 2), (key2934, -1), (key2933, -1), (key2993, 2), (key2970, 2), (key3003, -1), (key2996, -1), (key2933, 2), (key2991, -1), (key2970, -1)]

def rawRow6566 : Integer.Sparse Key := [(key2393, -4), (key2382, 2), (key2395, 2), (key2379, 2), (key2393, 2), (key2382, -4), (key2912, 2), (key2882, -1), (key2914, -1), (key2891, 2), (key2774, -1), (key2914, -1), (key2848, -1), (key2891, -1), (key2771, -1), (key2912, -1), (key2774, 2), (key2882, 2), (key2991, -1), (key3003, -1), (key2993, 2), (key2970, -1), (key2996, -1), (key2933, 2), (key3003, 2), (key2934, -1), (key2993, -1), (key2970, 2), (key2933, -1), (key2991, -1)]

def rawRow6567 : Integer.Sparse Key := [(key2393, -4), (key2395, 2), (key2382, 2), (key2393, 2), (key2379, 2), (key2382, -4), (key2912, 2), (key2914, -1), (key2882, -1), (key2891, 2), (key2914, -1), (key2774, -1), (key2891, -1), (key2848, -1), (key2912, -1), (key2771, -1), (key2882, 2), (key2774, 2), (key3003, -1), (key2991, -1), (key2993, 2), (key2996, -1), (key2970, -1), (key3003, 2), (key2933, 2), (key2993, -1), (key2934, -1), (key2970, 2), (key2991, -1), (key2933, -1)]

def rawRow6568 : Integer.Sparse Key := [(key2395, -4), (key2382, 2), (key2393, 2), (key2382, 2), (key2393, 2), (key2379, -4), (key2914, 2), (key2882, -1), (key2912, -1), (key2914, 2), (key2774, -1), (key2891, -1), (key2882, -1), (key2912, -1), (key2774, -1), (key2891, -1), (key2771, 2), (key2848, 2), (key2993, -1), (key3003, -1), (key2991, 2), (key2993, -1), (key3003, -1), (key2934, 2), (key2996, 2), (key2933, -1), (key2970, -1), (key2991, 2), (key2933, -1), (key2970, -1)]

def rawRow6569 : Integer.Sparse Key := [(key2395, -4), (key2393, 2), (key2382, 2), (key2393, 2), (key2382, 2), (key2379, -4), (key2914, 2), (key2912, -1), (key2882, -1), (key2914, 2), (key2891, -1), (key2774, -1), (key2912, -1), (key2882, -1), (key2891, -1), (key2774, -1), (key2848, 2), (key2771, 2), (key3003, -1), (key2993, -1), (key2991, 2), (key3003, -1), (key2993, -1), (key2996, 2), (key2934, 2), (key2970, -1), (key2933, -1), (key2991, 2), (key2970, -1), (key2933, -1)]

def rawRow6570 : Integer.Sparse Key := [(key2545, -4), (key2539, 2), (key2544, 2), (key2557, 2), (key2565, 2), (key2555, -4), (key2395, 2), (key2382, -1), (key2393, -1), (key2545, 2), (key2410, -1), (key2483, -1), (key2557, -1), (key2565, -1), (key2445, -1), (key2526, -1), (key2441, 2), (key2507, 2), (key2382, -1), (key2393, -1), (key2379, 2), (key2882, -1), (key2912, -1), (key2774, 2), (key2891, 2), (key2771, -1), (key2848, -1), (key2991, 2), (key2933, -1), (key2970, -1)]

def rawRow6571 : Integer.Sparse Key := [(key2545, -4), (key2544, 2), (key2539, 2), (key2565, 2), (key2557, 2), (key2555, -4), (key2395, 2), (key2393, -1), (key2382, -1), (key2545, 2), (key2483, -1), (key2410, -1), (key2565, -1), (key2557, -1), (key2526, -1), (key2445, -1), (key2507, 2), (key2441, 2), (key2393, -1), (key2382, -1), (key2379, 2), (key2912, -1), (key2882, -1), (key2891, 2), (key2774, 2), (key2848, -1), (key2771, -1), (key2991, 2), (key2970, -1), (key2933, -1)]

def rawRow6572 : Integer.Sparse Key := [(key2555, -4), (key2539, 2), (key2557, 2), (key2544, 2), (key2565, 2), (key2545, -4), (key2441, 2), (key2410, -1), (key2445, -1), (key2507, 2), (key2382, -1), (key2557, -1), (key2483, -1), (key2526, -1), (key2393, -1), (key2565, -1), (key2395, 2), (key2545, 2), (key2407, -1), (key2441, -1), (key2410, 2), (key2848, -1), (key2970, -1), (key2592, 2), (key2991, 2), (key2595, -1), (key2882, -1), (key2891, 2), (key2602, -1), (key2912, -1)]

def rawRow6573 : Integer.Sparse Key := [(key2555, -4), (key2557, 2), (key2539, 2), (key2565, 2), (key2544, 2), (key2545, -4), (key2441, 2), (key2445, -1), (key2410, -1), (key2507, 2), (key2557, -1), (key2382, -1), (key2526, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2545, 2), (key2395, 2), (key2441, -1), (key2407, -1), (key2410, 2), (key2970, -1), (key2848, -1), (key2991, 2), (key2592, 2), (key2882, -1), (key2595, -1), (key2891, 2), (key2912, -1), (key2602, -1)]

def rawRow6574 : Integer.Sparse Key := [(key2555, -4), (key2544, 2), (key2565, 2), (key2539, 2), (key2557, 2), (key2545, -4), (key2507, 2), (key2483, -1), (key2526, -1), (key2441, 2), (key2393, -1), (key2565, -1), (key2410, -1), (key2445, -1), (key2382, -1), (key2557, -1), (key2395, 2), (key2545, 2), (key2473, -1), (key2507, -1), (key2483, 2), (key2407, -1), (key2441, -1), (key2592, 2), (key2991, 2), (key2602, -1), (key2912, -1), (key2774, 2), (key2595, -1), (key2882, -1)]

def rawRow6575 : Integer.Sparse Key := [(key2555, -4), (key2565, 2), (key2544, 2), (key2557, 2), (key2539, 2), (key2545, -4), (key2507, 2), (key2526, -1), (key2483, -1), (key2441, 2), (key2565, -1), (key2393, -1), (key2445, -1), (key2410, -1), (key2557, -1), (key2382, -1), (key2545, 2), (key2395, 2), (key2507, -1), (key2473, -1), (key2483, 2), (key2441, -1), (key2407, -1), (key2991, 2), (key2592, 2), (key2912, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2595, -1)]

def rawRow6576 : Integer.Sparse Key := [(key2545, -4), (key2557, 2), (key2565, 2), (key2539, 2), (key2544, 2), (key2555, -4), (key2545, 2), (key2557, -1), (key2565, -1), (key2395, 2), (key2445, -1), (key2526, -1), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, 2), (key2507, 2), (key2539, -1), (key2544, -1), (key2555, 2), (key2382, -1), (key2393, -1), (key2410, 2), (key2483, 2), (key2441, -1), (key2507, -1), (key2379, 2), (key2771, -1), (key2848, -1)]

def rawRow6577 : Integer.Sparse Key := [(key2545, -4), (key2565, 2), (key2557, 2), (key2544, 2), (key2539, 2), (key2555, -4), (key2545, 2), (key2565, -1), (key2557, -1), (key2395, 2), (key2526, -1), (key2445, -1), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, 2), (key2441, 2), (key2544, -1), (key2539, -1), (key2555, 2), (key2393, -1), (key2382, -1), (key2483, 2), (key2410, 2), (key2507, -1), (key2441, -1), (key2379, 2), (key2848, -1), (key2771, -1)]

def rawRow6638 : Integer.Sparse Key := [(key2671, 1), (key2671, 1), (key2676, -2), (key2706, 1), (key2706, 1), (key2726, -2), (key2726, -2), (key2732, 1), (key2732, 1), (key2753, -2), (key2758, 1), (key2758, 1), (key2786, -1), (key2786, -1), (key2798, 1), (key2798, 1), (key2809, -1), (key2809, -1), (key2829, 1), (key2829, 1), (key2870, 1), (key2870, 1), (key2885, -1), (key2885, -1), (key2920, 1), (key2920, 1), (key2927, -1), (key2927, -1), (key3008, 2), (key3010, -1), (key3010, -1), (key3012, 2), (key3017, -1), (key3017, -1), (key3023, -1), (key3023, -1), (key3026, -1), (key3026, -1), (key3030, 2), (key3030, 2)]

def rawRow6639 : Integer.Sparse Key := [(key2671, 1), (key2676, 1), (key2671, -2), (key2726, 1), (key2732, 1), (key2706, -2), (key2732, -2), (key2706, 1), (key2726, 1), (key2758, -2), (key2753, 1), (key2758, 1), (key2794, -1), (key2798, -1), (key2786, 1), (key2794, 1), (key2829, -1), (key2835, -1), (key2809, 1), (key2835, 1), (key2860, 1), (key2885, 1), (key2860, -1), (key2870, -1), (key2923, 1), (key2927, 1), (key2920, -1), (key2923, -1), (key3010, 2), (key3008, -1), (key3010, -1), (key3017, 2), (key3012, -1), (key3017, -1), (key3026, -1), (key3030, -1), (key3023, -1), (key3030, -1), (key3023, 2), (key3026, 2)]

def rawRow6640 : Integer.Sparse Key := [(key2676, 1), (key2671, 1), (key2671, -2), (key2732, 1), (key2726, 1), (key2732, -2), (key2706, -2), (key2726, 1), (key2706, 1), (key2758, -2), (key2758, 1), (key2753, 1), (key2798, -1), (key2794, -1), (key2794, 1), (key2786, 1), (key2835, -1), (key2829, -1), (key2835, 1), (key2809, 1), (key2885, 1), (key2860, 1), (key2870, -1), (key2860, -1), (key2927, 1), (key2923, 1), (key2923, -1), (key2920, -1), (key3010, 2), (key3010, -1), (key3008, -1), (key3017, 2), (key3017, -1), (key3012, -1), (key3030, -1), (key3026, -1), (key3030, -1), (key3023, -1), (key3026, 2), (key3023, 2)]

def rawRow6641 : Integer.Sparse Key := [(key2706, 1), (key2706, 1), (key2753, -2), (key2671, 1), (key2671, 1), (key2726, -2), (key2726, -2), (key2758, 1), (key2758, 1), (key2676, -2), (key2732, 1), (key2732, 1), (key2809, -1), (key2809, -1), (key2920, 1), (key2920, 1), (key2786, -1), (key2786, -1), (key2870, 1), (key2870, 1), (key2829, 1), (key2829, 1), (key2927, -1), (key2927, -1), (key2798, 1), (key2798, 1), (key2885, -1), (key2885, -1), (key3012, 2), (key3023, -1), (key3023, -1), (key3008, 2), (key3026, -1), (key3026, -1), (key3010, -1), (key3010, -1), (key3017, -1), (key3017, -1), (key3030, 2), (key3030, 2)]

def rawRow6642 : Integer.Sparse Key := [(key2706, 1), (key2753, 1), (key2706, -2), (key2726, 1), (key2758, 1), (key2671, -2), (key2758, -2), (key2671, 1), (key2726, 1), (key2732, -2), (key2676, 1), (key2732, 1), (key2860, -1), (key2920, -1), (key2809, 1), (key2860, 1), (key2870, -1), (key2923, -1), (key2786, 1), (key2923, 1), (key2794, 1), (key2927, 1), (key2794, -1), (key2829, -1), (key2835, 1), (key2885, 1), (key2798, -1), (key2835, -1), (key3023, 2), (key3012, -1), (key3023, -1), (key3026, 2), (key3008, -1), (key3026, -1), (key3017, -1), (key3030, -1), (key3010, -1), (key3030, -1), (key3010, 2), (key3017, 2)]

def rawRow6643 : Integer.Sparse Key := [(key2753, 1), (key2706, 1), (key2706, -2), (key2758, 1), (key2726, 1), (key2758, -2), (key2671, -2), (key2726, 1), (key2671, 1), (key2732, -2), (key2732, 1), (key2676, 1), (key2920, -1), (key2860, -1), (key2860, 1), (key2809, 1), (key2923, -1), (key2870, -1), (key2923, 1), (key2786, 1), (key2927, 1), (key2794, 1), (key2829, -1), (key2794, -1), (key2885, 1), (key2835, 1), (key2835, -1), (key2798, -1), (key3023, 2), (key3023, -1), (key3012, -1), (key3026, 2), (key3026, -1), (key3008, -1), (key3030, -1), (key3017, -1), (key3030, -1), (key3010, -1), (key3017, 2), (key3010, 2)]

def rawRow6644 : Integer.Sparse Key := [(key2726, 1), (key2732, 1), (key2758, -2), (key2671, 1), (key2676, 1), (key2706, -2), (key2732, -2), (key2753, 1), (key2758, 1), (key2671, -2), (key2706, 1), (key2726, 1), (key2829, -1), (key2835, -1), (key2923, 1), (key2927, 1), (key2794, -1), (key2798, -1), (key2860, 1), (key2885, 1), (key2809, 1), (key2835, 1), (key2920, -1), (key2923, -1), (key2786, 1), (key2794, 1), (key2860, -1), (key2870, -1), (key3017, 2), (key3026, -1), (key3030, -1), (key3010, 2), (key3023, -1), (key3030, -1), (key3008, -1), (key3010, -1), (key3012, -1), (key3017, -1), (key3023, 2), (key3026, 2)]

def rawRow6645 : Integer.Sparse Key := [(key2732, 1), (key2726, 1), (key2758, -2), (key2676, 1), (key2671, 1), (key2732, -2), (key2706, -2), (key2758, 1), (key2753, 1), (key2671, -2), (key2726, 1), (key2706, 1), (key2835, -1), (key2829, -1), (key2927, 1), (key2923, 1), (key2798, -1), (key2794, -1), (key2885, 1), (key2860, 1), (key2835, 1), (key2809, 1), (key2923, -1), (key2920, -1), (key2794, 1), (key2786, 1), (key2870, -1), (key2860, -1), (key3017, 2), (key3030, -1), (key3026, -1), (key3010, 2), (key3030, -1), (key3023, -1), (key3010, -1), (key3008, -1), (key3017, -1), (key3012, -1), (key3026, 2), (key3023, 2)]

def rawRow6646 : Integer.Sparse Key := [(key2726, 1), (key2758, 1), (key2732, -2), (key2706, 1), (key2753, 1), (key2671, -2), (key2758, -2), (key2676, 1), (key2732, 1), (key2706, -2), (key2671, 1), (key2726, 1), (key2870, -1), (key2923, -1), (key2835, 1), (key2885, 1), (key2860, -1), (key2920, -1), (key2794, 1), (key2927, 1), (key2786, 1), (key2923, 1), (key2798, -1), (key2835, -1), (key2809, 1), (key2860, 1), (key2794, -1), (key2829, -1), (key3026, 2), (key3017, -1), (key3030, -1), (key3023, 2), (key3010, -1), (key3030, -1), (key3012, -1), (key3023, -1), (key3008, -1), (key3026, -1), (key3010, 2), (key3017, 2)]

def rawRow6647 : Integer.Sparse Key := [(key2758, 1), (key2726, 1), (key2732, -2), (key2753, 1), (key2706, 1), (key2758, -2), (key2671, -2), (key2732, 1), (key2676, 1), (key2706, -2), (key2726, 1), (key2671, 1), (key2923, -1), (key2870, -1), (key2885, 1), (key2835, 1), (key2920, -1), (key2860, -1), (key2927, 1), (key2794, 1), (key2923, 1), (key2786, 1), (key2835, -1), (key2798, -1), (key2860, 1), (key2809, 1), (key2829, -1), (key2794, -1), (key3026, 2), (key3030, -1), (key3017, -1), (key3023, 2), (key3030, -1), (key3010, -1), (key3023, -1), (key3012, -1), (key3026, -1), (key3008, -1), (key3017, 2), (key3010, 2)]

def rawRow6648 : Integer.Sparse Key := [(key2732, 1), (key2758, 1), (key2726, -2), (key2732, 1), (key2758, 1), (key2676, -2), (key2753, -2), (key2671, 1), (key2706, 1), (key2726, -2), (key2671, 1), (key2706, 1), (key2885, -1), (key2927, -1), (key2829, 1), (key2870, 1), (key2885, -1), (key2927, -1), (key2798, 1), (key2920, 1), (key2798, 1), (key2920, 1), (key2786, -1), (key2809, -1), (key2829, 1), (key2870, 1), (key2786, -1), (key2809, -1), (key3030, 2), (key3017, -1), (key3026, -1), (key3030, 2), (key3010, -1), (key3023, -1), (key3017, -1), (key3026, -1), (key3010, -1), (key3023, -1), (key3008, 2), (key3012, 2)]

def rawRow6649 : Integer.Sparse Key := [(key2758, 1), (key2732, 1), (key2726, -2), (key2758, 1), (key2732, 1), (key2753, -2), (key2676, -2), (key2706, 1), (key2671, 1), (key2726, -2), (key2706, 1), (key2671, 1), (key2927, -1), (key2885, -1), (key2870, 1), (key2829, 1), (key2927, -1), (key2885, -1), (key2920, 1), (key2798, 1), (key2920, 1), (key2798, 1), (key2809, -1), (key2786, -1), (key2870, 1), (key2829, 1), (key2809, -1), (key2786, -1), (key3030, 2), (key3026, -1), (key3017, -1), (key3030, 2), (key3023, -1), (key3010, -1), (key3026, -1), (key3017, -1), (key3023, -1), (key3010, -1), (key3012, 2), (key3008, 2)]

def rawRow6650 : Integer.Sparse Key := [(key2628, 1), (key2628, 1), (key2641, -2), (key2702, 1), (key2702, 1), (key2972, -2), (key2972, -2), (key2976, 1), (key2976, 1), (key2728, -2), (key2983, 1), (key2983, 1), (key2612, -1), (key2616, -1), (key2660, 1), (key2660, 1), (key2671, -1), (key2671, -1), (key2726, 1), (key2726, 1), (key2829, 1), (key2829, 1), (key2927, -1), (key2927, -1), (key3010, 1), (key3010, 1), (key3030, -1), (key3030, -1), (key2621, 2), (key2644, -1), (key2644, -1), (key2676, 2), (key2732, -1), (key2732, -1), (key2798, -1), (key2798, -1), (key2835, -1), (key2835, -1), (key2885, 2), (key2885, 2)]

def rawRow6651 : Integer.Sparse Key := [(key2628, 1), (key2641, 1), (key2628, -2), (key2972, 1), (key2976, 1), (key2702, -2), (key2976, -2), (key2702, 1), (key2972, 1), (key2983, -2), (key2728, 1), (key2983, 1), (key2646, -1), (key2653, -1), (key2616, 1), (key2640, 1), (key2726, -1), (key2758, -1), (key2671, 1), (key2758, 1), (key2794, 1), (key2927, 1), (key2794, -1), (key2829, -1), (key3017, 1), (key3030, 1), (key3010, -1), (key3017, -1), (key2644, 2), (key2621, -1), (key2644, -1), (key2732, 2), (key2676, -1), (key2732, -1), (key2835, -1), (key2885, -1), (key2798, -1), (key2885, -1), (key2798, 2), (key2835, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row103 : Integer.Sparse (Fin 3237) := [(677, 1), (913, 3), (950, 1), (1622, 1), (2832, -1)]

end MUB6.Certificate.MixedData

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

def nodeValue1001 : Sparse Master := [(Sum.inr 1001, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


