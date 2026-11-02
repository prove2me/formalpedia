-- Prove2me | Definitions.Def_OAIQ106D093
-- name    : OAIQ106D093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:56:31.441183+00:00
-- url     : https://prove2.me/theorems/460c54ef-74af-4faa-8b39-36cc2616ed5a
-- title:
--   Definitions bundle OAIQ106D093 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 545 declarations of OpenAI's Lean: 545 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.key1363`, `OAI.MUB6.Certificate.GramRows.key1369`, `OAI.MUB6.Certificate.GramRows.key1378`, `OAI.MUB6.Certificate.GramRows.key1518`, `OAI.MUB6.Certificate.GramRows.key1746`, `OAI.MUB6.Certificate.GramRows.key1879`, `OAI.MUB6.Certificate.GramRows.key2821`, `OAI.MUB6.Certificate.GramRows.row13599`, `OAI.MUB6.Certificate.GramRows.row13600`, `OAI.MUB6.Certificate.GramRows.row13601`, `OAI.MUB6.Certificate.GramRows.row13620`, `OAI.MUB6.Certificate.GramRows.row13621`, `OAI.MUB6.Certificate.GramRows.row13622`, `OAI.MUB6.Certificate.GramRows.row13809`, `OAI.MUB6.Certificate.GramRows.row13810`, `OAI.MUB6.Certificate.GramRows.row13811`, `OAI.MUB6.Certificate.GramRows.row13812`, `OAI.MUB6.Certificate.GramRows.row13813`, `OAI.MUB6.Certificate.GramRows.row13814`, `OAI.MUB6.Certificate.GramRows.row13815`, `OAI.MUB6.Certificate.GramRows.row13816`, `OAI.MUB6.Certificate.GramRows.row13817`, `OAI.MUB6.Certificate.GramRows.row13818`, `OAI.MUB6.Certificate.GramRows.row13819`, `OAI.MUB6.Certificate.GramRows.row13820`, `OAI.MUB6.Certificate.GramRows.row13821`, `OAI.MUB6.Certificate.GramRows.row13822`, `OAI.MUB6.Certificate.GramRows.row13823`, `OAI.MUB6.Certificate.GramRows.row13824`, `OAI.MUB6.Certificate.GramRows.row13825`, `OAI.MUB6.Certificate.GramRows.row13826`, `OAI.MUB6.Certificate.GramRows.row13827`, `OAI.MUB6.Certificate.GramRows.row13828`, `OAI.MUB6.Certificate.GramRows.row13829`, `OAI.MUB6.Certificate.GramRows.row13836`, `OAI.MUB6.Certificate.GramRows.row13837`, `OAI.MUB6.Certificate.GramRows.row13838`, `OAI.MUB6.Certificate.GramRows.row15285`, `OAI.MUB6.Certificate.GramRows.row15286`, `OAI.MUB6.Certificate.GramRows.row15287` and 505 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block22`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block131`, `MutuallyUnbiased_GramRows_Block132`, `MutuallyUnbiased_GramRows_Block143`, `MutuallyUnbiased_GramRows_Block145`, `MutuallyUnbiased_GramRows_Block146`, `MutuallyUnbiased_GramRows_Block147`, `MutuallyUnbiased_GramRows_Block148`, `MutuallyUnbiased_GramRows_Block149`, `MutuallyUnbiased_GramRows_Block150`, `MutuallyUnbiased_GramRows_Block152`, `MutuallyUnbiased_GramRows_Block153`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values19`, `MutuallyUnbiased_MixedSemantics_Values25`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D151`, `OAIQ106D155`, `OAIQ106D157` and `OAIQ106D162`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1363 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key1369 : Key := ⟨0, 1, [(-2, -2), (0, -1), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key1378 : Key := ⟨0, 1, [(-2, -2), (0, 0), (0, 1), (0, 1), (0, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1518 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 1), (0, 1), (0, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1746 : Key := ⟨0, 1, [(-2, 0), (0, -1), (0, 1), (0, 1), (0, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1879 : Key := ⟨0, 1, [(-2, 1), (0, -1), (0, 0), (0, 1), (0, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2821 : Key := ⟨1, 1, [(-2, 0), (-1, -1), (0, -1), (1, -1), (1, 0), (1, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13599 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

def row13600 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

def row13601 : Integer.Sparse Key := [(key2587, -4), (key2593, 4), (key2598, 4), (key2600, -4), (key2843, -4), (key2887, 8), (key2889, -4), (key2966, -4), (key2968, 8), (key2995, -4)]

def row13620 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

def row13621 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

def row13622 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2472, -4), (key2480, 8), (key2484, -4), (key2503, -4), (key2509, 8), (key2524, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13809 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13810 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13811 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13812 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13813 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13814 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, 2), (key2919, -1), (key2922, 1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row13815 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

def row13816 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

def row13817 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2704, 4), (key2752, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2918, -2), (key2919, 4), (key3021, 4), (key3022, -2)]

def row13818 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13819 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13820 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13821 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13822 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

def row13823 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 2), (key2704, -1), (key2724, 1), (key2752, -1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, 1), (key2851, -1), (key2858, 1), (key2868, -2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 4), (key3025, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13824 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13825 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13826 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 4), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13827 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 4), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13828 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13829 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -4), (key2659, 2), (key2663, 2), (key2669, -2), (key2698, -2), (key2704, 2), (key2724, -4), (key2757, 2), (key2784, 2), (key2792, -2), (key2827, -2), (key2868, 2), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, -2), (key3025, -2)]

def row13836 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

def row13837 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

def row13838 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2630, 4), (key2638, -2), (key2657, -2), (key2659, 2), (key2698, -2), (key2784, 4), (key2792, -2), (key2801, 4), (key2807, -2), (key2827, -2), (key2851, -2), (key2858, -2), (key2868, 4), (key2918, -2), (key2919, 4), (key2922, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block143
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15285 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15286 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15287 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15288 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15289 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15290 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15291 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15292 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15293 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -1), (key2704, 2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, 1), (key2784, -2), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -1), (key2868, -2), (key2918, -1), (key2919, 2), (key2922, 1), (key3007, 1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, 2), (key3022, -1), (key3025, 1)]

def row15294 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15295 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15296 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, -2), (key2919, -2), (key2922, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, -2)]

def row15297 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15298 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15299 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15300 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15301 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

def row15302 : Integer.Sparse Key := [(key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, 2), (key2784, -1), (key2792, 1), (key2801, 2), (key2807, -1), (key2827, 1), (key2851, -1), (key2858, -2), (key2868, 1), (key2919, 2), (key2922, 2), (key3007, -1), (key3009, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, -2), (key3025, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15505 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15506 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, 2), (key2503, -2), (key2509, -2), (key2524, -2), (key2587, -2), (key2593, -2), (key2600, -2), (key2766, -1), (key2772, -1), (key2843, -1), (key2880, -1), (key2889, -1), (key2910, -1), (key2929, -1), (key2931, 3), (key2966, -1), (key2968, 4), (key2989, 3), (key2995, -1), (key3002, -1)]

def row15507 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15508 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15509 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15510 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15511 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15512 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2443, 2), (key2472, 2), (key2480, -2), (key2484, -2), (key2503, 2), (key2509, 2), (key2524, -2), (key2587, -1), (key2593, -1), (key2598, -1), (key2600, 3), (key2766, -2), (key2772, -2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 4), (key2910, 3), (key2931, -2), (key2968, -1), (key2989, -1), (key2995, -1), (key3002, -1)]

def row15513 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15514 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15515 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15516 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15517 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15518 : Integer.Sparse Key := [(key2472, -2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 4), (key2587, -2), (key2593, 4), (key2600, -2), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2889, -2), (key2910, -2), (key2931, -2), (key2968, -2), (key2989, -2)]

def row15519 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15520 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15521 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -2), (key2704, -2), (key2724, -2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15522 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15523 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15524 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15525 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15526 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15527 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, 1), (key2704, 2), (key2724, -1), (key2752, 1), (key2757, -1), (key2778, 1), (key2784, -1), (key2792, 2), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key2918, -2), (key2919, 1), (key2922, 1)]

def row15528 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15529 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15530 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, -2), (key2630, -2), (key2638, -2), (key2663, 2), (key2669, 4), (key2698, -4), (key2704, -4), (key2724, -2), (key2752, -2), (key2801, -2), (key2807, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4)]

def row15531 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15532 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15533 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15534 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2858, -1), (key2868, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15535 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15536 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 2), (key2704, 1), (key2724, 3), (key2752, -1), (key2757, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2858, -1), (key2868, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row15537 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15538 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15539 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15540 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15541 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15542 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, -1), (key2698, -2), (key2704, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, 4), (key2784, 2), (key2792, 4), (key2801, 1), (key2807, -1), (key2827, 2), (key2851, -2), (key2858, -2), (key2918, -1), (key2919, 1), (key2922, 2), (key3021, -1), (key3022, -1)]

def row15543 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15544 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15545 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15546 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15547 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15548 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, 1), (key2630, -1), (key2638, 2), (key2663, -1), (key2669, -1), (key2698, 3), (key2704, 2), (key2724, 3), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, 2), (key2827, 1), (key2851, -2), (key2868, -2), (key2918, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -1), (key3022, 2), (key3025, 1)]

def row15549 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15550 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15551 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 4), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15552 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 4), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15553 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15554 : Integer.Sparse Key := [(key2608, 2), (key2624, -2), (key2638, -2), (key2659, 2), (key2663, 2), (key2698, -2), (key2724, -2), (key2757, 2), (key2778, -2), (key2792, -2), (key2801, -2), (key2827, -2), (key2851, 4), (key2858, 4), (key2868, 4), (key2919, -2), (key2922, -2), (key3009, 2), (key3016, 2), (key3022, -2), (key3025, -2)]

def row15555 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

def row15556 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

def row15557 : Integer.Sparse Key := [(key2766, -4), (key2772, 4), (key2843, -4), (key2887, -4), (key2889, 8), (key2929, 4), (key2931, -4), (key2966, 8), (key2968, -4), (key2995, -4)]

def row15558 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

def row15559 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

def row15560 : Integer.Sparse Key := [(key2406, -4), (key2411, 4), (key2437, 4), (key2443, -4), (key2472, -4), (key2480, -4), (key2484, 8), (key2503, 8), (key2509, -4), (key2524, -4)]

def row15591 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

def row15592 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

def row15593 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2752, -2), (key2778, -2), (key2784, 4), (key2792, -2), (key2801, -2), (key2807, 4), (key2851, -2), (key2858, -2), (key2918, 4), (key2919, -2), (key3007, -2), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, 4)]

def row15594 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

def row15595 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

def row15596 : Integer.Sparse Key := [(key2663, 2), (key2669, -2), (key2698, 4), (key2704, 4), (key2724, -2), (key2752, -2), (key2757, 2), (key2778, -2), (key2784, -2), (key2792, -2), (key2801, -2), (key2807, 4), (key2827, -2), (key2851, -2), (key2858, 4), (key2868, -2), (key2918, -2), (key2919, -2), (key2922, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block146
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15633 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15634 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15635 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15636 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15637 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15638 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15639 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15640 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15641 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

def row15642 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15643 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15644 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

def row15657 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

def row15658 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

def row15659 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

def row15660 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

def row15661 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

def row15662 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

def row15663 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

def row15664 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

def row15665 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

def row15666 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

def row15667 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

def row15668 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

def row15669 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

def row15670 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

def row15671 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

def row15672 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row15673 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row15674 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row15675 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

def row15676 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

def row15677 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

def row15678 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

def row15679 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

def row15680 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

def row15681 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15682 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15683 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15684 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15685 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15686 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

def row15687 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

def row15688 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

def row15689 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

def row15690 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15691 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15692 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15693 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15694 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15695 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

def row15696 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

def row15697 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

def row15698 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

def row15699 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15700 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15701 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15702 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15703 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15704 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

def row15705 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15706 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15707 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2918, -1), (key2919, 2), (key2922, -1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15708 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2918, -1), (key2919, 2), (key2922, -1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15709 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15710 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

def row15711 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

def row15712 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

def row15713 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

def row15714 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

def row15715 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

def row15716 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

def row15717 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15718 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15719 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15720 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15721 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15722 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15723 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15724 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15725 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15726 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15727 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15728 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15729 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15730 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15731 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

def row15732 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15733 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

def row15734 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block147
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15825 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15826 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15827 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15828 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15829 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15830 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15831 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15832 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15833 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15834 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15835 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15836 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15837 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15838 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15839 : Integer.Sparse Key := [(key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 2), (key2806, -1), (key2826, -1), (key2852, -1), (key2857, -1), (key2867, 2), (key2894, -1), (key2896, 2), (key2903, -1), (key2937, 1), (key2942, -1), (key2949, 1), (key2959, -1), (key2973, -2), (key2975, 1), (key2982, 1)]

def row15840 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15841 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

def row15842 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, 4), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, 4), (key2826, -2), (key2852, -2), (key2857, 4), (key2867, -2), (key2894, -2), (key2896, -2), (key2903, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block148
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row15897 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15898 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15899 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15900 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15901 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15902 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -1), (key2701, 2), (key2722, 1), (key2734, -1), (key2745, -1), (key2778, 1), (key2781, -2), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -1), (key2866, -2), (key2892, -1), (key2895, 2), (key2902, 1), (key2935, 1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, 2), (key2974, -1), (key2981, 1)]

def row15903 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

def row15904 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

def row15905 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2734, -2), (key2778, -2), (key2781, 4), (key2790, -2), (key2801, -2), (key2804, 4), (key2851, -2), (key2856, -2), (key2892, 4), (key2895, -2), (key2935, -2), (key2941, 2), (key2947, -2), (key2971, -2), (key2974, 4)]

def row15906 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15907 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15908 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15909 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15910 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15911 : Integer.Sparse Key := [(key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, 3), (key2734, -1), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, 1), (key2801, 2), (key2804, -1), (key2825, 1), (key2851, -1), (key2856, -2), (key2866, 1), (key2895, 2), (key2902, 2), (key2935, -1), (key2941, -1), (key2947, -1), (key2958, -1), (key2971, -1), (key2974, -2), (key2981, 1)]

def row15912 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

def row15913 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

def row15914 : Integer.Sparse Key := [(key2663, 2), (key2666, -2), (key2698, 4), (key2701, 4), (key2722, -2), (key2734, -2), (key2745, 2), (key2778, -2), (key2781, -2), (key2790, -2), (key2801, -2), (key2804, 4), (key2825, -2), (key2851, -2), (key2856, 4), (key2866, -2), (key2892, -2), (key2895, -2), (key2902, 4)]

def row15951 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15952 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15953 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15954 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15955 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15956 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15957 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15958 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15959 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15960 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15961 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15962 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15963 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15964 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15965 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15966 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15967 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15968 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15969 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15970 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15971 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15972 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15973 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15974 : Integer.Sparse Key := [(key2381, -2), (key2390, 2), (key2406, -1), (key2409, -1), (key2437, -1), (key2440, 3), (key2472, 1), (key2480, 2), (key2482, 1), (key2503, -3), (key2506, 2), (key2522, -3), (key2538, -1), (key2543, -1), (key2554, 3), (key2563, -1)]

def row15975 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15976 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15977 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15978 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15979 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15980 : Integer.Sparse Key := [(key2378, -1), (key2381, -1), (key2390, -1), (key2392, 3), (key2409, -2), (key2437, 2), (key2472, 1), (key2480, -3), (key2482, 2), (key2503, 2), (key2506, 1), (key2522, -3), (key2538, -1), (key2543, 3), (key2554, -1), (key2563, -1)]

def row15981 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15982 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15983 : Integer.Sparse Key := [(key2378, -4), (key2381, 2), (key2390, -2), (key2392, 4), (key2406, -2), (key2437, 4), (key2440, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2506, -2), (key2522, -2), (key2538, 2), (key2543, 4), (key2554, -4), (key2563, -2)]

def row15984 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15985 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15986 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2392, -2), (key2406, -4), (key2409, 2), (key2437, -2), (key2440, 4), (key2472, -2), (key2480, 8), (key2482, -2), (key2503, -2), (key2522, -2), (key2538, 2), (key2543, -4), (key2554, 4), (key2563, -2)]

def row15987 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15988 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15989 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15990 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15991 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15992 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row15993 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row15994 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row15995 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row15996 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row15997 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row15998 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row15999 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block149
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16000 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16001 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16002 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16003 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16004 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16005 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16006 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16007 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16008 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16009 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16010 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, -1), (key2736, 2), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, 1), (key2806, -1), (key2852, -2), (key2857, -2), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, -1), (key2949, 2), (key2973, -1), (key2975, 1)]

def row16011 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16012 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16013 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16014 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16015 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16016 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, -1), (key2647, 2), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2852, -2), (key2867, -2), (key2894, -1), (key2903, 1), (key2937, 2), (key2949, -1), (key2959, -1), (key2973, -1), (key2982, 1)]

def row16017 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row16018 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row16019 : Integer.Sparse Key := [(key2613, -2), (key2629, -2), (key2637, -2), (key2647, 4), (key2652, 2), (key2668, -2), (key2703, 4), (key2736, -2), (key2783, -2), (key2791, -2), (key2806, 4), (key2857, 4), (key2894, -2), (key2896, -2), (key2937, 4), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, -2)]

def row16020 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16021 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16022 : Integer.Sparse Key := [(key2613, -2), (key2629, 4), (key2647, -2), (key2668, -2), (key2703, -2), (key2723, -2), (key2736, 4), (key2746, 2), (key2783, 4), (key2806, -2), (key2826, -2), (key2867, 4), (key2894, -2), (key2903, -2), (key2937, -2), (key2949, 4), (key2959, 2), (key2973, -2), (key2982, -2)]

def row16023 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16024 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16025 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16026 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16027 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16028 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16029 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16030 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16031 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16032 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16033 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16034 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16035 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16036 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16037 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16038 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16039 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16040 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16041 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16042 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16043 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16044 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16045 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16046 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, -1), (key2629, 2), (key2637, -1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, 1), (key2723, -2), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, -1), (key2826, 2), (key2894, -1), (key2896, -1), (key2903, 2), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, 1), (key2982, -2)]

def row16047 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16048 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16049 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16050 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16051 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16052 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, 1), (key2637, -2), (key2664, -1), (key2668, 1), (key2699, -1), (key2703, 2), (key2723, -1), (key2736, 1), (key2746, -1), (key2779, -1), (key2783, -1), (key2791, 2), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -1), (key2896, 2), (key2903, -1), (key2949, -1), (key2959, 1), (key2973, 1), (key2975, -2), (key2982, 1)]

def row16053 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16054 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16055 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, 4), (key2629, -2), (key2637, -2), (key2664, -2), (key2668, 2), (key2736, 2), (key2746, -2), (key2779, -4), (key2783, 2), (key2791, 2), (key2894, 2), (key2896, 2), (key2903, -4), (key2949, -2), (key2959, 2), (key2973, -2), (key2975, -2), (key2982, 4)]

def row16056 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16057 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16058 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2647, 2), (key2652, -2), (key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2723, -2), (key2802, -4), (key2806, 2), (key2826, 2), (key2894, 2), (key2896, -4), (key2903, 2), (key2937, -2), (key2942, 2), (key2973, -2), (key2975, 4), (key2982, -2)]

def row16059 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16060 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16061 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16062 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16063 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16064 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 1), (key2701, -2), (key2722, -1), (key2734, 1), (key2745, 1), (key2778, 1), (key2781, 1), (key2801, -1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, -1), (key2902, 1), (key2935, -2), (key2947, 2), (key2974, 2), (key2981, -2)]

def row16065 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

def row16066 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

def row16067 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2701, 2), (key2734, 2), (key2790, 2), (key2825, -2), (key2856, 2), (key2866, -2), (key2895, 2), (key2902, -2), (key2941, -2), (key2958, 2), (key2974, -4), (key2981, 4)]

def row16068 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16069 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16070 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16071 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16072 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16073 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2645, -2), (key2663, -1), (key2666, 1), (key2698, -2), (key2701, 1), (key2722, -1), (key2734, 3), (key2745, -1), (key2801, 1), (key2804, -2), (key2825, -1), (key2856, -1), (key2866, 1), (key2895, 2), (key2902, -2), (key2947, 1), (key2958, 1), (key2974, -1), (key2981, 1)]

def row16074 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

def row16075 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

def row16076 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2636, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -4), (key2745, 2), (key2801, -4), (key2804, 2), (key2825, 2), (key2856, 2), (key2866, -2), (key2895, -4), (key2902, 4), (key2974, 2), (key2981, -2)]

def row16077 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16078 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16079 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16080 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16081 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16082 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, -1), (key2627, 2), (key2636, 1), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, 2), (key2701, -1), (key2722, -3), (key2734, 1), (key2745, 1), (key2801, -1), (key2804, -1), (key2825, 2), (key2892, -1), (key2895, -1), (key2902, 2), (key2971, 1), (key2974, 1), (key2981, -2)]

def row16083 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16084 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16085 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2892, -1), (key2895, 2), (key2902, -1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16086 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2892, -1), (key2895, 2), (key2902, -1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16087 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16088 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, 1), (key2627, 1), (key2636, -2), (key2663, -1), (key2666, 1), (key2698, -1), (key2722, -1), (key2734, -1), (key2745, -1), (key2778, -1), (key2781, 1), (key2790, 4), (key2801, 1), (key2804, -2), (key2825, -1), (key2892, -1), (key2895, 2), (key2902, -1), (key2947, 1), (key2958, 1), (key2971, 1), (key2974, -2), (key2981, 1)]

def row16089 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

def row16090 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

def row16091 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, 4), (key2627, -2), (key2636, -2), (key2663, -2), (key2666, 2), (key2698, -4), (key2734, 2), (key2745, -2), (key2781, 2), (key2790, 2), (key2892, 2), (key2895, 2), (key2902, -4), (key2947, -2), (key2958, 2), (key2971, -2), (key2974, -2), (key2981, 4)]

def row16092 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

def row16093 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

def row16094 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2645, 2), (key2651, -2), (key2663, 2), (key2666, -2), (key2698, 4), (key2701, -2), (key2722, -2), (key2801, -4), (key2804, 2), (key2825, 2), (key2892, 2), (key2895, -4), (key2902, 2), (key2935, -2), (key2941, 2), (key2971, -2), (key2974, 4), (key2981, -2)]

def row16095 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16096 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16097 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16098 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16099 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16100 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16101 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16102 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16103 : Integer.Sparse Key := [(key2592, -2), (key2595, 2), (key2602, 2), (key2603, -2), (key2848, -2), (key2882, -2), (key2891, 2), (key2912, 4), (key2914, -2), (key2970, 2), (key2991, -2), (key2993, 4), (key2996, -2), (key3003, -2)]

def row16104 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16105 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16106 : Integer.Sparse Key := [(key2592, 4), (key2595, -4), (key2602, -4), (key2603, 4), (key2882, -4), (key2912, -4), (key2914, 8), (key2991, 8), (key2993, -4), (key3003, -4)]

def row16107 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 4), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16108 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 4), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16109 : Integer.Sparse Key := [(key2393, 4), (key2407, -2), (key2441, 2), (key2565, 4), (key2592, -2), (key2595, 2), (key2602, -2), (key2603, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16110 : Integer.Sparse Key := [(key2393, 4), (key2407, -2), (key2441, 2), (key2565, 4), (key2592, -2), (key2595, 2), (key2602, -2), (key2603, -2), (key2774, 2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, -2), (key2991, -2), (key2993, -2)]

def row16111 : Integer.Sparse Key := [(key2379, -2), (key2393, 2), (key2441, 2), (key2544, -2), (key2555, -2), (key2565, 4), (key2595, 2), (key2603, -2), (key2771, -2), (key2774, 2), (key2882, 4), (key2914, -2), (key2934, -2), (key2993, -2)]

def row16112 : Integer.Sparse Key := [(key2393, 2), (key2407, -2), (key2441, 2), (key2544, -2), (key2555, -2), (key2565, 4), (key2592, -2), (key2595, 2), (key2603, -2), (key2774, 2), (key2882, 4), (key2914, -2), (key2934, -2), (key2993, -2)]

def row16113 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16114 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16115 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16116 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16117 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16118 : Integer.Sparse Key := [(key2382, 4), (key2393, -2), (key2395, -2), (key2483, -2), (key2507, 4), (key2526, -2), (key2545, -2), (key2557, 4), (key2565, -2), (key2592, -2), (key2595, -2), (key2602, 4), (key2848, -2), (key2882, -2), (key2891, 4), (key2912, 4), (key2970, -2), (key2991, -2)]

def row16119 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 4), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2933, -2), (key2991, -2)]

def row16120 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 4), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2933, -2), (key2991, -2)]

def row16121 : Integer.Sparse Key := [(key2382, -2), (key2393, 4), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2602, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2991, -2)]

def row16122 : Integer.Sparse Key := [(key2382, -2), (key2393, 4), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2545, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2602, -2), (key2774, 4), (key2882, 4), (key2912, -2), (key2991, -2)]

def row16123 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2393, 2), (key2395, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2544, -2), (key2545, -2), (key2555, -2), (key2557, -2), (key2565, 4), (key2595, 4), (key2771, -2), (key2774, 4), (key2882, 4)]

def row16124 : Integer.Sparse Key := [(key2382, -2), (key2393, 2), (key2395, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, -2), (key2544, -2), (key2545, -2), (key2555, -2), (key2557, -2), (key2565, 4), (key2592, -2), (key2595, 4), (key2774, 4), (key2882, 4)]

def row16125 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4), (key2848, 4)]

def row16126 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4), (key2848, 4)]

def row16127 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4), (key2848, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16128 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4), (key2848, 4)]

def row16129 : Integer.Sparse Key := [(key2379, 4), (key2382, -4), (key2393, -4), (key2395, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2473, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2771, 4)]

def row16130 : Integer.Sparse Key := [(key2382, -4), (key2393, -4), (key2395, 4), (key2407, 4), (key2410, -4), (key2441, -4), (key2445, 4), (key2473, 4), (key2483, -4), (key2507, -4), (key2526, 4), (key2592, 4)]

def row16170 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16455 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16456 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16457 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16458 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16459 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16460 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16461 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16462 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16463 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16464 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16465 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16466 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2726, 4), (key2729, -2), (key2748, -2), (key2829, -2), (key2832, 4), (key2870, -2), (key2883, -2), (key2905, 4), (key2913, -2), (key2961, -2), (key2984, -2), (key2992, 4)]

def row16467 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16468 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16469 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16470 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16471 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16472 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16473 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16474 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16475 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16476 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16477 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16478 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2809, 1), (key2829, 2), (key2832, -1), (key2860, -2), (key2870, -1), (key2883, -1), (key2898, 1), (key2905, -1), (key2913, 2), (key2951, -1), (key2961, -1), (key2977, 1), (key2984, 2), (key2992, -1)]

def row16479 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16480 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16481 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16482 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16483 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16484 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, -2), (key2796, 1), (key2829, -1), (key2832, -1), (key2870, 2), (key2883, 2), (key2905, -1), (key2913, -1), (key2939, -1), (key2944, 1), (key2961, 2), (key2984, -1), (key2992, -1)]

def row16485 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16486 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16487 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16488 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16489 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

def row16490 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, -2), (key2860, 4), (key2898, -2), (key2939, 2), (key2944, -2), (key2951, 2), (key2977, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16527 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

def row16528 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

def row16529 : Integer.Sparse Key := [(key2407, 2), (key2410, -4), (key2441, 4), (key2445, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2848, 2), (key2882, -2), (key2891, -4), (key2912, -2), (key2914, 8), (key2970, 4), (key2993, -2), (key2996, -2), (key3003, -2)]

def row16530 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16531 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16532 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16533 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16534 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16535 : Integer.Sparse Key := [(key2407, -2), (key2445, 2), (key2592, -1), (key2595, -1), (key2602, 3), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 3), (key2912, 2), (key2914, -3), (key2970, -1), (key2991, 1), (key2993, 2), (key2996, -1), (key3003, -3)]

def row16536 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

def row16537 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

def row16538 : Integer.Sparse Key := [(key2407, 2), (key2441, 4), (key2473, 2), (key2483, -4), (key2507, 4), (key2526, -2), (key2595, -2), (key2602, -2), (key2603, 4), (key2774, -4), (key2882, -2), (key2912, -2), (key2914, 8), (key2934, -2), (key2993, -2), (key3003, -2)]

def row16539 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2933, -1), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16540 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2933, -1), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16541 : Integer.Sparse Key := [(key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2592, -1), (key2595, 3), (key2602, -1), (key2603, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16542 : Integer.Sparse Key := [(key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 2), (key2555, 2), (key2565, 2), (key2592, -1), (key2595, 3), (key2602, -1), (key2603, -1), (key2774, 3), (key2882, 2), (key2912, -1), (key2914, -3), (key2934, -1), (key2991, -1), (key2993, -3)]

def row16543 : Integer.Sparse Key := [(key2379, -1), (key2393, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 1), (key2555, 1), (key2565, 2), (key2595, 3), (key2603, -1), (key2771, -1), (key2774, 3), (key2882, 2), (key2914, -3), (key2934, -1), (key2993, -3)]

def row16544 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, -1), (key2473, -2), (key2526, 2), (key2544, 1), (key2555, 1), (key2565, 2), (key2592, -1), (key2595, 3), (key2603, -1), (key2774, 3), (key2882, 2), (key2914, -3), (key2934, -1), (key2993, -3)]

def row16545 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16546 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16547 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16548 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16549 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16550 : Integer.Sparse Key := [(key2393, -1), (key2395, -1), (key2407, -2), (key2445, 2), (key2483, -1), (key2526, -1), (key2539, 2), (key2544, -2), (key2545, -3), (key2555, 2), (key2557, 2), (key2565, -3), (key2592, -1), (key2595, -1), (key2602, 4), (key2848, -1), (key2882, -1), (key2891, 4), (key2912, 4), (key2970, -1), (key2991, -1)]

def row16551 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2933, -1), (key2991, -1)]

def row16552 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2933, -1), (key2991, -1)]

def row16553 : Integer.Sparse Key := [(key2382, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2602, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2991, -1)]

def row16554 : Integer.Sparse Key := [(key2382, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 2), (key2545, -3), (key2555, 2), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2602, -1), (key2774, 4), (key2882, 4), (key2912, -1), (key2991, -1)]

def row16555 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, -1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, -3), (key2555, 1), (key2557, -3), (key2565, 2), (key2595, 4), (key2771, -1), (key2774, 4), (key2882, 4)]

def row16556 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, -1), (key2441, -1), (key2445, -1), (key2473, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, -3), (key2555, 1), (key2557, -3), (key2565, 2), (key2592, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

def row16557 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4), (key2848, 4)]

def row16558 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4), (key2848, 4)]

def row16559 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4), (key2848, 4)]

def row16560 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4), (key2848, 4)]

def row16561 : Integer.Sparse Key := [(key2379, 4), (key2382, -2), (key2393, -2), (key2410, -2), (key2441, -2), (key2473, 4), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2771, 4)]

def row16562 : Integer.Sparse Key := [(key2382, -2), (key2393, -2), (key2407, 4), (key2410, -2), (key2441, -2), (key2473, 4), (key2483, -2), (key2507, -2), (key2539, -4), (key2544, -4), (key2545, 4), (key2555, -4), (key2557, 4), (key2565, 4), (key2592, 4)]

def row16563 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -2), (key2831, 2), (key2860, -2), (key2870, -2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row16564 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, -2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row16565 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2632, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2706, -2), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2860, -2), (key2870, -2), (key2948, -1), (key2960, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row16566 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16567 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16568 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16569 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16570 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16571 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2632, 2), (key2640, -1), (key2644, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2706, 2), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, 2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, -1), (key2860, -1), (key2870, -1), (key2885, -2), (key2948, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row16572 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -2), (key2831, 2), (key2893, -2), (key2904, -2), (key2972, -2), (key2983, -2), (key3017, -2), (key3030, 4)]

def row16573 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2893, -2), (key2904, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2983, -2), (key3030, 4)]

def row16574 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2628, -2), (key2640, 4), (key2667, -2), (key2702, 4), (key2726, 4), (key2728, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2805, 4), (key2829, -1), (key2831, 2), (key2893, -2), (key2904, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2983, -2), (key3030, 4)]

def row16575 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16576 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16577 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16578 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16579 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16580 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16581 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16582 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16583 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16584 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16585 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16586 : Integer.Sparse Key := [(key2612, -1), (key2618, -1), (key2628, 2), (key2646, -1), (key2648, 1), (key2667, -1), (key2673, -1), (key2702, -1), (key2728, -1), (key2735, 2), (key2737, 1), (key2747, 1), (key2782, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2904, 1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2983, 1), (key2997, -2), (key3000, -2)]

def row16587 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16588 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16589 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16590 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16591 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16592 : Integer.Sparse Key := [(key2612, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2653, 1), (key2667, 2), (key2702, -1), (key2728, -1), (key2735, -1), (key2747, 1), (key2782, -1), (key2795, -1), (key2805, -1), (key2831, -1), (key2893, 2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, 1), (key2983, 1), (key2998, -2), (key3000, -2)]

def row16593 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16594 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16595 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16596 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16597 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16598 : Integer.Sparse Key := [(key2618, 2), (key2641, 2), (key2648, -2), (key2653, -2), (key2673, 2), (key2728, 2), (key2737, -2), (key2747, -2), (key2795, 2), (key2831, 2), (key2897, -2), (key2904, -2), (key2938, -2), (key2943, -2), (key2950, -2), (key2960, -2), (key2976, -2), (key2983, -2), (key2997, 4), (key2998, 4), (key3000, 4)]

def row16599 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 2), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key3017, 2), (key3023, -2), (key3026, 2)]

def row16600 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 1), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key2948, 1), (key2960, 2), (key3023, -2), (key3026, 2)]

def row16601 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2632, 2), (key2658, -2), (key2667, -2), (key2673, 2), (key2706, -2), (key2735, -2), (key2737, 4), (key2747, -2), (key2753, 2), (key2829, 1), (key2835, -4), (key2860, -2), (key2870, 2), (key2920, 4), (key2923, -4), (key2948, 1), (key2960, 2), (key3023, -2), (key3026, 2)]

def row16602 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16603 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16604 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16605 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16606 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

def row16607 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, 1), (key2660, -2), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, 2), (key2737, -1), (key2747, -1), (key2758, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2860, 1), (key2870, -1), (key2920, -2), (key2923, 2), (key2950, 1), (key2960, 1), (key3023, 1), (key3026, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1169 : Sparse Master := [(Sum.inr 1169, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1227 : Sparse Master := [(Sum.inr 1227, (1 / 1))]

def nodeValue1228 : Sparse Master := [(Sum.inr 1228, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1614 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end


