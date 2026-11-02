-- Prove2me | Definitions.Def_OAIQ106D089
-- name    : OAIQ106D089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:54:27.938066+00:00
-- url     : https://prove2.me/theorems/3121e5a5-7723-410f-8475-a244ac9bbdc1
-- title:
--   Definitions bundle OAIQ106D089 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 210 declarations of OpenAI's Lean: 210 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.key16`, `OAI.MUB6.Certificate.GramRows.key1835`, `OAI.MUB6.Certificate.GramRows.key205`, `OAI.MUB6.Certificate.GramRows.key374`, `OAI.MUB6.Certificate.GramRows.key41`, `OAI.MUB6.Certificate.GramRows.key425`, `OAI.MUB6.Certificate.GramRows.key433`, `OAI.MUB6.Certificate.GramRows.key98`, `OAI.MUB6.Certificate.GramRows.row6264`, `OAI.MUB6.Certificate.GramRows.row6265`, `OAI.MUB6.Certificate.GramRows.row6266`, `OAI.MUB6.Certificate.GramRows.row6267`, `OAI.MUB6.Certificate.GramRows.row6268`, `OAI.MUB6.Certificate.GramRows.row6269`, `OAI.MUB6.Certificate.GramRows.row6270`, `OAI.MUB6.Certificate.GramRows.row6271`, `OAI.MUB6.Certificate.GramRows.row6273`, `OAI.MUB6.Certificate.GramRows.row6274`, `OAI.MUB6.Certificate.GramRows.row6275`, `OAI.MUB6.Certificate.GramRows.row6276`, `OAI.MUB6.Certificate.GramRows.row6277`, `OAI.MUB6.Certificate.GramRows.row6318`, `OAI.MUB6.Certificate.GramRows.row6319`, `OAI.MUB6.Certificate.GramRows.row6320`, `OAI.MUB6.Certificate.GramRows.row6321`, `OAI.MUB6.Certificate.GramRows.row6322`, `OAI.MUB6.Certificate.GramRows.row6323`, `OAI.MUB6.Certificate.GramRows.row6324`, `OAI.MUB6.Certificate.GramRows.row6325`, `OAI.MUB6.Certificate.GramRows.row6326`, `OAI.MUB6.Certificate.GramRows.row6327`, `OAI.MUB6.Certificate.GramRows.row6328`, `OAI.MUB6.Certificate.GramRows.row6329`, `OAI.MUB6.Certificate.GramRows.row6330`, `OAI.MUB6.Certificate.GramRows.row6331`, `OAI.MUB6.Certificate.GramRows.row6332`, `OAI.MUB6.Certificate.GramRows.row6333`, `OAI.MUB6.Certificate.GramRows.row6334`, `OAI.MUB6.Certificate.GramRows.row6335`, `OAI.MUB6.Certificate.GramRows.row6336` and 170 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramKeys_Block0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramKeys/Block0.lean), [`MutuallyUnbiased_GramKeys_Block1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramKeys/Block1.lean), [`MutuallyUnbiased_GramKeys_Block14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramKeys/Block14.lean), [`MutuallyUnbiased_GramKeys_Block2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramKeys/Block2.lean), [`MutuallyUnbiased_GramKeys_Block3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramKeys/Block3.lean), [`MutuallyUnbiased_GramRows_Block72`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block72.lean), [`MutuallyUnbiased_GramRows_Block73`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block73.lean), [`MutuallyUnbiased_GramRows_Block74`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block74.lean), [`MutuallyUnbiased_GramRows_Block75`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block75.lean), [`MutuallyUnbiased_MixedSemantics_Values18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Values18.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D144`, `OAIQ106D147`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D156`, `OAIQ106D169`, `OAIQ106D176`, `OAIQ106D177`, `OAIQ106D178`, `OAIQ106D179`, `OAIQ106D184` and `OAIQ106D185`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key16 : Key := ⟨0, 0, [(-3, -2), (0, -1), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key41 : Key := ⟨0, 0, [(-3, -1), (0, -2), (0, 0), (0, 0), (0, 0), (3, 3)]⟩
def key98 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (0, 0), (3, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key205 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 0), (0, 0), (3, 3)]⟩

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

def key1835 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -3), (0, 0), (0, 0), (3, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key374 : Key := ⟨0, 0, [(-2, 0), (-1, -3), (0, 0), (0, 0), (0, 0), (3, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key425 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 0), (0, 0), (3, 3)]⟩
def key433 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (0, 0), (3, 3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row6264 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6265 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6266 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6267 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6268 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6269 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6270 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6271 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

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

def row6273 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6274 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6275 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6276 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6277 : Integer.Sparse Key := [(key2629, -2), (key2637, 2), (key2647, 2), (key2652, -2), (key2703, 2), (key2723, -2), (key2736, -2), (key2746, 2), (key2783, -2), (key2791, 2), (key2806, 2), (key2826, -2), (key2857, -4), (key2867, 4), (key2896, 2), (key2903, -2), (key2937, 2), (key2942, -2), (key2949, -2), (key2959, 2), (key2975, 2), (key2982, -2)]

def row6318 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6319 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6320 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6321 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6322 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6323 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6324 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6325 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6326 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6327 : Integer.Sparse Key := [(key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2587, -2), (key2593, 2), (key2598, 2), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2889, 4), (key2910, -2), (key2966, 4), (key2968, -2), (key2989, -2), (key2995, -2), (key3002, 2)]

def row6328 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6329 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2843, 1), (key2880, -1), (key2887, 1), (key2889, -2), (key2910, 1), (key2966, -2), (key2968, 1), (key2989, 1), (key2995, 1), (key3002, -1)]

def row6330 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2929, -1), (key2931, 1), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6331 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2929, -1), (key2931, 1), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6332 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2929, 2), (key2931, -2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6333 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2929, 2), (key2931, -2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6334 : Integer.Sparse Key := [(key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2931, 2), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6335 : Integer.Sparse Key := [(key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 2), (key2484, 2), (key2503, 2), (key2509, 2), (key2524, -4), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2887, -1), (key2889, -1), (key2910, -2), (key2931, 2), (key2966, -1), (key2968, -1), (key2989, -2), (key2995, 2), (key3002, 2)]

def row6336 : Integer.Sparse Key := [(key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2931, -1), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6337 : Integer.Sparse Key := [(key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 2), (key2484, -4), (key2503, -4), (key2509, 2), (key2524, 2), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 2), (key2910, 1), (key2931, -1), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

def row6338 : Integer.Sparse Key := [(key2437, 2), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, 1), (key2931, -2), (key2968, -1), (key2989, 1), (key3002, -1)]

def row6339 : Integer.Sparse Key := [(key2437, 2), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2587, 1), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, -2), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, 1), (key2931, -2), (key2968, -1), (key2989, 1), (key3002, -1)]

def row6340 : Integer.Sparse Key := [(key2390, -1), (key2437, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2580, 2), (key2587, 1), (key2593, -1), (key2600, 1), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -2), (key2931, 1), (key2968, -1), (key2989, -2)]

def row6341 : Integer.Sparse Key := [(key2390, -1), (key2437, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2580, 2), (key2587, 1), (key2593, -1), (key2600, 1), (key2766, 1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -2), (key2931, 1), (key2968, -1), (key2989, -2)]

def row6342 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2571, 2), (key2576, -1), (key2580, -1), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, -1), (key2931, -1), (key2968, -1), (key2989, 2)]

def row6343 : Integer.Sparse Key := [(key2378, -1), (key2390, -1), (key2394, 2), (key2406, -1), (key2437, 2), (key2443, -1), (key2472, 2), (key2480, 1), (key2484, -4), (key2503, -2), (key2509, 2), (key2524, 1), (key2571, 2), (key2576, -1), (key2580, -1), (key2587, 2), (key2593, -1), (key2600, -1), (key2766, -1), (key2772, 2), (key2843, -1), (key2880, -1), (key2889, 2), (key2910, -1), (key2931, -1), (key2968, -1), (key2989, 2)]

def row6344 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2571, -1), (key2576, -1), (key2580, 2), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -1), (key2931, 2), (key2968, -1), (key2989, -1)]

def row6345 : Integer.Sparse Key := [(key2378, 2), (key2390, -1), (key2394, -1), (key2406, 2), (key2437, -1), (key2443, -1), (key2472, -4), (key2480, 1), (key2484, 2), (key2503, 1), (key2509, 2), (key2524, -2), (key2571, -1), (key2576, -1), (key2580, 2), (key2587, -1), (key2593, -1), (key2600, 2), (key2766, -1), (key2772, -1), (key2843, 2), (key2880, 2), (key2889, -1), (key2910, -1), (key2931, 2), (key2968, -1), (key2989, -1)]

def row6346 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6347 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6348 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6349 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6350 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6351 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6352 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6353 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6354 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6355 : Integer.Sparse Key := [(key2378, 1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, 1), (key2411, -1), (key2437, -1), (key2443, 1), (key2472, -2), (key2480, 1), (key2484, 1), (key2503, 1), (key2509, 1), (key2524, -2), (key2569, 2), (key2571, -2), (key2576, -2), (key2580, 2)]

def row6356 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6357 : Integer.Sparse Key := [(key2378, -2), (key2383, 2), (key2390, 2), (key2394, -2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4), (key2569, -4), (key2571, 4), (key2576, 4), (key2580, -4)]

def row6358 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6359 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6360 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 2), (key2831, -2), (key2893, -2), (key2904, 2), (key2948, -4), (key2950, 2), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

def row6361 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2893, 1), (key2904, -1), (key2948, 1), (key2950, -2), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6362 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2835, 1), (key2893, 1), (key2904, -1), (key2948, 1), (key2950, -2), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1)]

def row6363 : Integer.Sparse Key := [(key2612, 2), (key2618, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -4), (key2831, -2), (key2835, 1), (key2893, -2), (key2904, 2), (key2950, 1), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

def row6364 : Integer.Sparse Key := [(key2612, 2), (key2618, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -4), (key2831, -2), (key2835, 1), (key2893, -2), (key2904, 2), (key2950, 1), (key2960, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2)]

def row6365 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 2), (key2831, 1), (key2835, -2), (key2893, 1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3017, -2)]

def row6366 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 2), (key2831, 1), (key2835, -2), (key2893, 1), (key2904, -1), (key2950, 1), (key2960, 1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3017, -2)]

def row6367 : Integer.Sparse Key := [(key2616, 2), (key2621, -2), (key2628, -2), (key2641, 2), (key2648, 2), (key2653, -2), (key2702, -2), (key2728, 2), (key2735, 2), (key2747, -2), (key2809, 2), (key2829, -4), (key2835, 2), (key2893, -2), (key2904, 2), (key2972, 4), (key2976, -2), (key2983, -2), (key2997, -2), (key2998, 2), (key3012, -2), (key3017, 2)]

def row6368 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2893, 1), (key2904, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3012, 1), (key3017, -1)]

def row6369 : Integer.Sparse Key := [(key2616, -1), (key2621, 1), (key2628, 1), (key2641, -1), (key2648, -1), (key2653, 1), (key2702, 1), (key2728, -1), (key2735, -1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2893, 1), (key2904, -1), (key2972, -2), (key2976, 1), (key2983, 1), (key2997, 1), (key2998, -1), (key3012, 1), (key3017, -1)]

def row6370 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2726, 1), (key2732, 1), (key2735, -1), (key2737, 1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6371 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2726, 1), (key2732, 1), (key2735, -1), (key2737, 1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6372 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2782, -1), (key2805, -1), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2936, 2), (key2938, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6373 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2702, 1), (key2706, 1), (key2726, -2), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2782, -1), (key2805, -1), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2936, 2), (key2938, -1), (key2948, 2), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6374 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2735, -1), (key2737, 1), (key2758, -1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6375 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2640, 1), (key2641, 1), (key2644, 1), (key2646, -1), (key2653, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2735, -1), (key2737, 1), (key2758, -1), (key2782, 1), (key2795, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key2998, 2), (key3000, 2), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6376 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2640, 1), (key2641, -1), (key2644, -2), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2758, -1), (key2782, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2938, -1), (key2943, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6377 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2640, 1), (key2641, -1), (key2644, -2), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2735, -1), (key2747, 1), (key2758, -1), (key2782, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2938, -1), (key2943, 1), (key2950, -1), (key2960, -1), (key2976, 1), (key2998, -1), (key3000, -1), (key3023, -2), (key3026, 1), (key3030, 1)]

def row6378 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, 1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2950, -1), (key2960, -1), (key2976, 1), (key3023, -2), (key3026, 1)]

def row6379 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, 1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, 1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2950, -1), (key2960, -1), (key2976, 1), (key3023, -2), (key3026, 1)]

def row6380 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2943, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key3023, 1), (key3026, 1)]

def row6381 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2653, -1), (key2667, 1), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2943, -1), (key2950, 1), (key2976, -1), (key2983, -1), (key3023, 1), (key3026, 1)]

def row6382 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, -1), (key2758, -1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, -1), (key2976, 1), (key3010, 2), (key3017, -1), (key3023, -2), (key3026, 1)]

def row6383 : Integer.Sparse Key := [(key2616, -1), (key2618, 1), (key2632, 1), (key2641, -1), (key2644, -2), (key2648, 1), (key2653, -1), (key2660, 2), (key2667, 1), (key2671, -1), (key2702, 1), (key2706, 1), (key2728, -1), (key2732, 1), (key2747, -1), (key2758, -1), (key2782, -1), (key2794, -1), (key2805, -1), (key2829, 2), (key2831, 1), (key2860, 1), (key2870, -2), (key2885, 1), (key2904, 1), (key2927, -1), (key2938, -1), (key2943, 1), (key2950, -1), (key2976, 1), (key3010, 2), (key3017, -1), (key3023, -2), (key3026, 1)]

def row6384 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2747, 1), (key2758, -1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2950, 1), (key2960, 1), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, -1), (key3023, 1), (key3026, 1)]

def row6385 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 1), (key2632, -2), (key2641, 1), (key2644, 1), (key2660, -1), (key2667, -1), (key2671, 2), (key2673, -1), (key2706, -2), (key2732, 1), (key2737, 1), (key2747, 1), (key2758, -1), (key2782, 1), (key2794, -1), (key2795, 1), (key2829, -1), (key2860, 1), (key2870, 1), (key2885, -2), (key2897, -1), (key2904, -1), (key2927, 2), (key2950, 1), (key2960, 1), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, -1), (key3023, 1), (key3026, 1)]

def row6386 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

def row6387 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6388 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6389 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

def row6390 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6391 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6392 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6393 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6394 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6395 : Integer.Sparse Key := [(key2616, 1), (key2621, -1), (key2632, -1), (key2644, 1), (key2658, 1), (key2660, -1), (key2671, 1), (key2676, -1), (key2706, -1), (key2732, 1), (key2753, 1), (key2758, -1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, 1), (key2885, -2), (key2920, -1), (key2923, -1), (key2927, 2)]

def row6396 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

def row6397 : Integer.Sparse Key := [(key2616, -2), (key2621, 2), (key2632, 2), (key2644, -2), (key2658, -2), (key2660, 2), (key2671, -2), (key2676, 2), (key2706, 2), (key2732, -2), (key2753, -2), (key2758, 2), (key2794, 2), (key2798, -2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, -2), (key2885, 4), (key2920, 2), (key2923, 2), (key2927, -4)]

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

def row6438 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6439 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6440 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3011, 2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6441 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6442 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6443 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6444 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 4), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6445 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6446 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -3), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, 1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6447 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2624, 2), (key2638, -2), (key2657, -2), (key2659, 2), (key2704, 2), (key2724, -2), (key2752, -2), (key2757, 2), (key2801, 2), (key2807, -4), (key2827, 2), (key2851, -2), (key2858, 2), (key2918, 4), (key2919, -2), (key2922, -2), (key3011, 2), (key3016, -2), (key3021, -2), (key3025, 2)]

def row6448 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6449 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 1), (key2657, 1), (key2659, -1), (key2704, -1), (key2724, 1), (key2752, 1), (key2757, -1), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -1), (key2918, -2), (key2919, 1), (key2922, 1), (key3011, -1), (key3016, 1), (key3021, 1), (key3025, -1)]

def row6450 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3021, -2)]

def row6451 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -2), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3021, -2)]

def row6452 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3011, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6453 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -1), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3011, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6454 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2757, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6455 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2757, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6456 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2752, 2), (key2757, -1), (key2784, 2), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6457 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2752, 2), (key2757, -1), (key2784, 2), (key2792, -1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6458 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2757, -1), (key2784, 2), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6459 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 2), (key2659, -1), (key2704, -3), (key2724, 1), (key2757, -1), (key2784, 2), (key2792, 1), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6460 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6461 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3021, -2)]

def row6462 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6463 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, -1), (key2638, 3), (key2657, -1), (key2659, -1), (key2698, 1), (key2704, -3), (key2724, 2), (key2752, 1), (key2778, -1), (key2784, 2), (key2801, -1), (key2807, 2), (key2827, -2), (key2851, 1), (key2858, -3), (key2919, 1), (key3007, -1), (key3009, -1), (key3016, 1), (key3021, 1), (key3022, 1), (key3025, -1)]

def row6464 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3011, 1), (key3021, -2)]

def row6465 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -2), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -2), (key2757, 1), (key2778, 1), (key2784, -1), (key2792, -1), (key2801, 1), (key2807, -1), (key2827, -1), (key2851, -2), (key2858, 3), (key2868, 3), (key2919, -1), (key2922, -1), (key3007, 1), (key3011, 1), (key3021, -2)]

def row6466 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6467 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6468 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6469 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -4), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6470 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6471 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 2), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6472 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, -2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 4), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6473 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, -2), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, 4), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6474 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 3), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6475 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2663, -1), (key2669, 1), (key2698, 3), (key2724, -1), (key2752, -1), (key2757, 1), (key2778, -1), (key2784, -1), (key2801, 1), (key2807, -1), (key2851, -2), (key2858, 1), (key2868, 1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row6476 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6477 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2778, -2), (key2784, 2), (key2801, -2), (key2807, 2), (key2851, 4), (key2858, -2), (key2868, -2), (key2918, -4), (key2919, 2), (key2922, 2)]

def row6478 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6479 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6480 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6481 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6482 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6483 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6484 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6485 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6486 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6487 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2794, 1), (key2798, -1), (key2829, -1), (key2835, 1), (key2860, 1), (key2870, -1), (key2920, -1), (key2923, 1)]

def row6488 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6489 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2794, -2), (key2798, 2), (key2829, 2), (key2835, -2), (key2860, -2), (key2870, 2), (key2920, 2), (key2923, -2)]

def row6490 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6491 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6492 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6493 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6494 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6495 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6496 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6497 : Integer.Sparse Key := [(key2612, 1), (key2618, -1), (key2628, 1), (key2641, -1), (key2646, -2), (key2648, 1), (key2653, 1), (key2667, -1), (key2673, 1), (key2735, 1), (key2737, -1), (key2782, -1), (key2795, 1), (key2893, 1), (key2897, -1), (key2936, 2), (key2938, -1), (key2943, -1), (key2948, -1), (key2950, 1), (key2972, -1), (key2976, 1)]

def row6518 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6519 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6520 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6521 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6522 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6523 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6524 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6525 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6526 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6527 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

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

def row6528 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6529 : Integer.Sparse Key := [(key2616, -2), (key2619, 2), (key2632, -2), (key2640, 4), (key2642, -2), (key2649, 2), (key2654, -2), (key2671, 2), (key2674, -2), (key2706, 2), (key2726, -4), (key2729, 2), (key2738, -2), (key2748, 2), (key2794, -2), (key2796, 2), (key2829, 2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, 2), (key2905, -2)]

def row6530 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6531 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6532 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6533 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6534 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6535 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6536 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6537 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, 1), (key2640, -2), (key2642, 1), (key2649, -1), (key2654, 1), (key2671, -1), (key2674, 1), (key2706, -1), (key2726, 2), (key2729, -1), (key2738, 1), (key2748, -1), (key2794, 1), (key2796, -1), (key2829, -1), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -1), (key2905, 1)]

def row6558 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6559 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6560 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6561 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6562 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6563 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6564 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6565 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6566 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6567 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2771, -1), (key2774, 1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, 1), (key2914, -2), (key2933, 1), (key2934, -1), (key2970, 1), (key2991, -2), (key2993, 1), (key2996, -1), (key3003, 1)]

def row6568 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6569 : Integer.Sparse Key := [(key2379, -4), (key2382, 4), (key2393, 4), (key2395, -4), (key2771, 2), (key2774, -2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, -2), (key2914, 4), (key2933, -2), (key2934, 2), (key2970, -2), (key2991, 4), (key2993, -2), (key2996, 2), (key3003, -2)]

def row6570 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, -1), (key2441, 2), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2771, -1), (key2774, 2), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2933, -1), (key2970, -1), (key2991, 2)]

def row6571 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, -1), (key2441, 2), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2771, -1), (key2774, 2), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2933, -1), (key2970, -1), (key2991, 2)]

def row6572 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2970, -1), (key2991, 2)]

def row6573 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, 2), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, 2), (key2912, -1), (key2970, -1), (key2991, 2)]

def row6574 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, -1), (key2441, 1), (key2445, -1), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2912, -1), (key2991, 2)]

def row6575 : Integer.Sparse Key := [(key2382, -1), (key2393, -1), (key2395, 2), (key2407, -1), (key2410, -1), (key2441, 1), (key2445, -1), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, 2), (key2545, -2), (key2555, -4), (key2557, 1), (key2565, 1), (key2592, 2), (key2595, -1), (key2602, -1), (key2774, 2), (key2882, -1), (key2912, -1), (key2991, 2)]

def row6576 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, 1), (key2545, -2), (key2555, -2), (key2557, 1), (key2565, 1), (key2771, -1), (key2848, -1)]

def row6577 : Integer.Sparse Key := [(key2379, 2), (key2382, -2), (key2393, -2), (key2395, 2), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, 1), (key2545, -2), (key2555, -2), (key2557, 1), (key2565, 1), (key2771, -1), (key2848, -1)]

def row6638 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row6639 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6640 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6641 : Integer.Sparse Key := [(key2671, 2), (key2676, -2), (key2706, 2), (key2726, -4), (key2732, 2), (key2753, -2), (key2758, 2), (key2786, -2), (key2798, 2), (key2809, -2), (key2829, 2), (key2870, 2), (key2885, -2), (key2920, 2), (key2927, -2), (key3008, 2), (key3010, -2), (key3012, 2), (key3017, -2), (key3023, -2), (key3026, -2), (key3030, 4)]

def row6642 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6643 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

def row6644 : Integer.Sparse Key := [(key2671, -1), (key2676, 1), (key2706, -1), (key2726, 2), (key2732, -1), (key2753, 1), (key2758, -1), (key2786, 1), (key2798, -1), (key2809, 1), (key2829, -1), (key2870, -1), (key2885, 1), (key2920, -1), (key2927, 1), (key3008, -1), (key3010, 1), (key3012, -1), (key3017, 1), (key3023, 1), (key3026, 1), (key3030, -2)]

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

def nodeValue1181 : Sparse Master := [(Sum.inr 1181, (1 / 1))]

def nodeValue1182 : Sparse Master := [(Sum.inr 1182, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


