-- Prove2me | Definitions.Def_OAIQ106D088
-- name    : OAIQ106D088
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:54:05.908261+00:00
-- url     : https://prove2.me/theorems/6d4975bd-322a-4525-906d-e7211188062a
-- title:
--   Definitions bundle OAIQ106D088 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 388 declarations of OpenAI's Lean: 388 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block3.entry0_0`, `OAI.MUB6.Certificate.GramRows.key159`, `OAI.MUB6.Certificate.GramRows.key1607`, `OAI.MUB6.Certificate.GramRows.key173`, `OAI.MUB6.Certificate.GramRows.key177`, `OAI.MUB6.Certificate.GramRows.key182`, `OAI.MUB6.Certificate.GramRows.key190`, `OAI.MUB6.Certificate.GramRows.row5268`, `OAI.MUB6.Certificate.GramRows.row5269`, `OAI.MUB6.Certificate.GramRows.row5270`, `OAI.MUB6.Certificate.GramRows.row5271`, `OAI.MUB6.Certificate.GramRows.row5272`, `OAI.MUB6.Certificate.GramRows.row5273`, `OAI.MUB6.Certificate.GramRows.row5274`, `OAI.MUB6.Certificate.GramRows.row5275`, `OAI.MUB6.Certificate.GramRows.row5276`, `OAI.MUB6.Certificate.GramRows.row5277`, `OAI.MUB6.Certificate.GramRows.row5278`, `OAI.MUB6.Certificate.GramRows.row5279`, `OAI.MUB6.Certificate.GramRows.row5280`, `OAI.MUB6.Certificate.GramRows.row5281`, `OAI.MUB6.Certificate.GramRows.row5282`, `OAI.MUB6.Certificate.GramRows.row5283`, `OAI.MUB6.Certificate.GramRows.row5284`, `OAI.MUB6.Certificate.GramRows.row5285`, `OAI.MUB6.Certificate.GramRows.row5286`, `OAI.MUB6.Certificate.GramRows.row5287`, `OAI.MUB6.Certificate.GramRows.row5288`, `OAI.MUB6.Certificate.GramRows.row5289`, `OAI.MUB6.Certificate.GramRows.row5290`, `OAI.MUB6.Certificate.GramRows.row5291`, `OAI.MUB6.Certificate.GramRows.row5292`, `OAI.MUB6.Certificate.GramRows.row5293`, `OAI.MUB6.Certificate.GramRows.row5294`, `OAI.MUB6.Certificate.GramRows.row5295`, `OAI.MUB6.Certificate.GramRows.row5296`, `OAI.MUB6.Certificate.GramRows.row5297`, `OAI.MUB6.Certificate.GramRows.row5298`, `OAI.MUB6.Certificate.GramRows.row5299`, `OAI.MUB6.Certificate.GramRows.row5300` and 348 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramEntries_Block3Data`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramEntries/Block3Data.lean), [`MutuallyUnbiased_GramKeys_Block1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramKeys/Block1.lean), [`MutuallyUnbiased_GramKeys_Block12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramKeys/Block12.lean), [`MutuallyUnbiased_GramRows_Block65`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block65.lean), [`MutuallyUnbiased_GramRows_Block66`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block66.lean), [`MutuallyUnbiased_GramRows_Block67`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block67.lean), [`MutuallyUnbiased_GramRows_Block68`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block68.lean), [`MutuallyUnbiased_GramRows_Block69`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block69.lean), [`MutuallyUnbiased_GramRows_Block72`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block72.lean), [`MutuallyUnbiased_GramRows_Block73`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block73.lean), [`MutuallyUnbiased_MixedSemantics_Values18`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Values18.lean), [`MutuallyUnbiased_MixedSemantics_Values19`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Values19.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D145`, `OAIQ106D147`, `OAIQ106D148`, `OAIQ106D149`, `OAIQ106D156`, `OAIQ106D169`, `OAIQ106D174` and `OAIQ106D184`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key159 : Key := ⟨0, 0, [(-3, 0), (0, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩
def key173 : Key := ⟨0, 0, [(-3, 1), (0, -2), (0, -1), (1, 0), (1, 0), (1, 2)]⟩
def key177 : Key := ⟨0, 0, [(-3, 1), (0, -2), (0, 0), (1, -1), (1, 0), (1, 2)]⟩
def key182 : Key := ⟨0, 0, [(-3, 1), (0, -1), (0, 0), (1, -2), (1, 0), (1, 2)]⟩
def key190 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1607 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (0, 1), (3, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization

def entry0_0 : Integer.Sparse Key := [(key2362, 96), (key2367, -96), (key2457, 144), (key2460, -96), (key2521, 64), (key2525, -192), (key2532, 128), (key2533, -96), (key2562, 144), (key2564, -96)]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5268 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5269 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5270 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5271 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5272 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5273 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5274 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5275 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5276 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5277 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2664, -2), (key2668, 2), (key2699, 2), (key2703, -2), (key2779, 2), (key2783, -4), (key2791, 2), (key2802, -2), (key2806, 2), (key2894, 2), (key2896, -2), (key2937, 2), (key2942, -2), (key2973, -2), (key2975, 2)]

def row5278 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5279 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5280 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5281 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5282 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5283 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5284 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5285 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5286 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5287 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5288 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5289 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 4), (key2723, -2), (key2736, -2), (key2746, 2), (key2779, -2), (key2783, 2), (key2802, 2), (key2806, -4), (key2826, 2), (key2894, 2), (key2903, -2), (key2949, 2), (key2959, -2), (key2973, -2), (key2982, 2)]

def row5290 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5291 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5292 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5293 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5294 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5295 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5296 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5297 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5298 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5299 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5300 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5301 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5302 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5303 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5304 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5305 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, 1), (key2746, -1), (key2779, 1), (key2783, -1), (key2802, -1), (key2806, 2), (key2826, -1), (key2894, -1), (key2903, 1), (key2949, -1), (key2959, 1), (key2973, 1), (key2982, -1)]

def row5306 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5307 : Integer.Sparse Key := [(key2609, -1), (key2613, 1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, 1), (key2652, -1), (key2664, 1), (key2668, -1), (key2699, -1), (key2703, 1), (key2779, -1), (key2783, 2), (key2791, -1), (key2802, 1), (key2806, -1), (key2894, -1), (key2896, 1), (key2937, -1), (key2942, 1), (key2973, 1), (key2975, -1)]

def row5308 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5309 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5310 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5311 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5312 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5313 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5314 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5315 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5316 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5317 : Integer.Sparse Key := [(key1292, 2), (key1297, -2), (key1312, -2), (key1317, 4), (key1325, -2), (key1338, -2), (key1344, 2), (key1387, -2), (key1392, 2), (key1420, 2), (key1425, -2), (key1542, 2), (key1547, -4), (key1555, 2), (key1569, -2), (key1574, 2), (key1656, 2), (key1658, -2), (key1773, 2), (key1779, -2), (key1814, -2), (key1816, 2)]

def row5318 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5319 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5320 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5321 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5322 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5323 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5324 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5325 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5326 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5327 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5328 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5329 : Integer.Sparse Key := [(key1292, -2), (key1297, 2), (key1312, 2), (key1317, -2), (key1387, 2), (key1392, -2), (key1420, -2), (key1425, 4), (key1443, -2), (key1456, -2), (key1465, 2), (key1542, -2), (key1547, 2), (key1569, 2), (key1574, -4), (key1592, 2), (key1656, 2), (key1666, -2), (key1789, 2), (key1797, -2), (key1814, -2), (key1824, 2)]

def row5330 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5331 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5332 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5333 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5334 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5335 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5336 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5337 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5338 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5339 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5340 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5341 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5342 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5343 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5344 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5345 : Integer.Sparse Key := [(key1292, 1), (key1297, -1), (key1312, -1), (key1317, 1), (key1387, -1), (key1392, 1), (key1420, 1), (key1425, -2), (key1443, 1), (key1456, 1), (key1465, -1), (key1542, 1), (key1547, -1), (key1569, -1), (key1574, 2), (key1592, -1), (key1656, -1), (key1666, 1), (key1789, -1), (key1797, 1), (key1814, 1), (key1824, -1)]

def row5346 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5347 : Integer.Sparse Key := [(key1292, -1), (key1297, 1), (key1312, 1), (key1317, -2), (key1325, 1), (key1338, 1), (key1344, -1), (key1387, 1), (key1392, -1), (key1420, -1), (key1425, 1), (key1542, -1), (key1547, 2), (key1555, -1), (key1569, 1), (key1574, -1), (key1656, -1), (key1658, 1), (key1773, -1), (key1779, 1), (key1814, 1), (key1816, -1)]

def row5348 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5349 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5350 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5351 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5352 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5353 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5354 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -4), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5355 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5356 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 3), (key2645, -1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5357 : Integer.Sparse Key := [(key2608, 2), (key2611, -2), (key2624, -2), (key2627, 4), (key2636, -2), (key2645, -2), (key2651, 2), (key2663, -2), (key2666, 2), (key2698, 2), (key2701, -4), (key2722, 2), (key2734, 2), (key2745, -2), (key2778, 2), (key2781, -2), (key2801, -2), (key2804, 2), (key2856, 2), (key2866, -2), (key2895, -2), (key2902, 2)]

def row5358 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5359 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 2), (key2722, -1), (key2734, -1), (key2745, 1), (key2778, -1), (key2781, 1), (key2801, 1), (key2804, -1), (key2856, -1), (key2866, 1), (key2895, 1), (key2902, -1)]

def row5360 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5361 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5362 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 2), (key2856, 2), (key2866, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5363 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5364 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5365 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 4), (key2856, 2), (key2866, -2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5366 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 4), (key2856, 2), (key2866, -2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5367 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5368 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -3), (key2856, -1), (key2866, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5369 : Integer.Sparse Key := [(key2608, -2), (key2611, 2), (key2624, 2), (key2627, -2), (key2663, 2), (key2666, -2), (key2698, -4), (key2701, 6), (key2722, -2), (key2734, -2), (key2745, 2), (key2801, 2), (key2804, -4), (key2825, 2), (key2856, 2), (key2866, -2), (key2947, 2), (key2958, -2), (key2974, -2), (key2981, 2)]

def row5370 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5371 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 2), (key2701, -3), (key2722, 1), (key2734, 1), (key2745, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2856, -1), (key2866, 1), (key2947, -1), (key2958, 1), (key2974, 1), (key2981, -1)]

def row5372 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -2), (key2701, 1), (key2745, 1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2825, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2947, 1), (key2971, 1), (key2974, -1)]

def row5373 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -2), (key2701, 1), (key2745, 1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2825, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2947, 1), (key2971, 1), (key2974, -1)]

def row5374 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2941, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5375 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2941, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5376 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2636, 1), (key2645, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 2), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5377 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2636, 1), (key2645, -1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 2), (key2745, -1), (key2778, 2), (key2781, -1), (key2790, -1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5378 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5379 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5380 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5381 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 2), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2722, -1), (key2745, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2971, 1), (key2974, -1)]

def row5382 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2790, 1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5383 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2698, 1), (key2701, -2), (key2722, 1), (key2745, -1), (key2778, 1), (key2781, -1), (key2790, 1), (key2801, -1), (key2804, 2), (key2825, -2), (key2892, -1), (key2902, 1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5384 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2892, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5385 : Integer.Sparse Key := [(key2608, 1), (key2611, -1), (key2624, -1), (key2627, 1), (key2663, -1), (key2666, 1), (key2701, -2), (key2722, 1), (key2734, 1), (key2745, -1), (key2778, 2), (key2781, -1), (key2801, -1), (key2804, 2), (key2825, -1), (key2892, -1), (key2902, 1), (key2947, -1), (key2958, 1), (key2971, 1), (key2981, -1)]

def row5386 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2941, 1), (key2971, 1), (key2974, -1)]

def row5387 : Integer.Sparse Key := [(key2608, -1), (key2611, 1), (key2624, 1), (key2627, -2), (key2636, 1), (key2645, 1), (key2651, -1), (key2663, 1), (key2666, -1), (key2698, -1), (key2701, 1), (key2778, -1), (key2781, 2), (key2790, -1), (key2801, 1), (key2804, -1), (key2892, -1), (key2895, 1), (key2935, -1), (key2941, 1), (key2971, 1), (key2974, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5508 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2480, -4), (key2484, 4), (key2503, 4), (key2509, -4)]

def row5509 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5510 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5511 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5512 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, -2), (key2411, 2), (key2437, 2), (key2443, -2), (key2480, 2), (key2484, -2), (key2503, -2), (key2509, 2)]

def row5513 : Integer.Sparse Key := [(key2378, -4), (key2383, 4), (key2390, 4), (key2394, -4), (key2406, 4), (key2411, -4), (key2437, -4), (key2443, 4), (key2480, -4), (key2484, 4), (key2503, 4), (key2509, -4)]

def row5514 : Integer.Sparse Key := [(key2390, -2), (key2394, 2), (key2437, 2), (key2443, -2), (key2480, -2), (key2503, 2), (key2571, 2), (key2576, -2), (key2587, 2), (key2593, -2), (key2766, -2), (key2772, 2), (key2887, 4), (key2889, -2), (key2910, -2), (key2966, -4), (key2968, 2), (key2989, 2)]

def row5515 : Integer.Sparse Key := [(key2390, 1), (key2394, -1), (key2437, -1), (key2443, 1), (key2480, 1), (key2503, -1), (key2571, -1), (key2576, 1), (key2587, -1), (key2593, 1), (key2766, 1), (key2772, -1), (key2887, -2), (key2889, 1), (key2910, 1), (key2966, 2), (key2968, -1), (key2989, -1)]

def row5516 : Integer.Sparse Key := [(key2390, 1), (key2394, -1), (key2437, -1), (key2443, 1), (key2480, 1), (key2503, -1), (key2571, -1), (key2576, 1), (key2587, -1), (key2593, 1), (key2766, 1), (key2772, -1), (key2887, -2), (key2889, 1), (key2910, 1), (key2966, 2), (key2968, -1), (key2989, -1)]

def row5517 : Integer.Sparse Key := [(key2390, -2), (key2394, 2), (key2437, 2), (key2443, -2), (key2587, 2), (key2593, -2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2966, -2), (key2968, 2)]

def row5518 : Integer.Sparse Key := [(key2394, -1), (key2443, 1), (key2587, -1), (key2593, 1), (key2598, 1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2966, 1), (key2968, -1)]

def row5519 : Integer.Sparse Key := [(key2394, -1), (key2443, 1), (key2587, -1), (key2593, 1), (key2598, 1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2966, 1), (key2968, -1)]

def row5520 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1), (key2587, -2), (key2593, 1), (key2600, -1), (key2766, 2), (key2772, -1), (key2887, -1), (key2889, 1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5521 : Integer.Sparse Key := [(key2378, 1), (key2390, 1), (key2406, -1), (key2437, -1), (key2587, -2), (key2593, 1), (key2600, -1), (key2766, 2), (key2772, -1), (key2887, -1), (key2889, 1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5522 : Integer.Sparse Key := [(key2378, -1), (key2406, 1), (key2480, 1), (key2503, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2772, -1), (key2887, -2), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 2), (key2968, -1)]

def row5523 : Integer.Sparse Key := [(key2378, -1), (key2406, 1), (key2480, 1), (key2503, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2772, -1), (key2887, -2), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 2), (key2968, -1)]

def row5524 : Integer.Sparse Key := [(key2390, -1), (key2437, 1), (key2480, -1), (key2503, 1), (key2587, 2), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 3), (key2889, -2), (key2929, 1), (key2931, -2), (key2966, -3), (key2968, 2)]

def row5525 : Integer.Sparse Key := [(key2390, -1), (key2437, 1), (key2480, -1), (key2503, 1), (key2587, 2), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 3), (key2889, -2), (key2929, 1), (key2931, -2), (key2966, -3), (key2968, 2)]

def row5526 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5527 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5528 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5529 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5530 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5531 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5532 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5533 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5534 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5535 : Integer.Sparse Key := [(key2587, 2), (key2593, -2), (key2598, -2), (key2600, 2), (key2766, -2), (key2772, 2), (key2887, 2), (key2889, -2), (key2929, 2), (key2931, -2), (key2966, -2), (key2968, 2)]

def row5536 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5537 : Integer.Sparse Key := [(key2587, -1), (key2593, 1), (key2598, 1), (key2600, -1), (key2766, 1), (key2772, -1), (key2887, -1), (key2889, 1), (key2929, -1), (key2931, 1), (key2966, 1), (key2968, -1)]

def row5538 : Integer.Sparse Key := [(key1256, -4), (key1261, 4), (key1265, 4), (key1268, -4), (key1531, 4), (key1536, -4), (key1648, -4), (key1651, 4), (key1765, -4), (key1768, 4), (key1806, 4), (key1809, -4)]

def row5539 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5540 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5541 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5542 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5543 : Integer.Sparse Key := [(key1256, -4), (key1261, 4), (key1265, 4), (key1268, -4), (key1531, 4), (key1536, -4), (key1648, -4), (key1651, 4), (key1765, -4), (key1768, 4), (key1806, 4), (key1809, -4)]

def row5544 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5545 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5546 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5547 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5548 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5549 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5550 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5551 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5552 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5553 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5554 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5555 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5556 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5557 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5558 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5559 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5560 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5561 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5562 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5563 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5564 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5565 : Integer.Sparse Key := [(key1256, 2), (key1261, -2), (key1265, -2), (key1268, 2), (key1531, -2), (key1536, 2), (key1648, 2), (key1651, -2), (key1765, 2), (key1768, -2), (key1806, -2), (key1809, 2)]

def row5566 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5567 : Integer.Sparse Key := [(key1256, -1), (key1261, 1), (key1265, 1), (key1268, -1), (key1531, 1), (key1536, -1), (key1648, -1), (key1651, 1), (key1765, -1), (key1768, 1), (key1806, 1), (key1809, -1)]

def row5568 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, 4), (key2409, -4), (key2437, -4), (key2440, 4), (key2480, -4), (key2482, 4), (key2503, 4), (key2506, -4)]

def row5569 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5570 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5571 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5572 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5573 : Integer.Sparse Key := [(key2378, -4), (key2381, 4), (key2390, 4), (key2392, -4), (key2406, 4), (key2409, -4), (key2437, -4), (key2440, 4), (key2480, -4), (key2482, 4), (key2503, 4), (key2506, -4)]

def row5574 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5575 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5576 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5577 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5578 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5579 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5580 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5581 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5582 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5583 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5584 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5585 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5586 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5587 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5588 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5589 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5590 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5591 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5592 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5593 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5594 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5595 : Integer.Sparse Key := [(key2378, 2), (key2381, -2), (key2390, -2), (key2392, 2), (key2406, -2), (key2409, 2), (key2437, 2), (key2440, -2), (key2480, 2), (key2482, -2), (key2503, -2), (key2506, 2)]

def row5596 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

def row5597 : Integer.Sparse Key := [(key2378, -1), (key2381, 1), (key2390, 1), (key2392, -1), (key2406, 1), (key2409, -1), (key2437, -1), (key2440, 1), (key2480, -1), (key2482, 1), (key2503, 1), (key2506, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5658 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2809, 2), (key2829, -4), (key2835, 2), (key2860, -2), (key2870, 2), (key3012, -2), (key3017, 2), (key3023, 2), (key3026, -2)]

def row5659 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2860, 1), (key2870, -1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row5660 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2809, -1), (key2829, 2), (key2835, -1), (key2860, 1), (key2870, -1), (key3012, 1), (key3017, -1), (key3023, -1), (key3026, 1)]

def row5661 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 2), (key2829, -4), (key2831, -2), (key2835, 2), (key2860, -2), (key2870, 2), (key3017, 2), (key3023, 2), (key3026, -2)]

def row5662 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2621, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2829, 1), (key2831, 1), (key2835, -1), (key2860, 1), (key2870, -1), (key2948, 1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5663 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2621, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2829, 1), (key2831, 1), (key2835, -1), (key2860, 1), (key2870, -1), (key2948, 1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5664 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5665 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -2), (key2809, 1), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5666 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5667 : Integer.Sparse Key := [(key2612, -2), (key2616, 1), (key2618, 1), (key2640, 1), (key2644, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, 1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, 1), (key2809, -2), (key2829, 1), (key2831, 1), (key2860, 1), (key2870, -1), (key2948, 1), (key2950, -1), (key2960, -1), (key3023, -1), (key3026, 1)]

def row5668 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2618, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -2), (key2831, -2), (key2860, -2), (key2870, 2), (key2948, -2), (key2950, 2), (key2960, 2), (key3023, 2), (key3026, -2)]

def row5669 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2618, -2), (key2640, -2), (key2644, 2), (key2667, -2), (key2673, 2), (key2702, -2), (key2726, 2), (key2728, 2), (key2732, -2), (key2735, 4), (key2737, -2), (key2747, -2), (key2805, 1), (key2809, 1), (key2829, -2), (key2831, -2), (key2860, -2), (key2870, 2), (key2948, -2), (key2950, 2), (key2960, 2), (key3023, 2), (key3026, -2)]

def row5670 : Integer.Sparse Key := [(key2628, 2), (key2640, -2), (key2641, -2), (key2660, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2758, -2), (key2782, -2), (key2794, -2), (key2795, 2), (key2805, -2), (key2829, 2), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3010, 2), (key3017, -2)]

def row5671 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2758, 1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, 1)]

def row5672 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2758, 1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2972, 2), (key2976, -1), (key2983, -1), (key3010, -1), (key3017, 1)]

def row5673 : Integer.Sparse Key := [(key2628, 2), (key2640, -2), (key2641, -2), (key2660, 2), (key2702, 2), (key2726, 2), (key2728, -2), (key2735, -2), (key2747, 2), (key2758, -2), (key2782, -2), (key2795, 2), (key2805, -2), (key2829, 2), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2972, -4), (key2976, 2), (key2983, 2), (key3017, -2)]

def row5674 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2660, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2758, 1), (key2782, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5675 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2640, 1), (key2641, 1), (key2660, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2758, 1), (key2782, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5676 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2667, 1), (key2671, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5677 : Integer.Sparse Key := [(key2612, -1), (key2616, 1), (key2628, -1), (key2640, 1), (key2641, 1), (key2653, -1), (key2667, 1), (key2671, -1), (key2702, -1), (key2726, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5678 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2667, -1), (key2671, 1), (key2702, -1), (key2728, 1), (key2747, -1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5679 : Integer.Sparse Key := [(key2612, 1), (key2616, -1), (key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2667, -1), (key2671, 1), (key2702, -1), (key2728, 1), (key2747, -1), (key2782, 1), (key2794, 1), (key2795, -1), (key2805, 1), (key2829, -1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5680 : Integer.Sparse Key := [(key2628, 2), (key2640, -1), (key2641, -2), (key2646, -1), (key2653, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2735, -1), (key2747, 2), (key2782, -2), (key2794, -1), (key2795, 2), (key2805, -2), (key2829, 1), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2936, 1), (key2943, -2), (key2948, 1), (key2960, -2), (key2972, -4), (key2976, 2), (key2983, 2)]

def row5681 : Integer.Sparse Key := [(key2628, 2), (key2640, -1), (key2641, -2), (key2646, -1), (key2653, 2), (key2702, 2), (key2726, 1), (key2728, -2), (key2735, -1), (key2747, 2), (key2782, -2), (key2794, -1), (key2795, 2), (key2805, -2), (key2829, 1), (key2831, 2), (key2893, 4), (key2897, -2), (key2904, -2), (key2936, 1), (key2943, -2), (key2948, 1), (key2960, -2), (key2972, -4), (key2976, 2), (key2983, 2)]

def row5682 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5683 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5684 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5685 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5686 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5687 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5688 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5689 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5690 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5691 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5692 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5693 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5694 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5695 : Integer.Sparse Key := [(key2612, -1), (key2618, 1), (key2646, 1), (key2648, -1), (key2667, 1), (key2673, -1), (key2702, 1), (key2728, -1), (key2735, -2), (key2737, 1), (key2747, 1), (key2805, -1), (key2831, 1), (key2893, 1), (key2904, -1), (key2936, -1), (key2938, 1), (key2948, 2), (key2950, -1), (key2960, -1), (key2972, -1), (key2983, 1)]

def row5696 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5697 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2646, 1), (key2653, -1), (key2702, -1), (key2728, 1), (key2735, 1), (key2747, -1), (key2782, 1), (key2795, -1), (key2805, 1), (key2831, -1), (key2893, -2), (key2897, 1), (key2904, 1), (key2936, -1), (key2943, 1), (key2948, -1), (key2960, 1), (key2972, 2), (key2976, -1), (key2983, -1)]

def row5738 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5739 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5740 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5741 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5742 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5743 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5744 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5745 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5746 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5747 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5748 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5749 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2640, -2), (key2642, 2), (key2671, -2), (key2674, 2), (key2726, 2), (key2729, -2), (key2786, -2), (key2794, 4), (key2796, -2), (key2809, 2), (key2829, -4), (key2832, 2), (key2860, -2), (key2870, 2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

def row5750 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5751 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5752 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5753 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5754 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5755 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5756 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5757 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5758 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5759 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row5760 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5761 : Integer.Sparse Key := [(key2632, 2), (key2640, -2), (key2649, -2), (key2654, 2), (key2706, -2), (key2726, 2), (key2738, 2), (key2748, -2), (key2786, 2), (key2794, -2), (key2809, -2), (key2829, 2), (key2860, 4), (key2870, -4), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

def row5762 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5763 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5764 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5765 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5766 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5767 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5768 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5769 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5770 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5771 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5772 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5773 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5774 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5775 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, -1), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row5776 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5777 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2649, 1), (key2654, -1), (key2706, 1), (key2726, -1), (key2738, -1), (key2748, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 2), (key2898, 1), (key2905, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row5818 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5819 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5820 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5821 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5822 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5823 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5824 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5825 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5826 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5827 : Integer.Sparse Key := [(key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2848, -1), (key2882, 1), (key2891, 1), (key2912, -2), (key2914, 1), (key2970, 1), (key2991, 1), (key2993, -2), (key2996, -1), (key3003, 1)]

def row5828 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5829 : Integer.Sparse Key := [(key2407, -4), (key2410, 4), (key2441, 4), (key2445, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2848, 2), (key2882, -2), (key2891, -2), (key2912, 4), (key2914, -2), (key2970, -2), (key2991, -2), (key2993, 4), (key2996, 2), (key3003, -2)]

def row5830 : Integer.Sparse Key := [(key2379, 2), (key2393, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2595, -2), (key2603, 2), (key2771, 2), (key2774, -2), (key2882, 4), (key2912, -2), (key2914, -2), (key2933, -2), (key2934, 2), (key2991, -2), (key2993, -2), (key3003, 4)]

def row5831 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2933, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5832 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2933, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5833 : Integer.Sparse Key := [(key2407, 2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2592, 2), (key2595, -2), (key2602, -2), (key2603, 2), (key2774, -2), (key2882, 4), (key2912, -2), (key2914, -2), (key2934, 2), (key2991, -2), (key2993, -2), (key3003, 4)]

def row5834 : Integer.Sparse Key := [(key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5835 : Integer.Sparse Key := [(key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2592, -1), (key2595, 1), (key2602, 1), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 1), (key2914, 1), (key2934, -1), (key2991, 1), (key2993, 1), (key3003, -2)]

def row5836 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2441, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, 2), (key2555, -1), (key2565, -2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, -1), (key2914, 1), (key2933, 2), (key2934, -1), (key2991, 2), (key2993, 1)]

def row5837 : Integer.Sparse Key := [(key2379, -1), (key2393, 1), (key2441, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, 2), (key2555, -1), (key2565, -2), (key2595, 1), (key2603, -1), (key2771, -1), (key2774, 1), (key2882, -2), (key2912, -1), (key2914, 1), (key2933, 2), (key2934, -1), (key2991, 2), (key2993, 1)]

def row5838 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, -1), (key2555, 2), (key2565, -2), (key2592, -1), (key2595, 1), (key2602, 2), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 2), (key2914, 1), (key2934, -1), (key2991, -1), (key2993, 1)]

def row5839 : Integer.Sparse Key := [(key2393, -1), (key2407, -1), (key2441, 1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2544, -1), (key2555, 2), (key2565, -2), (key2592, -1), (key2595, 1), (key2602, 2), (key2603, -1), (key2774, 1), (key2882, -2), (key2912, 2), (key2914, 1), (key2934, -1), (key2991, -1), (key2993, 1)]

def row5840 : Integer.Sparse Key := [(key2379, 2), (key2393, -2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2544, -2), (key2555, -2), (key2565, 4), (key2595, -2), (key2603, 2), (key2771, 2), (key2774, -2), (key2882, 4), (key2914, -2), (key2934, 2), (key2993, -2)]

def row5841 : Integer.Sparse Key := [(key2393, -2), (key2407, 2), (key2441, -2), (key2473, -4), (key2483, 4), (key2507, 4), (key2526, -4), (key2544, -2), (key2555, -2), (key2565, 4), (key2592, 2), (key2595, -2), (key2603, 2), (key2774, -2), (key2882, 4), (key2914, -2), (key2934, 2), (key2993, -2)]

def row5842 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, -1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2771, -1), (key2774, -1), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

def row5843 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, -1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2771, -1), (key2774, -1), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2933, 2), (key2970, -1), (key2991, -1)]

def row5844 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2771, 2), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2933, -1), (key2970, 2), (key2991, -1)]

def row5845 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2771, 2), (key2774, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2933, -1), (key2970, 2), (key2991, -1)]

def row5846 : Integer.Sparse Key := [(key2382, 2), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2602, 2), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2970, -1), (key2991, -1)]

def row5847 : Integer.Sparse Key := [(key2382, 2), (key2393, -1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2483, -1), (key2507, -1), (key2526, 2), (key2539, -4), (key2544, 2), (key2545, 1), (key2555, 2), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2602, 2), (key2848, 2), (key2882, 2), (key2891, -1), (key2912, -1), (key2970, -1), (key2991, -1)]

def row5848 : Integer.Sparse Key := [(key2382, -1), (key2393, 2), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2592, -1), (key2595, 2), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2970, 2), (key2991, -1)]

def row5849 : Integer.Sparse Key := [(key2382, -1), (key2393, 2), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 2), (key2507, -1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2592, -1), (key2595, 2), (key2602, -1), (key2848, -1), (key2882, -1), (key2891, -1), (key2912, 2), (key2970, 2), (key2991, -1)]

def row5850 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2595, 2), (key2771, 2), (key2774, -1), (key2882, -1), (key2912, 2), (key2933, -1), (key2991, -1)]

def row5851 : Integer.Sparse Key := [(key2379, -1), (key2382, -1), (key2393, 1), (key2395, -1), (key2410, -1), (key2441, -1), (key2445, 2), (key2473, -1), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 2), (key2544, -4), (key2545, 1), (key2555, 2), (key2557, -2), (key2565, 1), (key2595, 2), (key2771, 2), (key2774, -1), (key2882, -1), (key2912, 2), (key2933, -1), (key2991, -1)]

def row5852 : Integer.Sparse Key := [(key2379, -1), (key2382, 2), (key2393, 1), (key2395, -1), (key2410, 2), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -4), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2595, -1), (key2771, -1), (key2774, -1), (key2882, 2)]

def row5853 : Integer.Sparse Key := [(key2382, 2), (key2393, 1), (key2395, -1), (key2407, -1), (key2410, 2), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -4), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2592, -1), (key2595, -1), (key2774, -1), (key2882, 2)]

def row5854 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, -2), (key2545, 1), (key2555, 1), (key2557, -2), (key2565, 1), (key2592, -1), (key2848, -1)]

def row5855 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, 2), (key2410, -2), (key2441, -2), (key2445, 2), (key2483, 1), (key2507, 1), (key2526, -1), (key2539, 1), (key2544, -2), (key2545, 1), (key2555, 1), (key2557, -2), (key2565, 1), (key2592, -1), (key2848, -1)]

def row5856 : Integer.Sparse Key := [(key2379, -1), (key2382, 1), (key2393, 1), (key2395, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2771, -1)]

def row5857 : Integer.Sparse Key := [(key2382, 1), (key2393, 1), (key2395, -1), (key2407, -1), (key2410, 1), (key2441, 1), (key2445, -1), (key2473, 2), (key2483, -2), (key2507, -2), (key2526, 2), (key2539, -2), (key2544, 1), (key2545, 1), (key2555, 1), (key2557, 1), (key2565, -2), (key2592, -1)]

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

def row6178 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -2), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6179 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 2), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -2), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, 1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6180 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2778, -1), (key2784, -1), (key2792, 2), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6181 : Integer.Sparse Key := [(key2630, 1), (key2638, -3), (key2657, 1), (key2659, 1), (key2698, 1), (key2704, 1), (key2752, -2), (key2778, -1), (key2784, -1), (key2792, 2), (key2807, -1), (key2827, 3), (key2918, 2), (key2919, -1), (key2922, -1), (key3011, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6182 : Integer.Sparse Key := [(key2630, 1), (key2638, -2), (key2659, 1), (key2704, 1), (key2757, 1), (key2784, -1), (key2807, -1), (key2827, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key3009, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6183 : Integer.Sparse Key := [(key2630, 1), (key2638, -2), (key2659, 1), (key2704, 1), (key2757, 1), (key2784, -1), (key2807, -1), (key2827, 2), (key2918, 2), (key2919, -1), (key2922, -1), (key3009, -1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6184 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6185 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6186 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6187 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6188 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6189 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6190 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6191 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6192 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6193 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6194 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6195 : Integer.Sparse Key := [(key2630, 1), (key2638, -1), (key2657, -1), (key2659, 1), (key2704, 1), (key2724, -1), (key2752, -1), (key2757, 1), (key2784, -1), (key2792, 1), (key2807, -1), (key2827, 1), (key2918, 2), (key2919, -1), (key2922, -1), (key3007, 1), (key3009, -1), (key3011, 1), (key3016, -1), (key3021, -2), (key3022, 1), (key3025, 1)]

def row6196 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6197 : Integer.Sparse Key := [(key2630, -2), (key2638, 2), (key2657, 2), (key2659, -2), (key2704, -2), (key2724, 2), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, -2), (key2807, 2), (key2827, -2), (key2918, -4), (key2919, 2), (key2922, 2), (key3007, -2), (key3009, 2), (key3011, -2), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

def row6238 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6239 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6240 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6241 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6242 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6243 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6244 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6245 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6246 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6247 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, 2), (key2629, -2), (key2664, 2), (key2668, -2), (key2699, -2), (key2703, 2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, 2), (key2806, -4), (key2826, 2), (key2857, 2), (key2867, -2), (key2937, -2), (key2942, 2), (key2949, 2), (key2959, -2), (key2975, -2), (key2982, 2)]

def row6248 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6249 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6250 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6251 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6252 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6253 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6254 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6255 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6256 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6257 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6258 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6259 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6260 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6261 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

def row6262 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

def row6263 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, -1), (key2629, 1), (key2664, -1), (key2668, 1), (key2699, 1), (key2703, -1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, -1), (key2806, 2), (key2826, -1), (key2857, -1), (key2867, 1), (key2937, 1), (key2942, -1), (key2949, -1), (key2959, 1), (key2975, 1), (key2982, -1)]

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

def row6272 : Integer.Sparse Key := [(key2629, 1), (key2637, -1), (key2647, -1), (key2652, 1), (key2703, -1), (key2723, 1), (key2736, 1), (key2746, -1), (key2783, 1), (key2791, -1), (key2806, -1), (key2826, 1), (key2857, 2), (key2867, -2), (key2896, -1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, 1), (key2959, -1), (key2975, -1), (key2982, 1)]

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

def nodeValue1174 : Sparse Master := [(Sum.inr 1174, (1 / 1))]

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

def nodeValue1233 : Sparse Master := [(Sum.inr 1233, (1 / 1))]

def nodeValue1234 : Sparse Master := [(Sum.inr 1234, (1 / 1))]

def nodeValue1235 : Sparse Master := [(Sum.inr 1235, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


