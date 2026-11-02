-- Prove2me | Definitions.Def_OAIQ106D098
-- name    : OAIQ106D098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:02:22.922386+00:00
-- url     : https://prove2.me/theorems/da8388e2-b1f7-4eee-abcc-381ddcc17ac1
-- title:
--   Definitions bundle OAIQ106D098 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 326 declarations of OpenAI's Lean: 326 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow16324`, `OAI.MUB6.Certificate.GramRows.rawRow16325`, `OAI.MUB6.Certificate.GramRows.rawRow16326`, `OAI.MUB6.Certificate.GramRows.rawRow16327`, `OAI.MUB6.Certificate.GramRows.rawRow16328`, `OAI.MUB6.Certificate.GramRows.rawRow16329`, `OAI.MUB6.Certificate.GramRows.rawRow16330`, `OAI.MUB6.Certificate.GramRows.rawRow16331`, `OAI.MUB6.Certificate.GramRows.rawRow16332`, `OAI.MUB6.Certificate.GramRows.rawRow16333`, `OAI.MUB6.Certificate.GramRows.rawRow16334`, `OAI.MUB6.Certificate.GramRows.rawRow16335`, `OAI.MUB6.Certificate.GramRows.rawRow16336`, `OAI.MUB6.Certificate.GramRows.rawRow16337`, `OAI.MUB6.Certificate.GramRows.rawRow16338`, `OAI.MUB6.Certificate.GramRows.rawRow16339`, `OAI.MUB6.Certificate.GramRows.rawRow16340`, `OAI.MUB6.Certificate.GramRows.rawRow16341`, `OAI.MUB6.Certificate.GramRows.rawRow16342`, `OAI.MUB6.Certificate.GramRows.rawRow16343`, `OAI.MUB6.Certificate.GramRows.rawRow16344`, `OAI.MUB6.Certificate.GramRows.rawRow16345`, `OAI.MUB6.Certificate.GramRows.rawRow16346`, `OAI.MUB6.Certificate.GramRows.rawRow16383`, `OAI.MUB6.Certificate.GramRows.rawRow16384`, `OAI.MUB6.Certificate.GramRows.rawRow16385`, `OAI.MUB6.Certificate.GramRows.rawRow16386`, `OAI.MUB6.Certificate.GramRows.rawRow16387`, `OAI.MUB6.Certificate.GramRows.rawRow16388`, `OAI.MUB6.Certificate.GramRows.rawRow16389`, `OAI.MUB6.Certificate.GramRows.rawRow16390`, `OAI.MUB6.Certificate.GramRows.rawRow16391`, `OAI.MUB6.Certificate.GramRows.rawRow16392`, `OAI.MUB6.Certificate.GramRows.rawRow16393`, `OAI.MUB6.Certificate.GramRows.rawRow16394`, `OAI.MUB6.Certificate.GramRows.rawRow16395`, `OAI.MUB6.Certificate.GramRows.rawRow16396`, `OAI.MUB6.Certificate.GramRows.rawRow16397`, `OAI.MUB6.Certificate.GramRows.rawRow16398`, `OAI.MUB6.Certificate.GramRows.rawRow16399` and 286 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_Interpretation`, `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block151`, `MutuallyUnbiased_GramRows_Block152`, `MutuallyUnbiased_GramRows_Block153`, `MutuallyUnbiased_GramRows_Block154`, `MutuallyUnbiased_GramRows_Block169`, `MutuallyUnbiased_GramRows_Block2`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block38`, `MutuallyUnbiased_GramRows_Block93`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values19`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D183`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEval2_2`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Integer.Sparse

variable {ι κ Ω : Type*}

def reindex (f : ι → κ) (v : Integer.Sparse ι) : Integer.Sparse κ :=
  v.map fun p => (f p.1, p.2)

end Integer.Sparse
end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17 : Integer.Sparse Key := [(key335, -1), (key335, -1), (key340, 2), (key305, 1), (key305, 1), (key328, -1), (key328, -1), (key302, -2), (key316, 1), (key316, 1), (key578, 1), (key578, 1), (key583, -2), (key239, -1), (key239, -1), (key418, 1), (key418, 1), (key236, 2), (key406, -1), (key406, -1), (key328, -1), (key328, -1), (key601, 1), (key601, 1), (key260, 1), (key260, 1), (key595, -1), (key595, -1), (key248, -1), (key248, -1), (key316, 1), (key316, 1), (key340, 2), (key475, -1), (key475, -1), (key271, -2), (key469, 1), (key469, 1), (key267, 1), (key267, 1), (key335, -1), (key335, -1)]

def rawRow18 : Integer.Sparse Key := [(key335, -1), (key340, -1), (key335, 2), (key319, 1), (key328, 1), (key305, -1), (key319, -1), (key316, -2), (key302, 1), (key316, 1), (key578, 1), (key583, 1), (key578, -2), (key409, -1), (key418, -1), (key239, 1), (key409, 1), (key406, 2), (key236, -1), (key406, -1), (key450, -1), (key601, -1), (key328, 1), (key450, 1), (key442, 1), (key595, 1), (key260, -1), (key442, -1), (key316, -1), (key435, -1), (key248, 1), (key435, 1), (key475, 2), (key340, -1), (key475, -1), (key469, -2), (key271, 1), (key469, 1), (key335, 1), (key467, 1), (key267, -1), (key467, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16324 : Integer.Sparse Key := [(key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2628, 2), (key2972, 2), (key2702, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1), (key2644, 2), (key2885, 2), (key2798, 2), (key2644, -1), (key2621, -1), (key2732, -1), (key2676, -1), (key2835, -1), (key2798, -1)]

def rawRow16325 : Integer.Sparse Key := [(key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2702, 2), (key2628, 2), (key2972, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2798, 2), (key2644, 2), (key2885, 2), (key2676, -1), (key2798, -1), (key2621, -1), (key2835, -1), (key2644, -1), (key2732, -1)]

def rawRow16326 : Integer.Sparse Key := [(key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2702, 2), (key2972, 2), (key2628, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1), (key2798, 2), (key2885, 2), (key2644, 2), (key2798, -1), (key2676, -1), (key2835, -1), (key2621, -1), (key2732, -1), (key2644, -1)]

def rawRow16327 : Integer.Sparse Key := [(key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2972, 2), (key2628, 2), (key2702, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1), (key2885, 2), (key2644, 2), (key2798, 2), (key2732, -1), (key2835, -1), (key2644, -1), (key2798, -1), (key2621, -1), (key2676, -1)]

def rawRow16328 : Integer.Sparse Key := [(key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2972, 2), (key2702, 2), (key2628, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2885, 2), (key2798, 2), (key2644, 2), (key2835, -1), (key2732, -1), (key2798, -1), (key2644, -1), (key2676, -1), (key2621, -1)]

def rawRow16329 : Integer.Sparse Key := [(key2646, -1), (key2648, -1), (key2893, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2653, 2), (key2897, 2), (key2998, 2), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2628, 2), (key2648, 2), (key2782, 2), (key2938, 2), (key2904, 2), (key2983, 2), (key2641, -1), (key2653, -1), (key2795, -1), (key2943, -1), (key2897, -1), (key2976, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1)]

def rawRow16330 : Integer.Sparse Key := [(key2648, -1), (key2646, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2904, -1), (key2653, 2), (key2998, 2), (key2897, 2), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2648, 2), (key2628, 2), (key2938, 2), (key2782, 2), (key2983, 2), (key2904, 2), (key2653, -1), (key2641, -1), (key2943, -1), (key2795, -1), (key2976, -1), (key2897, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1)]

def rawRow16331 : Integer.Sparse Key := [(key2893, -1), (key2904, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2897, 2), (key2653, 2), (key2998, 2), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2782, 2), (key2904, 2), (key2628, 2), (key2983, 2), (key2648, 2), (key2938, 2), (key2795, -1), (key2897, -1), (key2641, -1), (key2976, -1), (key2653, -1), (key2943, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1)]

def rawRow16332 : Integer.Sparse Key := [(key2904, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2997, -1), (key2648, -1), (key2897, 2), (key2998, 2), (key2653, 2), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2904, 2), (key2782, 2), (key2983, 2), (key2628, 2), (key2938, 2), (key2648, 2), (key2897, -1), (key2795, -1), (key2976, -1), (key2641, -1), (key2943, -1), (key2653, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1)]

def rawRow16333 : Integer.Sparse Key := [(key2997, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2646, -1), (key2893, -1), (key2998, 2), (key2653, 2), (key2897, 2), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2938, 2), (key2983, 2), (key2648, 2), (key2904, 2), (key2628, 2), (key2782, 2), (key2943, -1), (key2976, -1), (key2653, -1), (key2897, -1), (key2641, -1), (key2795, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1)]

def rawRow16334 : Integer.Sparse Key := [(key3000, -1), (key2997, -1), (key2904, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key2998, 2), (key2897, 2), (key2653, 2), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 2), (key2938, 2), (key2904, 2), (key2648, 2), (key2782, 2), (key2628, 2), (key2976, -1), (key2943, -1), (key2897, -1), (key2653, -1), (key2795, -1), (key2641, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1)]

def rawRow16335 : Integer.Sparse Key := [(key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2648, 2), (key2737, 2), (key2997, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2), (key2618, -1), (key2648, -1), (key2673, -1), (key2938, -1), (key2737, -1), (key2950, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1)]

def rawRow16336 : Integer.Sparse Key := [(key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2648, 2), (key2997, 2), (key2737, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2), (key2648, -1), (key2618, -1), (key2938, -1), (key2673, -1), (key2950, -1), (key2737, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1)]

def rawRow16337 : Integer.Sparse Key := [(key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2737, 2), (key2648, 2), (key2997, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2), (key2673, -1), (key2737, -1), (key2618, -1), (key2950, -1), (key2648, -1), (key2938, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1)]

def rawRow16338 : Integer.Sparse Key := [(key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2737, 2), (key2997, 2), (key2648, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2), (key2737, -1), (key2673, -1), (key2950, -1), (key2618, -1), (key2938, -1), (key2648, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1)]

def rawRow16339 : Integer.Sparse Key := [(key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2997, 2), (key2648, 2), (key2737, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2), (key2938, -1), (key2950, -1), (key2648, -1), (key2737, -1), (key2618, -1), (key2673, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1)]

def rawRow16340 : Integer.Sparse Key := [(key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2997, 2), (key2737, 2), (key2648, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2), (key2950, -1), (key2938, -1), (key2737, -1), (key2648, -1), (key2673, -1), (key2618, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1)]

def rawRow16341 : Integer.Sparse Key := [(key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2646, 2), (key2735, 2), (key2893, 2), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2618, 2), (key2641, 2), (key2673, 2), (key2795, 2), (key2728, 2), (key2831, 2), (key2612, -1), (key2628, -1), (key2667, -1), (key2782, -1), (key2702, -1), (key2805, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1)]

def rawRow16342 : Integer.Sparse Key := [(key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2646, 2), (key2893, 2), (key2735, 2), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2641, 2), (key2618, 2), (key2795, 2), (key2673, 2), (key2831, 2), (key2728, 2), (key2628, -1), (key2612, -1), (key2782, -1), (key2667, -1), (key2805, -1), (key2702, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1)]

def rawRow16343 : Integer.Sparse Key := [(key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2735, 2), (key2646, 2), (key2893, 2), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2673, 2), (key2728, 2), (key2618, 2), (key2831, 2), (key2641, 2), (key2795, 2), (key2667, -1), (key2702, -1), (key2612, -1), (key2805, -1), (key2628, -1), (key2782, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1)]

def rawRow16344 : Integer.Sparse Key := [(key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2735, 2), (key2893, 2), (key2646, 2), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2728, 2), (key2673, 2), (key2831, 2), (key2618, 2), (key2795, 2), (key2641, 2), (key2702, -1), (key2667, -1), (key2805, -1), (key2612, -1), (key2782, -1), (key2628, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1)]

def rawRow16345 : Integer.Sparse Key := [(key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2893, 2), (key2646, 2), (key2735, 2), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2795, 2), (key2831, 2), (key2641, 2), (key2728, 2), (key2618, 2), (key2673, 2), (key2782, -1), (key2805, -1), (key2628, -1), (key2702, -1), (key2612, -1), (key2667, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1)]

def rawRow16346 : Integer.Sparse Key := [(key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2893, 2), (key2735, 2), (key2646, 2), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2831, 2), (key2795, 2), (key2728, 2), (key2641, 2), (key2673, 2), (key2618, 2), (key2805, -1), (key2782, -1), (key2702, -1), (key2628, -1), (key2667, -1), (key2612, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1)]

def rawRow16383 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2773, 6), (key2847, -2), (key2847, -2), (key2969, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2594, -2), (key2881, -2), (key2881, -2), (key2890, 6), (key2601, -2), (key2911, -2), (key2911, -2)]

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

def rawRow16384 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 6), (key2847, -2), (key2969, -2), (key2847, -2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2881, -2), (key2594, -2), (key2881, -2), (key2890, 6), (key2911, -2), (key2601, -2), (key2911, -2)]

def rawRow16385 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2773, 6), (key2969, -2), (key2847, -2), (key2847, -2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2881, -2), (key2881, -2), (key2594, -2), (key2890, 6), (key2911, -2), (key2911, -2), (key2601, -2)]

def rawRow16386 : Integer.Sparse Key := [(key2770, -2), (key2773, -2), (key2932, -2), (key2770, 6), (key2878, -2), (key2881, -2), (key2990, -2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2591, -2), (key2847, -2), (key2878, -2), (key2911, 6), (key2601, -2), (key2890, -2), (key2911, -2)]

def rawRow16387 : Integer.Sparse Key := [(key2773, -2), (key2770, -2), (key2932, -2), (key2770, 6), (key2881, -2), (key2878, -2), (key2990, -2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2591, -2), (key2878, -2), (key2847, -2), (key2911, 6), (key2601, -2), (key2911, -2), (key2890, -2)]

def rawRow16388 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2773, -2), (key2770, 6), (key2878, -2), (key2990, -2), (key2881, -2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2847, -2), (key2591, -2), (key2878, -2), (key2911, 6), (key2890, -2), (key2601, -2), (key2911, -2)]

def rawRow16389 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2773, -2), (key2770, 6), (key2990, -2), (key2878, -2), (key2881, -2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2847, -2), (key2878, -2), (key2591, -2), (key2911, 6), (key2890, -2), (key2911, -2), (key2601, -2)]

def rawRow16390 : Integer.Sparse Key := [(key2773, -2), (key2932, -2), (key2770, -2), (key2770, 6), (key2881, -2), (key2990, -2), (key2878, -2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2878, -2), (key2591, -2), (key2847, -2), (key2911, 6), (key2911, -2), (key2601, -2), (key2890, -2)]

def rawRow16391 : Integer.Sparse Key := [(key2932, -2), (key2773, -2), (key2770, -2), (key2770, 6), (key2990, -2), (key2881, -2), (key2878, -2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2878, -2), (key2847, -2), (key2591, -2), (key2911, 6), (key2911, -2), (key2890, -2), (key2601, -2)]

def rawRow16392 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2890, 6), (key2770, -2), (key2770, -2), (key2932, -2), (key2591, 2), (key2591, 2), (key2878, 2), (key2878, 2), (key2990, 2), (key2990, 2), (key2601, -2), (key2911, -2), (key2911, -2), (key2773, 6), (key2594, -2), (key2881, -2), (key2881, -2)]

def rawRow16393 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2890, 6), (key2770, -2), (key2932, -2), (key2770, -2), (key2878, 2), (key2990, 2), (key2591, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2911, -2), (key2601, -2), (key2911, -2), (key2773, 6), (key2881, -2), (key2594, -2), (key2881, -2)]

def rawRow16394 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2890, 6), (key2932, -2), (key2770, -2), (key2770, -2), (key2990, 2), (key2878, 2), (key2990, 2), (key2591, 2), (key2878, 2), (key2591, 2), (key2911, -2), (key2911, -2), (key2601, -2), (key2773, 6), (key2881, -2), (key2881, -2), (key2594, -2)]

def rawRow16395 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2969, -2), (key2847, 6), (key2878, -2), (key2911, -2), (key2990, -2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2591, -2), (key2770, -2), (key2878, -2), (key2881, 6), (key2594, -2), (key2773, -2), (key2881, -2)]

def rawRow16396 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2969, -2), (key2847, 6), (key2911, -2), (key2878, -2), (key2990, -2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2591, -2), (key2878, -2), (key2770, -2), (key2881, 6), (key2594, -2), (key2881, -2), (key2773, -2)]

def rawRow16397 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2890, -2), (key2847, 6), (key2878, -2), (key2990, -2), (key2911, -2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2770, -2), (key2591, -2), (key2878, -2), (key2881, 6), (key2773, -2), (key2594, -2), (key2881, -2)]

def rawRow16398 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2890, -2), (key2847, 6), (key2990, -2), (key2878, -2), (key2911, -2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2770, -2), (key2878, -2), (key2591, -2), (key2881, 6), (key2773, -2), (key2881, -2), (key2594, -2)]

def rawRow16399 : Integer.Sparse Key := [(key2890, -2), (key2969, -2), (key2847, -2), (key2847, 6), (key2911, -2), (key2990, -2), (key2878, -2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2878, -2), (key2591, -2), (key2770, -2), (key2881, 6), (key2881, -2), (key2594, -2), (key2773, -2)]

def rawRow16400 : Integer.Sparse Key := [(key2969, -2), (key2890, -2), (key2847, -2), (key2847, 6), (key2990, -2), (key2911, -2), (key2878, -2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2878, -2), (key2770, -2), (key2591, -2), (key2881, 6), (key2881, -2), (key2773, -2), (key2594, -2)]

def rawRow16401 : Integer.Sparse Key := [(key2878, -2), (key2881, -2), (key2990, -2), (key2911, 6), (key2770, -2), (key2773, -2), (key2932, -2), (key2591, 2), (key2594, 2), (key2847, 2), (key2881, 2), (key2969, 2), (key2990, 2), (key2601, -2), (key2890, -2), (key2911, -2), (key2770, 6), (key2591, -2), (key2847, -2), (key2878, -2)]

def rawRow16402 : Integer.Sparse Key := [(key2881, -2), (key2878, -2), (key2990, -2), (key2911, 6), (key2773, -2), (key2770, -2), (key2932, -2), (key2594, 2), (key2591, 2), (key2881, 2), (key2847, 2), (key2990, 2), (key2969, 2), (key2601, -2), (key2911, -2), (key2890, -2), (key2770, 6), (key2591, -2), (key2878, -2), (key2847, -2)]

def rawRow16403 : Integer.Sparse Key := [(key2878, -2), (key2990, -2), (key2881, -2), (key2911, 6), (key2770, -2), (key2932, -2), (key2773, -2), (key2847, 2), (key2969, 2), (key2591, 2), (key2990, 2), (key2594, 2), (key2881, 2), (key2890, -2), (key2601, -2), (key2911, -2), (key2770, 6), (key2847, -2), (key2591, -2), (key2878, -2)]

def rawRow16404 : Integer.Sparse Key := [(key2990, -2), (key2878, -2), (key2881, -2), (key2911, 6), (key2932, -2), (key2770, -2), (key2773, -2), (key2969, 2), (key2847, 2), (key2990, 2), (key2591, 2), (key2881, 2), (key2594, 2), (key2890, -2), (key2911, -2), (key2601, -2), (key2770, 6), (key2847, -2), (key2878, -2), (key2591, -2)]

def rawRow16405 : Integer.Sparse Key := [(key2881, -2), (key2990, -2), (key2878, -2), (key2911, 6), (key2773, -2), (key2932, -2), (key2770, -2), (key2881, 2), (key2990, 2), (key2594, 2), (key2969, 2), (key2591, 2), (key2847, 2), (key2911, -2), (key2601, -2), (key2890, -2), (key2770, 6), (key2878, -2), (key2591, -2), (key2847, -2)]

def rawRow16406 : Integer.Sparse Key := [(key2990, -2), (key2881, -2), (key2878, -2), (key2911, 6), (key2932, -2), (key2773, -2), (key2770, -2), (key2990, 2), (key2881, 2), (key2969, 2), (key2594, 2), (key2847, 2), (key2591, 2), (key2911, -2), (key2890, -2), (key2601, -2), (key2770, 6), (key2878, -2), (key2847, -2), (key2591, -2)]

def rawRow16407 : Integer.Sparse Key := [(key2878, -2), (key2911, -2), (key2990, -2), (key2881, 6), (key2847, -2), (key2890, -2), (key2969, -2), (key2591, 2), (key2601, 2), (key2770, 2), (key2911, 2), (key2932, 2), (key2990, 2), (key2594, -2), (key2773, -2), (key2881, -2), (key2847, 6), (key2591, -2), (key2770, -2), (key2878, -2)]

def rawRow16408 : Integer.Sparse Key := [(key2911, -2), (key2878, -2), (key2990, -2), (key2881, 6), (key2890, -2), (key2847, -2), (key2969, -2), (key2601, 2), (key2591, 2), (key2911, 2), (key2770, 2), (key2990, 2), (key2932, 2), (key2594, -2), (key2881, -2), (key2773, -2), (key2847, 6), (key2591, -2), (key2878, -2), (key2770, -2)]

def rawRow16409 : Integer.Sparse Key := [(key2878, -2), (key2990, -2), (key2911, -2), (key2881, 6), (key2847, -2), (key2969, -2), (key2890, -2), (key2770, 2), (key2932, 2), (key2591, 2), (key2990, 2), (key2601, 2), (key2911, 2), (key2773, -2), (key2594, -2), (key2881, -2), (key2847, 6), (key2770, -2), (key2591, -2), (key2878, -2)]

def rawRow16410 : Integer.Sparse Key := [(key2990, -2), (key2878, -2), (key2911, -2), (key2881, 6), (key2969, -2), (key2847, -2), (key2890, -2), (key2932, 2), (key2770, 2), (key2990, 2), (key2591, 2), (key2911, 2), (key2601, 2), (key2773, -2), (key2881, -2), (key2594, -2), (key2847, 6), (key2770, -2), (key2878, -2), (key2591, -2)]

def rawRow16411 : Integer.Sparse Key := [(key2911, -2), (key2990, -2), (key2878, -2), (key2881, 6), (key2890, -2), (key2969, -2), (key2847, -2), (key2911, 2), (key2990, 2), (key2601, 2), (key2932, 2), (key2591, 2), (key2770, 2), (key2881, -2), (key2594, -2), (key2773, -2), (key2847, 6), (key2878, -2), (key2591, -2), (key2770, -2)]

def rawRow16412 : Integer.Sparse Key := [(key2990, -2), (key2911, -2), (key2878, -2), (key2881, 6), (key2969, -2), (key2890, -2), (key2847, -2), (key2990, 2), (key2911, 2), (key2932, 2), (key2601, 2), (key2770, 2), (key2591, 2), (key2881, -2), (key2773, -2), (key2594, -2), (key2847, 6), (key2878, -2), (key2770, -2), (key2591, -2)]

def rawRow16413 : Integer.Sparse Key := [(key2881, -2), (key2911, -2), (key2990, -2), (key2878, 6), (key2881, -2), (key2911, -2), (key2990, -2), (key2594, 2), (key2601, 2), (key2773, 2), (key2890, 2), (key2932, 2), (key2969, 2), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6), (key2591, -2), (key2770, -2), (key2847, -2)]

def rawRow16414 : Integer.Sparse Key := [(key2911, -2), (key2881, -2), (key2990, -2), (key2878, 6), (key2911, -2), (key2881, -2), (key2990, -2), (key2601, 2), (key2594, 2), (key2890, 2), (key2773, 2), (key2969, 2), (key2932, 2), (key2591, -2), (key2847, -2), (key2770, -2), (key2878, 6), (key2591, -2), (key2847, -2), (key2770, -2)]

def rawRow16415 : Integer.Sparse Key := [(key2881, -2), (key2990, -2), (key2911, -2), (key2878, 6), (key2881, -2), (key2990, -2), (key2911, -2), (key2773, 2), (key2932, 2), (key2594, 2), (key2969, 2), (key2601, 2), (key2890, 2), (key2770, -2), (key2591, -2), (key2847, -2), (key2878, 6), (key2770, -2), (key2591, -2), (key2847, -2)]

def rawRow16416 : Integer.Sparse Key := [(key2990, -2), (key2881, -2), (key2911, -2), (key2878, 6), (key2990, -2), (key2881, -2), (key2911, -2), (key2932, 2), (key2773, 2), (key2969, 2), (key2594, 2), (key2890, 2), (key2601, 2), (key2770, -2), (key2847, -2), (key2591, -2), (key2878, 6), (key2770, -2), (key2847, -2), (key2591, -2)]

def rawRow16417 : Integer.Sparse Key := [(key2911, -2), (key2990, -2), (key2881, -2), (key2878, 6), (key2911, -2), (key2990, -2), (key2881, -2), (key2890, 2), (key2969, 2), (key2601, 2), (key2932, 2), (key2594, 2), (key2773, 2), (key2847, -2), (key2591, -2), (key2770, -2), (key2878, 6), (key2847, -2), (key2591, -2), (key2770, -2)]

def rawRow16418 : Integer.Sparse Key := [(key2990, -2), (key2911, -2), (key2881, -2), (key2878, 6), (key2990, -2), (key2911, -2), (key2881, -2), (key2969, 2), (key2890, 2), (key2932, 2), (key2601, 2), (key2773, 2), (key2594, 2), (key2847, -2), (key2770, -2), (key2591, -2), (key2878, 6), (key2847, -2), (key2770, -2), (key2591, -2)]

def rawRow16455 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key2992, 2), (key2992, 2), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1)]

def rawRow16456 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key2992, 2), (key2640, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1)]

def rawRow16457 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2992, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1)]

def rawRow16458 : Integer.Sparse Key := [(key2616, -1), (key2619, -1), (key2809, -1), (key2832, -1), (key2951, -1), (key2961, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2640, -1), (key2642, -1), (key2860, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2632, 2), (key2642, 2), (key2706, 2), (key2729, 2), (key2977, 2), (key2984, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1), (key2654, 2), (key2898, 2), (key2913, 2), (key2649, -1), (key2654, -1), (key2738, -1), (key2748, -1), (key2898, -1), (key2905, -1)]

def rawRow16459 : Integer.Sparse Key := [(key2619, -1), (key2616, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2951, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2642, -1), (key2640, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2977, -1), (key2642, 2), (key2632, 2), (key2729, 2), (key2706, 2), (key2984, 2), (key2977, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1), (key2654, 2), (key2913, 2), (key2898, 2), (key2654, -1), (key2649, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2898, -1)]

def rawRow16460 : Integer.Sparse Key := [(key2809, -1), (key2951, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2860, -1), (key2977, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2706, 2), (key2977, 2), (key2632, 2), (key2984, 2), (key2642, 2), (key2729, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2898, 2), (key2654, 2), (key2913, 2), (key2738, -1), (key2898, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2748, -1)]

def rawRow16461 : Integer.Sparse Key := [(key2951, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2832, -1), (key2619, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2977, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2883, -1), (key2642, -1), (key2977, 2), (key2706, 2), (key2984, 2), (key2632, 2), (key2729, 2), (key2642, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1), (key2898, 2), (key2913, 2), (key2654, 2), (key2898, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2748, -1), (key2654, -1)]

def rawRow16462 : Integer.Sparse Key := [(key2832, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2616, -1), (key2809, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2883, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2640, -1), (key2860, -1), (key2729, 2), (key2984, 2), (key2642, 2), (key2977, 2), (key2632, 2), (key2706, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1), (key2913, 2), (key2654, 2), (key2898, 2), (key2748, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2649, -1), (key2738, -1)]

def rawRow16463 : Integer.Sparse Key := [(key2961, -1), (key2832, -1), (key2951, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2992, -1), (key2883, -1), (key2977, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2984, 2), (key2729, 2), (key2977, 2), (key2642, 2), (key2706, 2), (key2632, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2913, 2), (key2898, 2), (key2654, 2), (key2905, -1), (key2748, -1), (key2898, -1), (key2654, -1), (key2738, -1), (key2649, -1)]

def rawRow16464 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key2992, 2), (key2992, 2), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1)]

def rawRow16465 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key2992, 2), (key2640, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1)]

def rawRow16466 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2992, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2640, 2), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1)]

def rawRow16467 : Integer.Sparse Key := [(key2632, -1), (key2649, -1), (key2786, -1), (key2905, -1), (key2939, -1), (key2984, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2913, -1), (key2944, -1), (key2992, -1), (key2616, 2), (key2654, 2), (key2671, 2), (key2748, 2), (key2944, 2), (key2961, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1), (key2642, 2), (key2796, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2729, -1), (key2796, -1), (key2832, -1)]

def rawRow16468 : Integer.Sparse Key := [(key2649, -1), (key2632, -1), (key2905, -1), (key2786, -1), (key2984, -1), (key2939, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2654, -1), (key2640, -1), (key2913, -1), (key2794, -1), (key2992, -1), (key2944, -1), (key2654, 2), (key2616, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2944, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1), (key2642, 2), (key2883, 2), (key2796, 2), (key2642, -1), (key2619, -1), (key2729, -1), (key2674, -1), (key2832, -1), (key2796, -1)]

def rawRow16469 : Integer.Sparse Key := [(key2786, -1), (key2939, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2794, -1), (key2944, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2671, 2), (key2944, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2796, 2), (key2642, 2), (key2883, 2), (key2674, -1), (key2796, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2729, -1)]

def rawRow16470 : Integer.Sparse Key := [(key2939, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2905, -1), (key2649, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2944, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2913, -1), (key2654, -1), (key2944, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2748, 2), (key2654, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1), (key2796, 2), (key2883, 2), (key2642, 2), (key2796, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2729, -1), (key2642, -1)]

def rawRow16471 : Integer.Sparse Key := [(key2905, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2632, -1), (key2786, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2913, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2640, -1), (key2794, -1), (key2748, 2), (key2961, 2), (key2654, 2), (key2944, 2), (key2616, 2), (key2671, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1), (key2883, 2), (key2642, 2), (key2796, 2), (key2729, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2619, -1), (key2674, -1)]

def rawRow16472 : Integer.Sparse Key := [(key2984, -1), (key2905, -1), (key2939, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2992, -1), (key2913, -1), (key2944, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2961, 2), (key2748, 2), (key2944, 2), (key2654, 2), (key2671, 2), (key2616, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2883, 2), (key2796, 2), (key2642, 2), (key2832, -1), (key2729, -1), (key2796, -1), (key2642, -1), (key2674, -1), (key2619, -1)]

def rawRow16473 : Integer.Sparse Key := [(key2640, -1), (key2642, -1), (key2860, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2654, 2), (key2898, 2), (key2913, 2), (key2616, -1), (key2619, -1), (key2809, -1), (key2832, -1), (key2951, -1), (key2961, -1), (key2632, 2), (key2642, 2), (key2706, 2), (key2729, 2), (key2977, 2), (key2984, 2), (key2649, -1), (key2654, -1), (key2738, -1), (key2748, -1), (key2898, -1), (key2905, -1), (key2616, 2), (key2809, 2), (key2829, 2), (key2632, -1), (key2640, -1), (key2706, -1), (key2726, -1), (key2860, -1), (key2870, -1)]

def rawRow16474 : Integer.Sparse Key := [(key2642, -1), (key2640, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2977, -1), (key2654, 2), (key2913, 2), (key2898, 2), (key2619, -1), (key2616, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2951, -1), (key2642, 2), (key2632, 2), (key2729, 2), (key2706, 2), (key2984, 2), (key2977, 2), (key2654, -1), (key2649, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2898, -1), (key2616, 2), (key2829, 2), (key2809, 2), (key2640, -1), (key2632, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2860, -1)]

def rawRow16475 : Integer.Sparse Key := [(key2860, -1), (key2977, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2898, 2), (key2654, 2), (key2913, 2), (key2809, -1), (key2951, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2706, 2), (key2977, 2), (key2632, 2), (key2984, 2), (key2642, 2), (key2729, 2), (key2738, -1), (key2898, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2748, -1), (key2809, 2), (key2616, 2), (key2829, 2), (key2706, -1), (key2860, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2726, -1)]

def rawRow16476 : Integer.Sparse Key := [(key2977, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2883, -1), (key2642, -1), (key2898, 2), (key2913, 2), (key2654, 2), (key2951, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2832, -1), (key2619, -1), (key2977, 2), (key2706, 2), (key2984, 2), (key2632, 2), (key2729, 2), (key2642, 2), (key2898, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2748, -1), (key2654, -1), (key2809, 2), (key2829, 2), (key2616, 2), (key2860, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2726, -1), (key2640, -1)]

def rawRow16477 : Integer.Sparse Key := [(key2883, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2640, -1), (key2860, -1), (key2913, 2), (key2654, 2), (key2898, 2), (key2832, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2616, -1), (key2809, -1), (key2729, 2), (key2984, 2), (key2642, 2), (key2977, 2), (key2632, 2), (key2706, 2), (key2748, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2649, -1), (key2738, -1), (key2829, 2), (key2616, 2), (key2809, 2), (key2726, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2632, -1), (key2706, -1)]

def rawRow16478 : Integer.Sparse Key := [(key2992, -1), (key2883, -1), (key2977, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2913, 2), (key2898, 2), (key2654, 2), (key2961, -1), (key2832, -1), (key2951, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2984, 2), (key2729, 2), (key2977, 2), (key2642, 2), (key2706, 2), (key2632, 2), (key2905, -1), (key2748, -1), (key2898, -1), (key2654, -1), (key2738, -1), (key2649, -1), (key2829, 2), (key2809, 2), (key2616, 2), (key2870, -1), (key2726, -1), (key2860, -1), (key2640, -1), (key2706, -1), (key2632, -1)]

def rawRow16479 : Integer.Sparse Key := [(key2640, -1), (key2654, -1), (key2794, -1), (key2913, -1), (key2944, -1), (key2992, -1), (key2642, 2), (key2796, 2), (key2883, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2905, -1), (key2939, -1), (key2984, -1), (key2616, 2), (key2654, 2), (key2671, 2), (key2748, 2), (key2944, 2), (key2961, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2729, -1), (key2796, -1), (key2832, -1), (key2632, 2), (key2786, 2), (key2870, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2726, -1), (key2794, -1), (key2829, -1)]

def rawRow16480 : Integer.Sparse Key := [(key2654, -1), (key2640, -1), (key2913, -1), (key2794, -1), (key2992, -1), (key2944, -1), (key2642, 2), (key2883, 2), (key2796, 2), (key2649, -1), (key2632, -1), (key2905, -1), (key2786, -1), (key2984, -1), (key2939, -1), (key2654, 2), (key2616, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2944, 2), (key2642, -1), (key2619, -1), (key2729, -1), (key2674, -1), (key2832, -1), (key2796, -1), (key2632, 2), (key2870, 2), (key2786, 2), (key2640, -1), (key2616, -1), (key2726, -1), (key2671, -1), (key2829, -1), (key2794, -1)]

def rawRow16481 : Integer.Sparse Key := [(key2794, -1), (key2944, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2796, 2), (key2642, 2), (key2883, 2), (key2786, -1), (key2939, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2671, 2), (key2944, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2674, -1), (key2796, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2786, 2), (key2632, 2), (key2870, 2), (key2671, -1), (key2794, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2726, -1)]

def rawRow16482 : Integer.Sparse Key := [(key2944, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2913, -1), (key2654, -1), (key2796, 2), (key2883, 2), (key2642, 2), (key2939, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2905, -1), (key2649, -1), (key2944, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2748, 2), (key2654, 2), (key2796, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2729, -1), (key2642, -1), (key2786, 2), (key2870, 2), (key2632, 2), (key2794, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2726, -1), (key2640, -1)]

def rawRow16483 : Integer.Sparse Key := [(key2913, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2640, -1), (key2794, -1), (key2883, 2), (key2642, 2), (key2796, 2), (key2905, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2632, -1), (key2786, -1), (key2748, 2), (key2961, 2), (key2654, 2), (key2944, 2), (key2616, 2), (key2671, 2), (key2729, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2619, -1), (key2674, -1), (key2870, 2), (key2632, 2), (key2786, 2), (key2726, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2616, -1), (key2671, -1)]

def rawRow16484 : Integer.Sparse Key := [(key2992, -1), (key2913, -1), (key2944, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2883, 2), (key2796, 2), (key2642, 2), (key2984, -1), (key2905, -1), (key2939, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2961, 2), (key2748, 2), (key2944, 2), (key2654, 2), (key2671, 2), (key2616, 2), (key2832, -1), (key2729, -1), (key2796, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, 2), (key2786, 2), (key2632, 2), (key2829, -1), (key2726, -1), (key2794, -1), (key2640, -1), (key2671, -1), (key2616, -1)]

def rawRow16485 : Integer.Sparse Key := [(key2642, -1), (key2654, -1), (key2796, -1), (key2898, -1), (key2944, -1), (key2977, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2642, -1), (key2654, -1), (key2796, -1), (key2898, -1), (key2944, -1), (key2977, -1), (key2619, 2), (key2649, 2), (key2674, 2), (key2738, 2), (key2939, 2), (key2951, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1), (key2640, 2), (key2794, 2), (key2860, 2), (key2616, -1), (key2632, -1), (key2671, -1), (key2706, -1), (key2786, -1), (key2809, -1)]

def rawRow16486 : Integer.Sparse Key := [(key2654, -1), (key2642, -1), (key2898, -1), (key2796, -1), (key2977, -1), (key2944, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2654, -1), (key2642, -1), (key2898, -1), (key2796, -1), (key2977, -1), (key2944, -1), (key2649, 2), (key2619, 2), (key2738, 2), (key2674, 2), (key2951, 2), (key2939, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1), (key2640, 2), (key2860, 2), (key2794, 2), (key2632, -1), (key2616, -1), (key2706, -1), (key2671, -1), (key2809, -1), (key2786, -1)]

def rawRow16487 : Integer.Sparse Key := [(key2796, -1), (key2944, -1), (key2642, -1), (key2977, -1), (key2654, -1), (key2898, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2796, -1), (key2944, -1), (key2642, -1), (key2977, -1), (key2654, -1), (key2898, -1), (key2674, 2), (key2939, 2), (key2619, 2), (key2951, 2), (key2649, 2), (key2738, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1), (key2794, 2), (key2640, 2), (key2860, 2), (key2671, -1), (key2786, -1), (key2616, -1), (key2809, -1), (key2632, -1), (key2706, -1)]

def rawRow16488 : Integer.Sparse Key := [(key2944, -1), (key2796, -1), (key2977, -1), (key2642, -1), (key2898, -1), (key2654, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2944, -1), (key2796, -1), (key2977, -1), (key2642, -1), (key2898, -1), (key2654, -1), (key2939, 2), (key2674, 2), (key2951, 2), (key2619, 2), (key2738, 2), (key2649, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1), (key2794, 2), (key2860, 2), (key2640, 2), (key2786, -1), (key2671, -1), (key2809, -1), (key2616, -1), (key2706, -1), (key2632, -1)]

def rawRow16489 : Integer.Sparse Key := [(key2898, -1), (key2977, -1), (key2654, -1), (key2944, -1), (key2642, -1), (key2796, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2898, -1), (key2977, -1), (key2654, -1), (key2944, -1), (key2642, -1), (key2796, -1), (key2738, 2), (key2951, 2), (key2649, 2), (key2939, 2), (key2619, 2), (key2674, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1), (key2860, 2), (key2640, 2), (key2794, 2), (key2706, -1), (key2809, -1), (key2632, -1), (key2786, -1), (key2616, -1), (key2671, -1)]

def rawRow16490 : Integer.Sparse Key := [(key2977, -1), (key2898, -1), (key2944, -1), (key2654, -1), (key2796, -1), (key2642, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2977, -1), (key2898, -1), (key2944, -1), (key2654, -1), (key2796, -1), (key2642, -1), (key2951, 2), (key2738, 2), (key2939, 2), (key2649, 2), (key2674, 2), (key2619, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1), (key2860, 2), (key2794, 2), (key2640, 2), (key2809, -1), (key2706, -1), (key2786, -1), (key2632, -1), (key2671, -1), (key2616, -1)]

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

def rawRow16527 : Integer.Sparse Key := [(key2407, 2), (key2441, 2), (key2441, 2), (key2410, -2), (key2410, -2), (key2445, -2), (key2848, 2), (key2970, 2), (key2970, 2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16528 : Integer.Sparse Key := [(key2441, 2), (key2407, 2), (key2441, 2), (key2410, -2), (key2445, -2), (key2410, -2), (key2970, 2), (key2848, 2), (key2970, 2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16529 : Integer.Sparse Key := [(key2441, 2), (key2441, 2), (key2407, 2), (key2445, -2), (key2410, -2), (key2410, -2), (key2970, 2), (key2970, 2), (key2848, 2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16530 : Integer.Sparse Key := [(key2410, 2), (key2441, 2), (key2445, 2), (key2407, -2), (key2410, -2), (key2441, -2), (key2882, 2), (key2991, 2), (key2993, 2), (key2592, -1), (key2595, -1), (key2848, -1), (key2882, -1), (key2970, -1), (key2991, -1), (key2912, -2), (key2914, -2), (key3003, -2), (key2602, -1), (key2603, -1), (key2891, -1), (key2914, -1), (key2996, -1), (key3003, -1), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16531 : Integer.Sparse Key := [(key2410, 2), (key2445, 2), (key2441, 2), (key2410, -2), (key2407, -2), (key2441, -2), (key2882, 2), (key2993, 2), (key2991, 2), (key2595, -1), (key2592, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2970, -1), (key2914, -2), (key2912, -2), (key3003, -2), (key2603, -1), (key2602, -1), (key2914, -1), (key2891, -1), (key3003, -1), (key2996, -1), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16532 : Integer.Sparse Key := [(key2441, 2), (key2410, 2), (key2445, 2), (key2407, -2), (key2441, -2), (key2410, -2), (key2991, 2), (key2882, 2), (key2993, 2), (key2848, -1), (key2970, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2912, -2), (key3003, -2), (key2914, -2), (key2891, -1), (key2996, -1), (key2602, -1), (key3003, -1), (key2603, -1), (key2914, -1), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16533 : Integer.Sparse Key := [(key2441, 2), (key2445, 2), (key2410, 2), (key2441, -2), (key2407, -2), (key2410, -2), (key2991, 2), (key2993, 2), (key2882, 2), (key2970, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2882, -1), (key2595, -1), (key3003, -2), (key2912, -2), (key2914, -2), (key2996, -1), (key2891, -1), (key3003, -1), (key2602, -1), (key2914, -1), (key2603, -1), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16534 : Integer.Sparse Key := [(key2445, 2), (key2410, 2), (key2441, 2), (key2410, -2), (key2441, -2), (key2407, -2), (key2993, 2), (key2882, 2), (key2991, 2), (key2882, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2592, -1), (key2848, -1), (key2914, -2), (key3003, -2), (key2912, -2), (key2914, -1), (key3003, -1), (key2603, -1), (key2996, -1), (key2602, -1), (key2891, -1), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16535 : Integer.Sparse Key := [(key2445, 2), (key2441, 2), (key2410, 2), (key2441, -2), (key2410, -2), (key2407, -2), (key2993, 2), (key2991, 2), (key2882, 2), (key2991, -1), (key2882, -1), (key2970, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key3003, -2), (key2914, -2), (key2912, -2), (key3003, -1), (key2914, -1), (key2996, -1), (key2603, -1), (key2891, -1), (key2602, -1), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16536 : Integer.Sparse Key := [(key2473, 2), (key2507, 2), (key2507, 2), (key2483, -2), (key2483, -2), (key2526, -2), (key2407, 2), (key2441, 2), (key2441, 2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2603, 4), (key2914, 4), (key2914, 4)]

def rawRow16537 : Integer.Sparse Key := [(key2507, 2), (key2473, 2), (key2507, 2), (key2483, -2), (key2526, -2), (key2483, -2), (key2441, 2), (key2407, 2), (key2441, 2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2914, 4), (key2603, 4), (key2914, 4)]

def rawRow16538 : Integer.Sparse Key := [(key2507, 2), (key2507, 2), (key2473, 2), (key2526, -2), (key2483, -2), (key2483, -2), (key2441, 2), (key2441, 2), (key2407, 2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2914, 4), (key2914, 4), (key2603, 4)]

def rawRow16539 : Integer.Sparse Key := [(key2483, 2), (key2507, 2), (key2526, 2), (key2473, -2), (key2483, -2), (key2507, -2), (key2544, 2), (key2555, 2), (key2565, 2), (key2379, -1), (key2393, -1), (key2771, -1), (key2912, -1), (key2933, -1), (key2991, -1), (key2882, -2), (key2914, -2), (key2993, -2), (key2595, -1), (key2603, -1), (key2774, -1), (key2914, -1), (key2934, -1), (key2993, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16540 : Integer.Sparse Key := [(key2483, 2), (key2526, 2), (key2507, 2), (key2483, -2), (key2473, -2), (key2507, -2), (key2544, 2), (key2565, 2), (key2555, 2), (key2393, -1), (key2379, -1), (key2912, -1), (key2771, -1), (key2991, -1), (key2933, -1), (key2914, -2), (key2882, -2), (key2993, -2), (key2603, -1), (key2595, -1), (key2914, -1), (key2774, -1), (key2993, -1), (key2934, -1), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16541 : Integer.Sparse Key := [(key2507, 2), (key2483, 2), (key2526, 2), (key2473, -2), (key2507, -2), (key2483, -2), (key2555, 2), (key2544, 2), (key2565, 2), (key2407, -1), (key2441, -1), (key2592, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2882, -2), (key2993, -2), (key2914, -2), (key2774, -1), (key2934, -1), (key2595, -1), (key2993, -1), (key2603, -1), (key2914, -1), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16542 : Integer.Sparse Key := [(key2507, 2), (key2526, 2), (key2483, 2), (key2507, -2), (key2473, -2), (key2483, -2), (key2555, 2), (key2565, 2), (key2544, 2), (key2441, -1), (key2407, -1), (key2991, -1), (key2592, -1), (key2912, -1), (key2602, -1), (key2993, -2), (key2882, -2), (key2914, -2), (key2934, -1), (key2774, -1), (key2993, -1), (key2595, -1), (key2914, -1), (key2603, -1), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16543 : Integer.Sparse Key := [(key2526, 2), (key2483, 2), (key2507, 2), (key2483, -2), (key2507, -2), (key2473, -2), (key2565, 2), (key2544, 2), (key2555, 2), (key2544, -1), (key2555, -1), (key2393, -1), (key2441, -1), (key2379, -1), (key2771, -1), (key2914, -2), (key2993, -2), (key2882, -2), (key2914, -1), (key2993, -1), (key2603, -1), (key2934, -1), (key2595, -1), (key2774, -1), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16544 : Integer.Sparse Key := [(key2526, 2), (key2507, 2), (key2483, 2), (key2507, -2), (key2483, -2), (key2473, -2), (key2565, 2), (key2555, 2), (key2544, 2), (key2555, -1), (key2544, -1), (key2441, -1), (key2393, -1), (key2407, -1), (key2592, -1), (key2993, -2), (key2914, -2), (key2882, -2), (key2993, -1), (key2914, -1), (key2934, -1), (key2603, -1), (key2774, -1), (key2595, -1), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16545 : Integer.Sparse Key := [(key2539, 2), (key2555, 2), (key2557, 2), (key2544, -2), (key2545, -2), (key2565, -2), (key2410, 2), (key2441, 2), (key2445, 2), (key2393, -1), (key2395, -1), (key2483, -1), (key2545, -1), (key2526, -1), (key2565, -1), (key2407, -2), (key2410, -2), (key2441, -2), (key2592, -1), (key2595, -1), (key2848, -1), (key2882, -1), (key2970, -1), (key2991, -1), (key2602, 4), (key2891, 4), (key2912, 4)]

def rawRow16546 : Integer.Sparse Key := [(key2539, 2), (key2557, 2), (key2555, 2), (key2545, -2), (key2544, -2), (key2565, -2), (key2410, 2), (key2445, 2), (key2441, 2), (key2395, -1), (key2393, -1), (key2545, -1), (key2483, -1), (key2565, -1), (key2526, -1), (key2410, -2), (key2407, -2), (key2441, -2), (key2595, -1), (key2592, -1), (key2882, -1), (key2848, -1), (key2991, -1), (key2970, -1), (key2602, 4), (key2912, 4), (key2891, 4)]

def rawRow16547 : Integer.Sparse Key := [(key2555, 2), (key2539, 2), (key2557, 2), (key2544, -2), (key2565, -2), (key2545, -2), (key2441, 2), (key2410, 2), (key2445, 2), (key2483, -1), (key2526, -1), (key2393, -1), (key2565, -1), (key2395, -1), (key2545, -1), (key2407, -2), (key2441, -2), (key2410, -2), (key2848, -1), (key2970, -1), (key2592, -1), (key2991, -1), (key2595, -1), (key2882, -1), (key2891, 4), (key2602, 4), (key2912, 4)]

def rawRow16548 : Integer.Sparse Key := [(key2555, 2), (key2557, 2), (key2539, 2), (key2565, -2), (key2544, -2), (key2545, -2), (key2441, 2), (key2445, 2), (key2410, 2), (key2526, -1), (key2483, -1), (key2565, -1), (key2393, -1), (key2545, -1), (key2395, -1), (key2441, -2), (key2407, -2), (key2410, -2), (key2970, -1), (key2848, -1), (key2991, -1), (key2592, -1), (key2882, -1), (key2595, -1), (key2891, 4), (key2912, 4), (key2602, 4)]

def rawRow16549 : Integer.Sparse Key := [(key2557, 2), (key2539, 2), (key2555, 2), (key2545, -2), (key2565, -2), (key2544, -2), (key2445, 2), (key2410, 2), (key2441, 2), (key2545, -1), (key2565, -1), (key2395, -1), (key2526, -1), (key2393, -1), (key2483, -1), (key2410, -2), (key2441, -2), (key2407, -2), (key2882, -1), (key2991, -1), (key2595, -1), (key2970, -1), (key2592, -1), (key2848, -1), (key2912, 4), (key2602, 4), (key2891, 4)]

def rawRow16550 : Integer.Sparse Key := [(key2557, 2), (key2555, 2), (key2539, 2), (key2565, -2), (key2545, -2), (key2544, -2), (key2445, 2), (key2441, 2), (key2410, 2), (key2565, -1), (key2545, -1), (key2526, -1), (key2395, -1), (key2483, -1), (key2393, -1), (key2441, -2), (key2410, -2), (key2407, -2), (key2991, -1), (key2882, -1), (key2970, -1), (key2595, -1), (key2848, -1), (key2592, -1), (key2912, 4), (key2891, 4), (key2602, 4)]

def rawRow16551 : Integer.Sparse Key := [(key2544, 2), (key2555, 2), (key2565, 2), (key2539, -2), (key2545, -2), (key2557, -2), (key2483, 2), (key2507, 2), (key2526, 2), (key2382, -1), (key2395, -1), (key2410, -1), (key2545, -1), (key2445, -1), (key2557, -1), (key2473, -2), (key2483, -2), (key2507, -2), (key2379, -1), (key2393, -1), (key2771, -1), (key2912, -1), (key2933, -1), (key2991, -1), (key2595, 4), (key2774, 4), (key2882, 4)]

def rawRow16552 : Integer.Sparse Key := [(key2544, 2), (key2565, 2), (key2555, 2), (key2545, -2), (key2539, -2), (key2557, -2), (key2483, 2), (key2526, 2), (key2507, 2), (key2395, -1), (key2382, -1), (key2545, -1), (key2410, -1), (key2557, -1), (key2445, -1), (key2483, -2), (key2473, -2), (key2507, -2), (key2393, -1), (key2379, -1), (key2912, -1), (key2771, -1), (key2991, -1), (key2933, -1), (key2595, 4), (key2882, 4), (key2774, 4)]

def rawRow16553 : Integer.Sparse Key := [(key2555, 2), (key2544, 2), (key2565, 2), (key2539, -2), (key2557, -2), (key2545, -2), (key2507, 2), (key2483, 2), (key2526, 2), (key2410, -1), (key2445, -1), (key2382, -1), (key2557, -1), (key2395, -1), (key2545, -1), (key2473, -2), (key2507, -2), (key2483, -2), (key2407, -1), (key2441, -1), (key2592, -1), (key2991, -1), (key2602, -1), (key2912, -1), (key2774, 4), (key2595, 4), (key2882, 4)]

def rawRow16554 : Integer.Sparse Key := [(key2555, 2), (key2565, 2), (key2544, 2), (key2557, -2), (key2539, -2), (key2545, -2), (key2507, 2), (key2526, 2), (key2483, 2), (key2445, -1), (key2410, -1), (key2557, -1), (key2382, -1), (key2545, -1), (key2395, -1), (key2507, -2), (key2473, -2), (key2483, -2), (key2441, -1), (key2407, -1), (key2991, -1), (key2592, -1), (key2912, -1), (key2602, -1), (key2774, 4), (key2882, 4), (key2595, 4)]

def rawRow16555 : Integer.Sparse Key := [(key2565, 2), (key2544, 2), (key2555, 2), (key2545, -2), (key2557, -2), (key2539, -2), (key2526, 2), (key2483, 2), (key2507, 2), (key2545, -1), (key2557, -1), (key2395, -1), (key2445, -1), (key2382, -1), (key2410, -1), (key2483, -2), (key2507, -2), (key2473, -2), (key2544, -1), (key2555, -1), (key2393, -1), (key2441, -1), (key2379, -1), (key2771, -1), (key2882, 4), (key2595, 4), (key2774, 4)]

def rawRow16556 : Integer.Sparse Key := [(key2565, 2), (key2555, 2), (key2544, 2), (key2557, -2), (key2545, -2), (key2539, -2), (key2526, 2), (key2507, 2), (key2483, 2), (key2557, -1), (key2545, -1), (key2445, -1), (key2395, -1), (key2410, -1), (key2382, -1), (key2507, -2), (key2483, -2), (key2473, -2), (key2555, -1), (key2544, -1), (key2441, -1), (key2393, -1), (key2407, -1), (key2592, -1), (key2882, 4), (key2774, 4), (key2595, 4)]

def rawRow16557 : Integer.Sparse Key := [(key2545, 2), (key2557, 2), (key2565, 2), (key2539, -2), (key2544, -2), (key2555, -2), (key2545, 2), (key2557, 2), (key2565, 2), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, -1), (key2507, -1), (key2539, -2), (key2544, -2), (key2555, -2), (key2382, -1), (key2393, -1), (key2410, -1), (key2483, -1), (key2441, -1), (key2507, -1), (key2379, 4), (key2771, 4), (key2848, 4)]

def rawRow16558 : Integer.Sparse Key := [(key2545, 2), (key2565, 2), (key2557, 2), (key2544, -2), (key2539, -2), (key2555, -2), (key2545, 2), (key2565, 2), (key2557, 2), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, -1), (key2441, -1), (key2544, -2), (key2539, -2), (key2555, -2), (key2393, -1), (key2382, -1), (key2483, -1), (key2410, -1), (key2507, -1), (key2441, -1), (key2379, 4), (key2848, 4), (key2771, 4)]

def rawRow16559 : Integer.Sparse Key := [(key2557, 2), (key2545, 2), (key2565, 2), (key2539, -2), (key2555, -2), (key2544, -2), (key2557, 2), (key2545, 2), (key2565, 2), (key2410, -1), (key2441, -1), (key2382, -1), (key2507, -1), (key2393, -1), (key2483, -1), (key2539, -2), (key2555, -2), (key2544, -2), (key2410, -1), (key2441, -1), (key2382, -1), (key2507, -1), (key2393, -1), (key2483, -1), (key2407, 4), (key2592, 4), (key2848, 4)]

def rawRow16560 : Integer.Sparse Key := [(key2557, 2), (key2565, 2), (key2545, 2), (key2555, -2), (key2539, -2), (key2544, -2), (key2557, 2), (key2565, 2), (key2545, 2), (key2441, -1), (key2410, -1), (key2507, -1), (key2382, -1), (key2483, -1), (key2393, -1), (key2555, -2), (key2539, -2), (key2544, -2), (key2441, -1), (key2410, -1), (key2507, -1), (key2382, -1), (key2483, -1), (key2393, -1), (key2407, 4), (key2848, 4), (key2592, 4)]

def rawRow16561 : Integer.Sparse Key := [(key2565, 2), (key2545, 2), (key2557, 2), (key2544, -2), (key2555, -2), (key2539, -2), (key2565, 2), (key2545, 2), (key2557, 2), (key2483, -1), (key2507, -1), (key2393, -1), (key2441, -1), (key2382, -1), (key2410, -1), (key2544, -2), (key2555, -2), (key2539, -2), (key2483, -1), (key2507, -1), (key2393, -1), (key2441, -1), (key2382, -1), (key2410, -1), (key2473, 4), (key2379, 4), (key2771, 4)]

def rawRow16562 : Integer.Sparse Key := [(key2565, 2), (key2557, 2), (key2545, 2), (key2555, -2), (key2544, -2), (key2539, -2), (key2565, 2), (key2557, 2), (key2545, 2), (key2507, -1), (key2483, -1), (key2441, -1), (key2393, -1), (key2410, -1), (key2382, -1), (key2555, -2), (key2544, -2), (key2539, -2), (key2507, -1), (key2483, -1), (key2441, -1), (key2393, -1), (key2410, -1), (key2382, -1), (key2473, 4), (key2407, 4), (key2592, 4)]

def rawRow16563 : Integer.Sparse Key := [(key2702, 2), (key2702, 2), (key2728, 2), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key3026, -1), (key3026, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2)]

def rawRow16564 : Integer.Sparse Key := [(key2702, 2), (key2728, 2), (key2702, 2), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2)]

def rawRow16565 : Integer.Sparse Key := [(key2728, 2), (key2702, 2), (key2702, 2), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, -1), (key2870, -1), (key3026, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2)]

def rawRow16566 : Integer.Sparse Key := [(key2735, 2), (key2737, 2), (key2747, 2), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2948, 2), (key2950, 2), (key2960, 2), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2726, -1), (key2732, -1), (key2870, -1), (key2885, -1), (key3026, -1), (key3030, -1), (key2640, -1), (key2644, -1), (key2860, -1), (key2885, -1), (key3023, -1), (key3030, -1), (key2632, 2), (key2644, 2), (key2706, 2), (key2732, 2), (key3023, 2), (key3026, 2)]

def rawRow16567 : Integer.Sparse Key := [(key2737, 2), (key2735, 2), (key2747, 2), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2950, 2), (key2948, 2), (key2960, 2), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2732, -1), (key2726, -1), (key2885, -1), (key2870, -1), (key3030, -1), (key3026, -1), (key2644, -1), (key2640, -1), (key2885, -1), (key2860, -1), (key3030, -1), (key3023, -1), (key2644, 2), (key2632, 2), (key2732, 2), (key2706, 2), (key3026, 2), (key3023, 2)]

def rawRow16568 : Integer.Sparse Key := [(key2735, 2), (key2747, 2), (key2737, 2), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2948, 2), (key2960, 2), (key2950, 2), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2870, -1), (key3026, -1), (key2726, -1), (key3030, -1), (key2732, -1), (key2885, -1), (key2860, -1), (key3023, -1), (key2640, -1), (key3030, -1), (key2644, -1), (key2885, -1), (key2706, 2), (key3023, 2), (key2632, 2), (key3026, 2), (key2644, 2), (key2732, 2)]

def rawRow16569 : Integer.Sparse Key := [(key2747, 2), (key2735, 2), (key2737, 2), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2960, 2), (key2948, 2), (key2950, 2), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key3026, -1), (key2870, -1), (key3030, -1), (key2726, -1), (key2885, -1), (key2732, -1), (key3023, -1), (key2860, -1), (key3030, -1), (key2640, -1), (key2885, -1), (key2644, -1), (key3023, 2), (key2706, 2), (key3026, 2), (key2632, 2), (key2732, 2), (key2644, 2)]

def rawRow16570 : Integer.Sparse Key := [(key2737, 2), (key2747, 2), (key2735, 2), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, 2), (key2960, 2), (key2948, 2), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2885, -1), (key3030, -1), (key2732, -1), (key3026, -1), (key2726, -1), (key2870, -1), (key2885, -1), (key3030, -1), (key2644, -1), (key3023, -1), (key2640, -1), (key2860, -1), (key2732, 2), (key3026, 2), (key2644, 2), (key3023, 2), (key2632, 2), (key2706, 2)]

def rawRow16571 : Integer.Sparse Key := [(key2747, 2), (key2737, 2), (key2735, 2), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, 2), (key2950, 2), (key2948, 2), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key3030, -1), (key2885, -1), (key3026, -1), (key2732, -1), (key2870, -1), (key2726, -1), (key3030, -1), (key2885, -1), (key3023, -1), (key2644, -1), (key2860, -1), (key2640, -1), (key3026, 2), (key2732, 2), (key3023, 2), (key2644, 2), (key2706, 2), (key2632, 2)]

def rawRow16572 : Integer.Sparse Key := [(key2805, 2), (key2805, 2), (key2831, 2), (key2782, -1), (key2782, -1), (key2893, -1), (key2893, -1), (key2904, -1), (key2904, -1), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2640, 2), (key2640, 2), (key2726, 2), (key2726, 2), (key3030, 2), (key3030, 2)]

def rawRow16573 : Integer.Sparse Key := [(key2805, 2), (key2831, 2), (key2805, 2), (key2893, -1), (key2904, -1), (key2782, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2726, 2), (key3030, 2), (key2640, 2), (key3030, 2), (key2640, 2), (key2726, 2)]

def rawRow16574 : Integer.Sparse Key := [(key2831, 2), (key2805, 2), (key2805, 2), (key2904, -1), (key2893, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2782, -1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3030, 2), (key2726, 2), (key3030, 2), (key2640, 2), (key2726, 2), (key2640, 2)]

def rawRow16575 : Integer.Sparse Key := [(key2893, 2), (key2897, 2), (key2904, 2), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2972, 2), (key2976, 2), (key2983, 2), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2)]

def rawRow16576 : Integer.Sparse Key := [(key2897, 2), (key2893, 2), (key2904, 2), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2976, 2), (key2972, 2), (key2983, 2), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2)]

def rawRow16577 : Integer.Sparse Key := [(key2893, 2), (key2904, 2), (key2897, 2), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2972, 2), (key2983, 2), (key2976, 2), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2)]

def rawRow16578 : Integer.Sparse Key := [(key2904, 2), (key2893, 2), (key2897, 2), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2983, 2), (key2972, 2), (key2976, 2), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2)]

def rawRow16579 : Integer.Sparse Key := [(key2897, 2), (key2904, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 2), (key2983, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2)]

def rawRow16580 : Integer.Sparse Key := [(key2904, 2), (key2897, 2), (key2893, 2), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 2), (key2976, 2), (key2972, 2), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2)]

def rawRow16581 : Integer.Sparse Key := [(key2948, 2), (key2950, 2), (key2960, 2), (key2936, -1), (key2938, -1), (key2972, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2735, 2), (key2737, 2), (key2747, 2), (key2646, -1), (key2648, -1), (key2893, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2612, -1), (key2618, -1), (key2805, -1), (key2950, -1), (key2831, -1), (key2960, -1), (key2628, 2), (key2648, 2), (key2782, 2), (key2938, 2), (key2904, 2), (key2983, 2)]

def rawRow16582 : Integer.Sparse Key := [(key2950, 2), (key2948, 2), (key2960, 2), (key2938, -1), (key2936, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2983, -1), (key2737, 2), (key2735, 2), (key2747, 2), (key2648, -1), (key2646, -1), (key2997, -1), (key2893, -1), (key3000, -1), (key2904, -1), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2618, -1), (key2612, -1), (key2950, -1), (key2805, -1), (key2960, -1), (key2831, -1), (key2648, 2), (key2628, 2), (key2938, 2), (key2782, 2), (key2983, 2), (key2904, 2)]

def rawRow16583 : Integer.Sparse Key := [(key2948, 2), (key2960, 2), (key2950, 2), (key2972, -1), (key2983, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2735, 2), (key2747, 2), (key2737, 2), (key2893, -1), (key2904, -1), (key2646, -1), (key3000, -1), (key2648, -1), (key2997, -1), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2805, -1), (key2831, -1), (key2612, -1), (key2960, -1), (key2618, -1), (key2950, -1), (key2782, 2), (key2904, 2), (key2628, 2), (key2983, 2), (key2648, 2), (key2938, 2)]

def rawRow16584 : Integer.Sparse Key := [(key2960, 2), (key2948, 2), (key2950, 2), (key2983, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2997, -1), (key2938, -1), (key2747, 2), (key2735, 2), (key2737, 2), (key2904, -1), (key2893, -1), (key3000, -1), (key2646, -1), (key2997, -1), (key2648, -1), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2831, -1), (key2805, -1), (key2960, -1), (key2612, -1), (key2950, -1), (key2618, -1), (key2904, 2), (key2782, 2), (key2983, 2), (key2628, 2), (key2938, 2), (key2648, 2)]

def rawRow16585 : Integer.Sparse Key := [(key2950, 2), (key2960, 2), (key2948, 2), (key2997, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2936, -1), (key2972, -1), (key2737, 2), (key2747, 2), (key2735, 2), (key2997, -1), (key3000, -1), (key2648, -1), (key2904, -1), (key2646, -1), (key2893, -1), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, -1), (key2960, -1), (key2618, -1), (key2831, -1), (key2612, -1), (key2805, -1), (key2938, 2), (key2983, 2), (key2648, 2), (key2904, 2), (key2628, 2), (key2782, 2)]

def rawRow16586 : Integer.Sparse Key := [(key2960, 2), (key2950, 2), (key2948, 2), (key3000, -1), (key2997, -1), (key2983, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key2747, 2), (key2737, 2), (key2735, 2), (key3000, -1), (key2997, -1), (key2904, -1), (key2648, -1), (key2893, -1), (key2646, -1), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, -1), (key2950, -1), (key2831, -1), (key2618, -1), (key2805, -1), (key2612, -1), (key2983, 2), (key2938, 2), (key2904, 2), (key2648, 2), (key2782, 2), (key2628, 2)]

def rawRow16587 : Integer.Sparse Key := [(key2972, 2), (key2976, 2), (key2983, 2), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2893, 2), (key2897, 2), (key2904, 2), (key2646, -1), (key2653, -1), (key2735, -1), (key2998, -1), (key2747, -1), (key3000, -1), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, -1), (key2641, -1), (key2702, -1), (key2976, -1), (key2728, -1), (key2983, -1), (key2612, 2), (key2653, 2), (key2667, 2), (key2943, 2), (key2747, 2), (key2960, 2)]

def rawRow16588 : Integer.Sparse Key := [(key2976, 2), (key2972, 2), (key2983, 2), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2897, 2), (key2893, 2), (key2904, 2), (key2653, -1), (key2646, -1), (key2998, -1), (key2735, -1), (key3000, -1), (key2747, -1), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, -1), (key2628, -1), (key2976, -1), (key2702, -1), (key2983, -1), (key2728, -1), (key2653, 2), (key2612, 2), (key2943, 2), (key2667, 2), (key2960, 2), (key2747, 2)]

def rawRow16589 : Integer.Sparse Key := [(key2972, 2), (key2983, 2), (key2976, 2), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2893, 2), (key2904, 2), (key2897, 2), (key2735, -1), (key2747, -1), (key2646, -1), (key3000, -1), (key2653, -1), (key2998, -1), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, -1), (key2728, -1), (key2628, -1), (key2983, -1), (key2641, -1), (key2976, -1), (key2667, 2), (key2747, 2), (key2612, 2), (key2960, 2), (key2653, 2), (key2943, 2)]

def rawRow16590 : Integer.Sparse Key := [(key2983, 2), (key2972, 2), (key2976, 2), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2904, 2), (key2893, 2), (key2897, 2), (key2747, -1), (key2735, -1), (key3000, -1), (key2646, -1), (key2998, -1), (key2653, -1), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, -1), (key2702, -1), (key2983, -1), (key2628, -1), (key2976, -1), (key2641, -1), (key2747, 2), (key2667, 2), (key2960, 2), (key2612, 2), (key2943, 2), (key2653, 2)]

def rawRow16591 : Integer.Sparse Key := [(key2976, 2), (key2983, 2), (key2972, 2), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2897, 2), (key2904, 2), (key2893, 2), (key2998, -1), (key3000, -1), (key2653, -1), (key2747, -1), (key2646, -1), (key2735, -1), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, -1), (key2983, -1), (key2641, -1), (key2728, -1), (key2628, -1), (key2702, -1), (key2943, 2), (key2960, 2), (key2653, 2), (key2747, 2), (key2612, 2), (key2667, 2)]

def rawRow16592 : Integer.Sparse Key := [(key2983, 2), (key2976, 2), (key2972, 2), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2904, 2), (key2897, 2), (key2893, 2), (key3000, -1), (key2998, -1), (key2747, -1), (key2653, -1), (key2735, -1), (key2646, -1), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, -1), (key2976, -1), (key2728, -1), (key2641, -1), (key2702, -1), (key2628, -1), (key2960, 2), (key2943, 2), (key2747, 2), (key2653, 2), (key2667, 2), (key2612, 2)]

def rawRow16593 : Integer.Sparse Key := [(key2997, 2), (key2998, 2), (key3000, 2), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2997, 2), (key2998, 2), (key3000, 2), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2648, -1), (key2653, -1), (key2737, -1), (key2897, -1), (key2747, -1), (key2904, -1), (key2618, 2), (key2641, 2), (key2673, 2), (key2795, 2), (key2728, 2), (key2831, 2)]

def rawRow16594 : Integer.Sparse Key := [(key2998, 2), (key2997, 2), (key3000, 2), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2998, 2), (key2997, 2), (key3000, 2), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2653, -1), (key2648, -1), (key2897, -1), (key2737, -1), (key2904, -1), (key2747, -1), (key2641, 2), (key2618, 2), (key2795, 2), (key2673, 2), (key2831, 2), (key2728, 2)]

def rawRow16595 : Integer.Sparse Key := [(key2997, 2), (key3000, 2), (key2998, 2), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2997, 2), (key3000, 2), (key2998, 2), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2737, -1), (key2747, -1), (key2648, -1), (key2904, -1), (key2653, -1), (key2897, -1), (key2673, 2), (key2728, 2), (key2618, 2), (key2831, 2), (key2641, 2), (key2795, 2)]

def rawRow16596 : Integer.Sparse Key := [(key3000, 2), (key2997, 2), (key2998, 2), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key3000, 2), (key2997, 2), (key2998, 2), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2747, -1), (key2737, -1), (key2904, -1), (key2648, -1), (key2897, -1), (key2653, -1), (key2728, 2), (key2673, 2), (key2831, 2), (key2618, 2), (key2795, 2), (key2641, 2)]

def rawRow16597 : Integer.Sparse Key := [(key2998, 2), (key3000, 2), (key2997, 2), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2998, 2), (key3000, 2), (key2997, 2), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2897, -1), (key2904, -1), (key2653, -1), (key2747, -1), (key2648, -1), (key2737, -1), (key2795, 2), (key2831, 2), (key2641, 2), (key2728, 2), (key2618, 2), (key2673, 2)]

def rawRow16598 : Integer.Sparse Key := [(key3000, 2), (key2998, 2), (key2997, 2), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key3000, 2), (key2998, 2), (key2997, 2), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2904, -1), (key2897, -1), (key2747, -1), (key2653, -1), (key2737, -1), (key2648, -1), (key2831, 2), (key2795, 2), (key2728, 2), (key2641, 2), (key2673, 2), (key2618, 2)]

def rawRow16599 : Integer.Sparse Key := [(key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2673, 2), (key2737, 2), (key2737, 2), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2621, -2), (key2835, -2), (key2835, -2), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2753, 2), (key2920, 2), (key2920, 2), (key2658, -2), (key2923, -2), (key2923, -2)]

def rawRow16600 : Integer.Sparse Key := [(key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2737, 2), (key2673, 2), (key2737, 2), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2835, -2), (key2621, -2), (key2835, -2), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2920, 2), (key2753, 2), (key2920, 2), (key2923, -2), (key2658, -2), (key2923, -2)]

def rawRow16601 : Integer.Sparse Key := [(key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2737, 2), (key2737, 2), (key2673, 2), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2835, -2), (key2835, -2), (key2621, -2), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2920, 2), (key2920, 2), (key2753, 2), (key2923, -2), (key2923, -2), (key2658, -2)]

def rawRow16602 : Integer.Sparse Key := [(key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2667, 2), (key2702, 2), (key2735, 2), (key2612, 1), (key2618, 1), (key2805, 1), (key2950, 1), (key2831, 1), (key2960, 1), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, -1), (key2732, -1), (key2870, -1), (key2885, -1), (key3026, -1), (key3030, -1), (key2640, 1), (key2644, 1), (key2860, 1), (key2885, 1), (key3023, 1), (key3030, 1), (key2758, 2), (key2923, 2), (key2927, 2), (key2660, -2), (key2920, -2), (key2927, -2)]

def rawRow16603 : Integer.Sparse Key := [(key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2667, 2), (key2735, 2), (key2702, 2), (key2618, 1), (key2612, 1), (key2950, 1), (key2805, 1), (key2960, 1), (key2831, 1), (key2616, -2), (key2829, -2), (key2809, -2), (key2732, -1), (key2726, -1), (key2885, -1), (key2870, -1), (key3030, -1), (key3026, -1), (key2644, 1), (key2640, 1), (key2885, 1), (key2860, 1), (key3030, 1), (key3023, 1), (key2758, 2), (key2927, 2), (key2923, 2), (key2660, -2), (key2927, -2), (key2920, -2)]

def rawRow16604 : Integer.Sparse Key := [(key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2702, 2), (key2667, 2), (key2735, 2), (key2805, 1), (key2831, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, -1), (key3026, -1), (key2726, -1), (key3030, -1), (key2732, -1), (key2885, -1), (key2860, 1), (key3023, 1), (key2640, 1), (key3030, 1), (key2644, 1), (key2885, 1), (key2923, 2), (key2758, 2), (key2927, 2), (key2920, -2), (key2660, -2), (key2927, -2)]

def rawRow16605 : Integer.Sparse Key := [(key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2702, 2), (key2735, 2), (key2667, 2), (key2831, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2950, 1), (key2618, 1), (key2809, -2), (key2829, -2), (key2616, -2), (key3026, -1), (key2870, -1), (key3030, -1), (key2726, -1), (key2885, -1), (key2732, -1), (key3023, 1), (key2860, 1), (key3030, 1), (key2640, 1), (key2885, 1), (key2644, 1), (key2923, 2), (key2927, 2), (key2758, 2), (key2920, -2), (key2927, -2), (key2660, -2)]

def rawRow16606 : Integer.Sparse Key := [(key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2735, 2), (key2667, 2), (key2702, 2), (key2950, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2612, 1), (key2805, 1), (key2829, -2), (key2616, -2), (key2809, -2), (key2885, -1), (key3030, -1), (key2732, -1), (key3026, -1), (key2726, -1), (key2870, -1), (key2885, 1), (key3030, 1), (key2644, 1), (key3023, 1), (key2640, 1), (key2860, 1), (key2927, 2), (key2758, 2), (key2923, 2), (key2927, -2), (key2660, -2), (key2920, -2)]

def rawRow16607 : Integer.Sparse Key := [(key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2735, 2), (key2702, 2), (key2667, 2), (key2960, 1), (key2950, 1), (key2831, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2829, -2), (key2809, -2), (key2616, -2), (key3030, -1), (key2885, -1), (key3026, -1), (key2732, -1), (key2870, -1), (key2726, -1), (key3030, 1), (key2885, 1), (key3023, 1), (key2644, 1), (key2860, 1), (key2640, 1), (key2927, 2), (key2923, 2), (key2758, 2), (key2927, -2), (key2920, -2), (key2660, -2)]

def rawRow16608 : Integer.Sparse Key := [(key2782, -1), (key2782, -1), (key2893, -1), (key2893, -1), (key2904, -1), (key2904, -1), (key2795, 2), (key2897, 2), (key2897, 2), (key2628, 1), (key2628, 1), (key2972, 1), (key2972, 1), (key2983, 1), (key2983, 1), (key2641, -2), (key2976, -2), (key2976, -2), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2676, 2), (key2798, 2), (key2798, 2), (key2621, -2), (key2835, -2), (key2835, -2)]

def rawRow16609 : Integer.Sparse Key := [(key2893, -1), (key2904, -1), (key2782, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2897, 2), (key2795, 2), (key2897, 2), (key2972, 1), (key2983, 1), (key2628, 1), (key2983, 1), (key2628, 1), (key2972, 1), (key2976, -2), (key2641, -2), (key2976, -2), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2798, 2), (key2676, 2), (key2798, 2), (key2835, -2), (key2621, -2), (key2835, -2)]

def rawRow16610 : Integer.Sparse Key := [(key2904, -1), (key2893, -1), (key2904, -1), (key2782, -1), (key2893, -1), (key2782, -1), (key2897, 2), (key2897, 2), (key2795, 2), (key2983, 1), (key2972, 1), (key2983, 1), (key2628, 1), (key2972, 1), (key2628, 1), (key2976, -2), (key2976, -2), (key2641, -2), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2798, 2), (key2798, 2), (key2676, 2), (key2835, -2), (key2835, -2), (key2621, -2)]

def rawRow16611 : Integer.Sparse Key := [(key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2782, 2), (key2805, 2), (key2893, 2), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1), (key2628, -2), (key2702, -2), (key2972, -2), (key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2732, 2), (key2835, 2), (key2885, 2), (key2644, -2), (key2798, -2), (key2885, -2)]

def rawRow16612 : Integer.Sparse Key := [(key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2782, 2), (key2893, 2), (key2805, 2), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1), (key2628, -2), (key2972, -2), (key2702, -2), (key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2732, 2), (key2885, 2), (key2835, 2), (key2644, -2), (key2885, -2), (key2798, -2)]

def rawRow16613 : Integer.Sparse Key := [(key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2805, 2), (key2782, 2), (key2893, 2), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2702, -2), (key2628, -2), (key2972, -2), (key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2835, 2), (key2732, 2), (key2885, 2), (key2798, -2), (key2644, -2), (key2885, -2)]

def rawRow16614 : Integer.Sparse Key := [(key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2805, 2), (key2893, 2), (key2782, 2), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1), (key2702, -2), (key2972, -2), (key2628, -2), (key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2835, 2), (key2885, 2), (key2732, 2), (key2798, -2), (key2885, -2), (key2644, -2)]

def rawRow16615 : Integer.Sparse Key := [(key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2893, 2), (key2782, 2), (key2805, 2), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1), (key2972, -2), (key2628, -2), (key2702, -2), (key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2885, 2), (key2732, 2), (key2835, 2), (key2885, -2), (key2644, -2), (key2798, -2)]

def rawRow16616 : Integer.Sparse Key := [(key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2893, 2), (key2805, 2), (key2782, 2), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1), (key2972, -2), (key2702, -2), (key2628, -2), (key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2885, 2), (key2835, 2), (key2732, 2), (key2885, -2), (key2798, -2), (key2644, -2)]

def rawRow16617 : Integer.Sparse Key := [(key2936, -1), (key2938, -1), (key2972, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2943, 2), (key2976, 2), (key2998, 2), (key2646, 1), (key2648, 1), (key2893, 1), (key2997, 1), (key2904, 1), (key3000, 1), (key2653, -2), (key2897, -2), (key2998, -2), (key2667, -1), (key2673, -1), (key2702, -1), (key2737, -1), (key2728, -1), (key2747, -1), (key2612, 1), (key2618, 1), (key2805, 1), (key2950, 1), (key2831, 1), (key2960, 1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, -2), (key2809, -2), (key2829, -2)]

def rawRow16618 : Integer.Sparse Key := [(key2938, -1), (key2936, -1), (key2997, -1), (key2972, -1), (key3000, -1), (key2983, -1), (key2943, 2), (key2998, 2), (key2976, 2), (key2648, 1), (key2646, 1), (key2997, 1), (key2893, 1), (key3000, 1), (key2904, 1), (key2653, -2), (key2998, -2), (key2897, -2), (key2673, -1), (key2667, -1), (key2737, -1), (key2702, -1), (key2747, -1), (key2728, -1), (key2618, 1), (key2612, 1), (key2950, 1), (key2805, 1), (key2960, 1), (key2831, 1), (key2671, 2), (key2794, 2), (key2786, 2), (key2616, -2), (key2829, -2), (key2809, -2)]

def rawRow16619 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2936, -1), (key3000, -1), (key2938, -1), (key2997, -1), (key2976, 2), (key2943, 2), (key2998, 2), (key2893, 1), (key2904, 1), (key2646, 1), (key3000, 1), (key2648, 1), (key2997, 1), (key2897, -2), (key2653, -2), (key2998, -2), (key2702, -1), (key2728, -1), (key2667, -1), (key2747, -1), (key2673, -1), (key2737, -1), (key2805, 1), (key2831, 1), (key2612, 1), (key2960, 1), (key2618, 1), (key2950, 1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, -2), (key2616, -2), (key2829, -2)]

def rawRow16620 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key3000, -1), (key2936, -1), (key2997, -1), (key2938, -1), (key2976, 2), (key2998, 2), (key2943, 2), (key2904, 1), (key2893, 1), (key3000, 1), (key2646, 1), (key2997, 1), (key2648, 1), (key2897, -2), (key2998, -2), (key2653, -2), (key2728, -1), (key2702, -1), (key2747, -1), (key2667, -1), (key2737, -1), (key2673, -1), (key2831, 1), (key2805, 1), (key2960, 1), (key2612, 1), (key2950, 1), (key2618, 1), (key2786, 2), (key2794, 2), (key2671, 2), (key2809, -2), (key2829, -2), (key2616, -2)]

def rawRow16621 : Integer.Sparse Key := [(key2997, -1), (key3000, -1), (key2938, -1), (key2983, -1), (key2936, -1), (key2972, -1), (key2998, 2), (key2943, 2), (key2976, 2), (key2997, 1), (key3000, 1), (key2648, 1), (key2904, 1), (key2646, 1), (key2893, 1), (key2998, -2), (key2653, -2), (key2897, -2), (key2737, -1), (key2747, -1), (key2673, -1), (key2728, -1), (key2667, -1), (key2702, -1), (key2950, 1), (key2960, 1), (key2618, 1), (key2831, 1), (key2612, 1), (key2805, 1), (key2794, 2), (key2671, 2), (key2786, 2), (key2829, -2), (key2616, -2), (key2809, -2)]

def rawRow16622 : Integer.Sparse Key := [(key3000, -1), (key2997, -1), (key2983, -1), (key2938, -1), (key2972, -1), (key2936, -1), (key2998, 2), (key2976, 2), (key2943, 2), (key3000, 1), (key2997, 1), (key2904, 1), (key2648, 1), (key2893, 1), (key2646, 1), (key2998, -2), (key2897, -2), (key2653, -2), (key2747, -1), (key2737, -1), (key2728, -1), (key2673, -1), (key2702, -1), (key2667, -1), (key2960, 1), (key2950, 1), (key2831, 1), (key2618, 1), (key2805, 1), (key2612, 1), (key2794, 2), (key2786, 2), (key2671, 2), (key2829, -2), (key2809, -2), (key2616, -2)]

def rawRow16623 : Integer.Sparse Key := [(key2936, -1), (key2943, -1), (key2948, -1), (key2998, -1), (key2960, -1), (key3000, -1), (key2938, 2), (key2950, 2), (key2997, 2), (key2646, 1), (key2653, 1), (key2735, 1), (key2998, 1), (key2747, 1), (key3000, 1), (key2648, -2), (key2737, -2), (key2997, -2), (key2782, -1), (key2795, -1), (key2805, -1), (key2897, -1), (key2831, -1), (key2904, -1), (key2628, 1), (key2641, 1), (key2702, 1), (key2976, 1), (key2728, 1), (key2983, 1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, -2), (key2786, -2), (key2870, -2)]

def rawRow16624 : Integer.Sparse Key := [(key2943, -1), (key2936, -1), (key2998, -1), (key2948, -1), (key3000, -1), (key2960, -1), (key2938, 2), (key2997, 2), (key2950, 2), (key2653, 1), (key2646, 1), (key2998, 1), (key2735, 1), (key3000, 1), (key2747, 1), (key2648, -2), (key2997, -2), (key2737, -2), (key2795, -1), (key2782, -1), (key2897, -1), (key2805, -1), (key2904, -1), (key2831, -1), (key2641, 1), (key2628, 1), (key2976, 1), (key2702, 1), (key2983, 1), (key2728, 1), (key2706, 2), (key2860, 2), (key2809, 2), (key2632, -2), (key2870, -2), (key2786, -2)]

def rawRow16625 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2936, -1), (key3000, -1), (key2943, -1), (key2998, -1), (key2950, 2), (key2938, 2), (key2997, 2), (key2735, 1), (key2747, 1), (key2646, 1), (key3000, 1), (key2653, 1), (key2998, 1), (key2737, -2), (key2648, -2), (key2997, -2), (key2805, -1), (key2831, -1), (key2782, -1), (key2904, -1), (key2795, -1), (key2897, -1), (key2702, 1), (key2728, 1), (key2628, 1), (key2983, 1), (key2641, 1), (key2976, 1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, -2), (key2632, -2), (key2870, -2)]

def rawRow16626 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key3000, -1), (key2936, -1), (key2998, -1), (key2943, -1), (key2950, 2), (key2997, 2), (key2938, 2), (key2747, 1), (key2735, 1), (key3000, 1), (key2646, 1), (key2998, 1), (key2653, 1), (key2737, -2), (key2997, -2), (key2648, -2), (key2831, -1), (key2805, -1), (key2904, -1), (key2782, -1), (key2897, -1), (key2795, -1), (key2728, 1), (key2702, 1), (key2983, 1), (key2628, 1), (key2976, 1), (key2641, 1), (key2809, 2), (key2860, 2), (key2706, 2), (key2786, -2), (key2870, -2), (key2632, -2)]

def rawRow16627 : Integer.Sparse Key := [(key2998, -1), (key3000, -1), (key2943, -1), (key2960, -1), (key2936, -1), (key2948, -1), (key2997, 2), (key2938, 2), (key2950, 2), (key2998, 1), (key3000, 1), (key2653, 1), (key2747, 1), (key2646, 1), (key2735, 1), (key2997, -2), (key2648, -2), (key2737, -2), (key2897, -1), (key2904, -1), (key2795, -1), (key2831, -1), (key2782, -1), (key2805, -1), (key2976, 1), (key2983, 1), (key2641, 1), (key2728, 1), (key2628, 1), (key2702, 1), (key2860, 2), (key2706, 2), (key2809, 2), (key2870, -2), (key2632, -2), (key2786, -2)]

def rawRow16628 : Integer.Sparse Key := [(key3000, -1), (key2998, -1), (key2960, -1), (key2943, -1), (key2948, -1), (key2936, -1), (key2997, 2), (key2950, 2), (key2938, 2), (key3000, 1), (key2998, 1), (key2747, 1), (key2653, 1), (key2735, 1), (key2646, 1), (key2997, -2), (key2737, -2), (key2648, -2), (key2904, -1), (key2897, -1), (key2831, -1), (key2795, -1), (key2805, -1), (key2782, -1), (key2983, 1), (key2976, 1), (key2728, 1), (key2641, 1), (key2702, 1), (key2628, 1), (key2860, 2), (key2809, 2), (key2706, 2), (key2870, -2), (key2786, -2), (key2632, -2)]

def rawRow16629 : Integer.Sparse Key := [(key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2936, 2), (key2948, 2), (key2972, 2), (key2648, 1), (key2653, 1), (key2737, 1), (key2897, 1), (key2747, 1), (key2904, 1), (key2646, -2), (key2735, -2), (key2893, -2), (key2938, -1), (key2943, -1), (key2950, -1), (key2976, -1), (key2960, -1), (key2983, -1), (key2648, 1), (key2653, 1), (key2737, 1), (key2897, 1), (key2747, 1), (key2904, 1), (key2726, 2), (key2829, 2), (key2870, 2), (key2640, -2), (key2794, -2), (key2860, -2)]

def rawRow16630 : Integer.Sparse Key := [(key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2936, 2), (key2972, 2), (key2948, 2), (key2653, 1), (key2648, 1), (key2897, 1), (key2737, 1), (key2904, 1), (key2747, 1), (key2646, -2), (key2893, -2), (key2735, -2), (key2943, -1), (key2938, -1), (key2976, -1), (key2950, -1), (key2983, -1), (key2960, -1), (key2653, 1), (key2648, 1), (key2897, 1), (key2737, 1), (key2904, 1), (key2747, 1), (key2726, 2), (key2870, 2), (key2829, 2), (key2640, -2), (key2860, -2), (key2794, -2)]

def rawRow16631 : Integer.Sparse Key := [(key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2948, 2), (key2936, 2), (key2972, 2), (key2737, 1), (key2747, 1), (key2648, 1), (key2904, 1), (key2653, 1), (key2897, 1), (key2735, -2), (key2646, -2), (key2893, -2), (key2950, -1), (key2960, -1), (key2938, -1), (key2983, -1), (key2943, -1), (key2976, -1), (key2737, 1), (key2747, 1), (key2648, 1), (key2904, 1), (key2653, 1), (key2897, 1), (key2829, 2), (key2726, 2), (key2870, 2), (key2794, -2), (key2640, -2), (key2860, -2)]

def rawRow16632 : Integer.Sparse Key := [(key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2948, 2), (key2972, 2), (key2936, 2), (key2747, 1), (key2737, 1), (key2904, 1), (key2648, 1), (key2897, 1), (key2653, 1), (key2735, -2), (key2893, -2), (key2646, -2), (key2960, -1), (key2950, -1), (key2983, -1), (key2938, -1), (key2976, -1), (key2943, -1), (key2747, 1), (key2737, 1), (key2904, 1), (key2648, 1), (key2897, 1), (key2653, 1), (key2829, 2), (key2870, 2), (key2726, 2), (key2794, -2), (key2860, -2), (key2640, -2)]

def rawRow16633 : Integer.Sparse Key := [(key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2972, 2), (key2936, 2), (key2948, 2), (key2897, 1), (key2904, 1), (key2653, 1), (key2747, 1), (key2648, 1), (key2737, 1), (key2893, -2), (key2646, -2), (key2735, -2), (key2976, -1), (key2983, -1), (key2943, -1), (key2960, -1), (key2938, -1), (key2950, -1), (key2897, 1), (key2904, 1), (key2653, 1), (key2747, 1), (key2648, 1), (key2737, 1), (key2870, 2), (key2726, 2), (key2829, 2), (key2860, -2), (key2640, -2), (key2794, -2)]

def rawRow16634 : Integer.Sparse Key := [(key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2972, 2), (key2948, 2), (key2936, 2), (key2904, 1), (key2897, 1), (key2747, 1), (key2653, 1), (key2737, 1), (key2648, 1), (key2893, -2), (key2735, -2), (key2646, -2), (key2983, -1), (key2976, -1), (key2960, -1), (key2943, -1), (key2950, -1), (key2938, -1), (key2904, 1), (key2897, 1), (key2747, 1), (key2653, 1), (key2737, 1), (key2648, 1), (key2870, 2), (key2829, 2), (key2726, 2), (key2860, -2), (key2794, -2), (key2640, -2)]

def rawRow16635 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2674, 2), (key2796, 2), (key2796, 2), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2619, -2), (key2832, -2), (key2832, -2), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2738, 2), (key2898, 2), (key2898, 2), (key2649, -2), (key2905, -2), (key2905, -2)]

def rawRow16636 : Integer.Sparse Key := [(key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2796, 2), (key2674, 2), (key2796, 2), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2832, -2), (key2619, -2), (key2832, -2), (key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2898, 2), (key2738, 2), (key2898, 2), (key2905, -2), (key2649, -2), (key2905, -2)]

def rawRow16637 : Integer.Sparse Key := [(key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2796, 2), (key2796, 2), (key2674, 2), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2832, -2), (key2832, -2), (key2619, -2), (key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2898, 2), (key2898, 2), (key2738, 2), (key2905, -2), (key2905, -2), (key2649, -2)]

def rawRow16638 : Integer.Sparse Key := [(key2671, -1), (key2674, -1), (key2786, -1), (key2796, -1), (key2939, -1), (key2944, -1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, 1), (key2619, 1), (key2809, 1), (key2832, 1), (key2951, 1), (key2961, 1), (key2616, -2), (key2809, -2), (key2829, -2), (key2726, -1), (key2729, -1), (key2870, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2640, 1), (key2642, 1), (key2860, 1), (key2883, 1), (key2977, 1), (key2992, 1), (key2748, 2), (key2905, 2), (key2913, 2), (key2654, -2), (key2898, -2), (key2913, -2)]

def rawRow16639 : Integer.Sparse Key := [(key2674, -1), (key2671, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2939, -1), (key2671, 2), (key2794, 2), (key2786, 2), (key2619, 1), (key2616, 1), (key2832, 1), (key2809, 1), (key2961, 1), (key2951, 1), (key2616, -2), (key2829, -2), (key2809, -2), (key2729, -1), (key2726, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2984, -1), (key2642, 1), (key2640, 1), (key2883, 1), (key2860, 1), (key2992, 1), (key2977, 1), (key2748, 2), (key2913, 2), (key2905, 2), (key2654, -2), (key2913, -2), (key2898, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow16640 : Integer.Sparse Key := [(key2786, -1), (key2939, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, 1), (key2951, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2809, -2), (key2616, -2), (key2829, -2), (key2870, -1), (key2984, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2860, 1), (key2977, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2905, 2), (key2748, 2), (key2913, 2), (key2898, -2), (key2654, -2), (key2913, -2)]

def rawRow16641 : Integer.Sparse Key := [(key2939, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2796, -1), (key2674, -1), (key2786, 2), (key2794, 2), (key2671, 2), (key2951, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2832, 1), (key2619, 1), (key2809, -2), (key2829, -2), (key2616, -2), (key2984, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2883, -1), (key2729, -1), (key2977, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2883, 1), (key2642, 1), (key2905, 2), (key2913, 2), (key2748, 2), (key2898, -2), (key2913, -2), (key2654, -2)]

def rawRow16642 : Integer.Sparse Key := [(key2796, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2671, -1), (key2786, -1), (key2794, 2), (key2671, 2), (key2786, 2), (key2832, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2616, 1), (key2809, 1), (key2829, -2), (key2616, -2), (key2809, -2), (key2883, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2726, -1), (key2870, -1), (key2883, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2640, 1), (key2860, 1), (key2913, 2), (key2748, 2), (key2905, 2), (key2913, -2), (key2654, -2), (key2898, -2)]

def rawRow16643 : Integer.Sparse Key := [(key2944, -1), (key2796, -1), (key2939, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2794, 2), (key2786, 2), (key2671, 2), (key2961, 1), (key2832, 1), (key2951, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2829, -2), (key2809, -2), (key2616, -2), (key2992, -1), (key2883, -1), (key2984, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2992, 1), (key2883, 1), (key2977, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2913, 2), (key2905, 2), (key2748, 2), (key2913, -2), (key2898, -2), (key2654, -2)]

def rawRow16644 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2738, 2), (key2898, 2), (key2898, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2649, -2), (key2905, -2), (key2905, -2), (key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2674, 2), (key2796, 2), (key2796, 2), (key2619, -2), (key2832, -2), (key2832, -2)]

def rawRow16645 : Integer.Sparse Key := [(key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2898, 2), (key2738, 2), (key2898, 2), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2905, -2), (key2649, -2), (key2905, -2), (key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, -2), (key2619, -2), (key2832, -2)]

def rawRow16646 : Integer.Sparse Key := [(key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2898, 2), (key2898, 2), (key2738, 2), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2905, -2), (key2905, -2), (key2649, -2), (key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2796, 2), (key2796, 2), (key2674, 2), (key2832, -2), (key2832, -2), (key2619, -2)]

def rawRow16647 : Integer.Sparse Key := [(key2706, -1), (key2738, -1), (key2809, -1), (key2898, -1), (key2951, -1), (key2977, -1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, 1), (key2649, 1), (key2786, 1), (key2905, 1), (key2939, 1), (key2984, 1), (key2632, -2), (key2786, -2), (key2870, -2), (key2726, -1), (key2748, -1), (key2829, -1), (key2913, -1), (key2961, -1), (key2992, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2913, 1), (key2944, 1), (key2992, 1), (key2729, 2), (key2832, 2), (key2883, 2), (key2642, -2), (key2796, -2), (key2883, -2)]

def rawRow16648 : Integer.Sparse Key := [(key2738, -1), (key2706, -1), (key2898, -1), (key2809, -1), (key2977, -1), (key2951, -1), (key2706, 2), (key2860, 2), (key2809, 2), (key2649, 1), (key2632, 1), (key2905, 1), (key2786, 1), (key2984, 1), (key2939, 1), (key2632, -2), (key2870, -2), (key2786, -2), (key2748, -1), (key2726, -1), (key2913, -1), (key2829, -1), (key2992, -1), (key2961, -1), (key2654, 1), (key2640, 1), (key2913, 1), (key2794, 1), (key2992, 1), (key2944, 1), (key2729, 2), (key2883, 2), (key2832, 2), (key2642, -2), (key2883, -2), (key2796, -2)]

def rawRow16649 : Integer.Sparse Key := [(key2809, -1), (key2951, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, 1), (key2939, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2786, -2), (key2632, -2), (key2870, -2), (key2829, -1), (key2961, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2794, 1), (key2944, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2832, 2), (key2729, 2), (key2883, 2), (key2796, -2), (key2642, -2), (key2883, -2)]

def rawRow16650 : Integer.Sparse Key := [(key2951, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2898, -1), (key2738, -1), (key2809, 2), (key2860, 2), (key2706, 2), (key2939, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2905, 1), (key2649, 1), (key2786, -2), (key2870, -2), (key2632, -2), (key2961, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2913, -1), (key2748, -1), (key2944, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2913, 1), (key2654, 1), (key2832, 2), (key2883, 2), (key2729, 2), (key2796, -2), (key2883, -2), (key2642, -2)]

def rawRow16651 : Integer.Sparse Key := [(key2898, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2706, -1), (key2809, -1), (key2860, 2), (key2706, 2), (key2809, 2), (key2905, 1), (key2984, 1), (key2649, 1), (key2939, 1), (key2632, 1), (key2786, 1), (key2870, -2), (key2632, -2), (key2786, -2), (key2913, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2726, -1), (key2829, -1), (key2913, 1), (key2992, 1), (key2654, 1), (key2944, 1), (key2640, 1), (key2794, 1), (key2883, 2), (key2729, 2), (key2832, 2), (key2883, -2), (key2642, -2), (key2796, -2)]

def rawRow16652 : Integer.Sparse Key := [(key2977, -1), (key2898, -1), (key2951, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2860, 2), (key2809, 2), (key2706, 2), (key2984, 1), (key2905, 1), (key2939, 1), (key2649, 1), (key2786, 1), (key2632, 1), (key2870, -2), (key2786, -2), (key2632, -2), (key2992, -1), (key2913, -1), (key2961, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2992, 1), (key2913, 1), (key2944, 1), (key2654, 1), (key2794, 1), (key2640, 1), (key2883, 2), (key2832, 2), (key2729, 2), (key2883, -2), (key2796, -2), (key2642, -2)]

def rawRow16653 : Integer.Sparse Key := [(key2726, -1), (key2729, -1), (key2870, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2748, 2), (key2905, 2), (key2913, 2), (key2640, 1), (key2642, 1), (key2860, 1), (key2883, 1), (key2977, 1), (key2992, 1), (key2654, -2), (key2898, -2), (key2913, -2), (key2671, -1), (key2674, -1), (key2786, -1), (key2796, -1), (key2939, -1), (key2944, -1), (key2616, 1), (key2619, 1), (key2809, 1), (key2832, 1), (key2951, 1), (key2961, 1), (key2671, 2), (key2786, 2), (key2794, 2), (key2616, -2), (key2809, -2), (key2829, -2)]

def rawRow16654 : Integer.Sparse Key := [(key2729, -1), (key2726, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2984, -1), (key2748, 2), (key2913, 2), (key2905, 2), (key2642, 1), (key2640, 1), (key2883, 1), (key2860, 1), (key2992, 1), (key2977, 1), (key2654, -2), (key2913, -2), (key2898, -2), (key2674, -1), (key2671, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2939, -1), (key2619, 1), (key2616, 1), (key2832, 1), (key2809, 1), (key2961, 1), (key2951, 1), (key2671, 2), (key2794, 2), (key2786, 2), (key2616, -2), (key2829, -2), (key2809, -2)]

def rawRow16655 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2905, 2), (key2748, 2), (key2913, 2), (key2860, 1), (key2977, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2898, -2), (key2654, -2), (key2913, -2), (key2786, -1), (key2939, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2809, 1), (key2951, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2786, 2), (key2671, 2), (key2794, 2), (key2809, -2), (key2616, -2), (key2829, -2)]

def rawRow16656 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2883, -1), (key2729, -1), (key2905, 2), (key2913, 2), (key2748, 2), (key2977, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2883, 1), (key2642, 1), (key2898, -2), (key2913, -2), (key2654, -2), (key2939, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2796, -1), (key2674, -1), (key2951, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2832, 1), (key2619, 1), (key2786, 2), (key2794, 2), (key2671, 2), (key2809, -2), (key2829, -2), (key2616, -2)]

def rawRow16657 : Integer.Sparse Key := [(key2883, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2726, -1), (key2870, -1), (key2913, 2), (key2748, 2), (key2905, 2), (key2883, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2640, 1), (key2860, 1), (key2913, -2), (key2654, -2), (key2898, -2), (key2796, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2671, -1), (key2786, -1), (key2832, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2616, 1), (key2809, 1), (key2794, 2), (key2671, 2), (key2786, 2), (key2829, -2), (key2616, -2), (key2809, -2)]

def rawRow16658 : Integer.Sparse Key := [(key2992, -1), (key2883, -1), (key2984, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2913, 2), (key2905, 2), (key2748, 2), (key2992, 1), (key2883, 1), (key2977, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2913, -2), (key2898, -2), (key2654, -2), (key2944, -1), (key2796, -1), (key2939, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2961, 1), (key2832, 1), (key2951, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2794, 2), (key2786, 2), (key2671, 2), (key2829, -2), (key2809, -2), (key2616, -2)]

def rawRow16659 : Integer.Sparse Key := [(key2726, -1), (key2748, -1), (key2829, -1), (key2913, -1), (key2961, -1), (key2992, -1), (key2729, 2), (key2832, 2), (key2883, 2), (key2640, 1), (key2654, 1), (key2794, 1), (key2913, 1), (key2944, 1), (key2992, 1), (key2642, -2), (key2796, -2), (key2883, -2), (key2706, -1), (key2738, -1), (key2809, -1), (key2898, -1), (key2951, -1), (key2977, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2905, 1), (key2939, 1), (key2984, 1), (key2706, 2), (key2809, 2), (key2860, 2), (key2632, -2), (key2786, -2), (key2870, -2)]

def rawRow16660 : Integer.Sparse Key := [(key2748, -1), (key2726, -1), (key2913, -1), (key2829, -1), (key2992, -1), (key2961, -1), (key2729, 2), (key2883, 2), (key2832, 2), (key2654, 1), (key2640, 1), (key2913, 1), (key2794, 1), (key2992, 1), (key2944, 1), (key2642, -2), (key2883, -2), (key2796, -2), (key2738, -1), (key2706, -1), (key2898, -1), (key2809, -1), (key2977, -1), (key2951, -1), (key2649, 1), (key2632, 1), (key2905, 1), (key2786, 1), (key2984, 1), (key2939, 1), (key2706, 2), (key2860, 2), (key2809, 2), (key2632, -2), (key2870, -2), (key2786, -2)]

def rawRow16661 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2832, 2), (key2729, 2), (key2883, 2), (key2794, 1), (key2944, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2796, -2), (key2642, -2), (key2883, -2), (key2809, -1), (key2951, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2786, 1), (key2939, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2809, 2), (key2706, 2), (key2860, 2), (key2786, -2), (key2632, -2), (key2870, -2)]

def rawRow16662 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2913, -1), (key2748, -1), (key2832, 2), (key2883, 2), (key2729, 2), (key2944, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2913, 1), (key2654, 1), (key2796, -2), (key2883, -2), (key2642, -2), (key2951, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2898, -1), (key2738, -1), (key2939, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2905, 1), (key2649, 1), (key2809, 2), (key2860, 2), (key2706, 2), (key2786, -2), (key2870, -2), (key2632, -2)]

def rawRow16663 : Integer.Sparse Key := [(key2913, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2726, -1), (key2829, -1), (key2883, 2), (key2729, 2), (key2832, 2), (key2913, 1), (key2992, 1), (key2654, 1), (key2944, 1), (key2640, 1), (key2794, 1), (key2883, -2), (key2642, -2), (key2796, -2), (key2898, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2706, -1), (key2809, -1), (key2905, 1), (key2984, 1), (key2649, 1), (key2939, 1), (key2632, 1), (key2786, 1), (key2860, 2), (key2706, 2), (key2809, 2), (key2870, -2), (key2632, -2), (key2786, -2)]

def rawRow16664 : Integer.Sparse Key := [(key2992, -1), (key2913, -1), (key2961, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2883, 2), (key2832, 2), (key2729, 2), (key2992, 1), (key2913, 1), (key2944, 1), (key2654, 1), (key2794, 1), (key2640, 1), (key2883, -2), (key2796, -2), (key2642, -2), (key2977, -1), (key2898, -1), (key2951, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2984, 1), (key2905, 1), (key2939, 1), (key2649, 1), (key2786, 1), (key2632, 1), (key2860, 2), (key2809, 2), (key2706, 2), (key2870, -2), (key2786, -2), (key2632, -2)]

def rawRow16665 : Integer.Sparse Key := [(key2729, -1), (key2748, -1), (key2832, -1), (key2905, -1), (key2961, -1), (key2984, -1), (key2726, 2), (key2829, 2), (key2870, 2), (key2642, 1), (key2654, 1), (key2796, 1), (key2898, 1), (key2944, 1), (key2977, 1), (key2640, -2), (key2794, -2), (key2860, -2), (key2729, -1), (key2748, -1), (key2832, -1), (key2905, -1), (key2961, -1), (key2984, -1), (key2642, 1), (key2654, 1), (key2796, 1), (key2898, 1), (key2944, 1), (key2977, 1), (key2726, 2), (key2829, 2), (key2870, 2), (key2640, -2), (key2794, -2), (key2860, -2)]

def rawRow16666 : Integer.Sparse Key := [(key2748, -1), (key2729, -1), (key2905, -1), (key2832, -1), (key2984, -1), (key2961, -1), (key2726, 2), (key2870, 2), (key2829, 2), (key2654, 1), (key2642, 1), (key2898, 1), (key2796, 1), (key2977, 1), (key2944, 1), (key2640, -2), (key2860, -2), (key2794, -2), (key2748, -1), (key2729, -1), (key2905, -1), (key2832, -1), (key2984, -1), (key2961, -1), (key2654, 1), (key2642, 1), (key2898, 1), (key2796, 1), (key2977, 1), (key2944, 1), (key2726, 2), (key2870, 2), (key2829, 2), (key2640, -2), (key2860, -2), (key2794, -2)]

def rawRow16667 : Integer.Sparse Key := [(key2832, -1), (key2961, -1), (key2729, -1), (key2984, -1), (key2748, -1), (key2905, -1), (key2829, 2), (key2726, 2), (key2870, 2), (key2796, 1), (key2944, 1), (key2642, 1), (key2977, 1), (key2654, 1), (key2898, 1), (key2794, -2), (key2640, -2), (key2860, -2), (key2832, -1), (key2961, -1), (key2729, -1), (key2984, -1), (key2748, -1), (key2905, -1), (key2796, 1), (key2944, 1), (key2642, 1), (key2977, 1), (key2654, 1), (key2898, 1), (key2829, 2), (key2726, 2), (key2870, 2), (key2794, -2), (key2640, -2), (key2860, -2)]

def rawRow16668 : Integer.Sparse Key := [(key2961, -1), (key2832, -1), (key2984, -1), (key2729, -1), (key2905, -1), (key2748, -1), (key2829, 2), (key2870, 2), (key2726, 2), (key2944, 1), (key2796, 1), (key2977, 1), (key2642, 1), (key2898, 1), (key2654, 1), (key2794, -2), (key2860, -2), (key2640, -2), (key2961, -1), (key2832, -1), (key2984, -1), (key2729, -1), (key2905, -1), (key2748, -1), (key2944, 1), (key2796, 1), (key2977, 1), (key2642, 1), (key2898, 1), (key2654, 1), (key2829, 2), (key2870, 2), (key2726, 2), (key2794, -2), (key2860, -2), (key2640, -2)]

def rawRow16669 : Integer.Sparse Key := [(key2905, -1), (key2984, -1), (key2748, -1), (key2961, -1), (key2729, -1), (key2832, -1), (key2870, 2), (key2726, 2), (key2829, 2), (key2898, 1), (key2977, 1), (key2654, 1), (key2944, 1), (key2642, 1), (key2796, 1), (key2860, -2), (key2640, -2), (key2794, -2), (key2905, -1), (key2984, -1), (key2748, -1), (key2961, -1), (key2729, -1), (key2832, -1), (key2898, 1), (key2977, 1), (key2654, 1), (key2944, 1), (key2642, 1), (key2796, 1), (key2870, 2), (key2726, 2), (key2829, 2), (key2860, -2), (key2640, -2), (key2794, -2)]

def rawRow16670 : Integer.Sparse Key := [(key2984, -1), (key2905, -1), (key2961, -1), (key2748, -1), (key2832, -1), (key2729, -1), (key2870, 2), (key2829, 2), (key2726, 2), (key2977, 1), (key2898, 1), (key2944, 1), (key2654, 1), (key2796, 1), (key2642, 1), (key2860, -2), (key2794, -2), (key2640, -2), (key2984, -1), (key2905, -1), (key2961, -1), (key2748, -1), (key2832, -1), (key2729, -1), (key2977, 1), (key2898, 1), (key2944, 1), (key2654, 1), (key2796, 1), (key2642, 1), (key2870, 2), (key2829, 2), (key2726, 2), (key2860, -2), (key2794, -2), (key2640, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18579 : Integer.Sparse Key := [(key2608, 2), (key2614, 2), (key2614, 2), (key2624, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 2), (key2778, 2), (key2792, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key2918, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2922, 2), (key3007, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3025, 2)]

def rawRow18580 : Integer.Sparse Key := [(key2614, 2), (key2608, 2), (key2614, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2784, 2), (key2778, 2), (key2792, 2), (key2778, 2), (key2792, 2), (key2784, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key3007, 2), (key3009, 2), (key3007, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3022, 2)]

def rawRow18581 : Integer.Sparse Key := [(key2614, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2638, 2), (key2630, 2), (key2630, 2), (key2624, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2669, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2792, 2), (key2792, 2), (key2784, 2), (key2784, 2), (key2778, 2), (key2778, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key2922, 2), (key2922, 2), (key2919, 2), (key2919, 2), (key2918, 2), (key2918, 2), (key3009, 2), (key3007, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key3025, 2), (key3025, 2), (key3022, 2), (key3022, 2), (key3021, 2), (key3021, 2)]

def rawRow18582 : Integer.Sparse Key := [(key2624, 2), (key2630, 2), (key2638, 2), (key2608, 2), (key2614, 2), (key2624, 2), (key2638, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2801, 2), (key2807, 2), (key2851, 2), (key2858, 2), (key2918, 2), (key2919, 2), (key2778, 2), (key2784, 2), (key2851, 2), (key2868, 2), (key2918, 2), (key2922, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2), (key3011, 2), (key3021, 2), (key3022, 2), (key3007, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3022, 2), (key3025, 2)]

def rawRow18583 : Integer.Sparse Key := [(key2630, 2), (key2624, 2), (key2638, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2807, 2), (key2801, 2), (key2858, 2), (key2851, 2), (key2919, 2), (key2918, 2), (key2784, 2), (key2778, 2), (key2868, 2), (key2851, 2), (key2922, 2), (key2918, 2), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key2792, 2), (key2784, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2858, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3021, 2), (key3009, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3022, 2)]

def rawRow18584 : Integer.Sparse Key := [(key2624, 2), (key2638, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2608, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2638, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2724, 2), (key2851, 2), (key2918, 2), (key2801, 2), (key2919, 2), (key2807, 2), (key2858, 2), (key2851, 2), (key2918, 2), (key2778, 2), (key2922, 2), (key2784, 2), (key2868, 2), (key2801, 2), (key2919, 2), (key2778, 2), (key2922, 2), (key2792, 2), (key2827, 2), (key2807, 2), (key2858, 2), (key2784, 2), (key2868, 2), (key2792, 2), (key2827, 2), (key3021, 2), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3011, 2), (key3022, 2), (key3007, 2), (key3025, 2), (key3009, 2), (key3016, 2)]

def rawRow18585 : Integer.Sparse Key := [(key2638, 2), (key2624, 2), (key2630, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2608, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2752, 2), (key2698, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2918, 2), (key2851, 2), (key2919, 2), (key2801, 2), (key2858, 2), (key2807, 2), (key2918, 2), (key2851, 2), (key2922, 2), (key2778, 2), (key2868, 2), (key2784, 2), (key2919, 2), (key2801, 2), (key2922, 2), (key2778, 2), (key2827, 2), (key2792, 2), (key2858, 2), (key2807, 2), (key2868, 2), (key2784, 2), (key2827, 2), (key2792, 2), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3022, 2), (key3011, 2), (key3025, 2), (key3007, 2), (key3016, 2), (key3009, 2)]

def rawRow18586 : Integer.Sparse Key := [(key2630, 2), (key2638, 2), (key2624, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2704, 2), (key2752, 2), (key2698, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2858, 2), (key2919, 2), (key2807, 2), (key2918, 2), (key2801, 2), (key2851, 2), (key2868, 2), (key2922, 2), (key2784, 2), (key2918, 2), (key2778, 2), (key2851, 2), (key2827, 2), (key2922, 2), (key2792, 2), (key2919, 2), (key2778, 2), (key2801, 2), (key2827, 2), (key2868, 2), (key2792, 2), (key2858, 2), (key2784, 2), (key2807, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, 2), (key3007, 2), (key3021, 2), (key3016, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3007, 2), (key3011, 2)]

def rawRow18587 : Integer.Sparse Key := [(key2638, 2), (key2630, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2638, 2), (key2614, 2), (key2624, 2), (key2608, 2), (key2638, 2), (key2630, 2), (key2614, 2), (key2752, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2752, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2724, 2), (key2704, 2), (key2669, 2), (key2919, 2), (key2858, 2), (key2918, 2), (key2807, 2), (key2851, 2), (key2801, 2), (key2922, 2), (key2868, 2), (key2918, 2), (key2784, 2), (key2851, 2), (key2778, 2), (key2922, 2), (key2827, 2), (key2919, 2), (key2792, 2), (key2801, 2), (key2778, 2), (key2868, 2), (key2827, 2), (key2858, 2), (key2792, 2), (key2807, 2), (key2784, 2), (key3022, 2), (key3021, 2), (key3011, 2), (key3025, 2), (key3021, 2), (key3007, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3009, 2), (key3011, 2), (key3007, 2)]

def rawRow18588 : Integer.Sparse Key := [(key2657, 2), (key2657, 2), (key2659, 2), (key2614, 2), (key2614, 2), (key2630, 2), (key2630, 2), (key2638, 2), (key2638, 2), (key2608, 2), (key2624, 2), (key2624, 2), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2752, 2), (key2752, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key2827, 2), (key2827, 2), (key2868, 2), (key2868, 2), (key2922, 2), (key2922, 2), (key2792, 2), (key2792, 2), (key2858, 2), (key2858, 2), (key2919, 2), (key2919, 2), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2), (key2778, 2), (key2778, 2), (key2801, 2), (key2801, 2), (key2851, 2), (key2851, 2), (key3016, 2), (key3025, 2), (key3025, 2), (key3009, 2), (key3022, 2), (key3022, 2), (key3007, 2), (key3007, 2), (key3011, 2), (key3011, 2), (key3021, 2), (key3021, 2)]

def rawRow18589 : Integer.Sparse Key := [(key2657, 2), (key2659, 2), (key2657, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2624, 2), (key2608, 2), (key2624, 2), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key3025, 2), (key3016, 2), (key3025, 2), (key3022, 2), (key3009, 2), (key3022, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3021, 2), (key3007, 2), (key3011, 2)]

def rawRow18590 : Integer.Sparse Key := [(key2659, 2), (key2657, 2), (key2657, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2614, 2), (key2630, 2), (key2614, 2), (key2624, 2), (key2624, 2), (key2608, 2), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key2922, 2), (key2868, 2), (key2922, 2), (key2827, 2), (key2868, 2), (key2827, 2), (key2919, 2), (key2858, 2), (key2919, 2), (key2792, 2), (key2858, 2), (key2792, 2), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2), (key2851, 2), (key2801, 2), (key2851, 2), (key2778, 2), (key2801, 2), (key2778, 2), (key3025, 2), (key3025, 2), (key3016, 2), (key3022, 2), (key3022, 2), (key3009, 2), (key3021, 2), (key3011, 2), (key3021, 2), (key3007, 2), (key3011, 2), (key3007, 2)]

def rawRow18591 : Integer.Sparse Key := [(key2663, 2), (key2669, 2), (key2669, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2752, 2), (key2724, 2), (key2724, 2), (key2757, 2), (key2608, 2), (key2614, 2), (key2614, 2), (key2801, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key2624, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2851, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key2868, 2), (key3021, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key3025, 2), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2752, 2), (key2757, 2), (key2918, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2919, 2), (key2922, 2)]

def rawRow18592 : Integer.Sparse Key := [(key2669, 2), (key2663, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2752, 2), (key2698, 2), (key2752, 2), (key2704, 2), (key2724, 2), (key2757, 2), (key2724, 2), (key2614, 2), (key2608, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2624, 2), (key2638, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2698, 2), (key2724, 2), (key2704, 2), (key2858, 2), (key2851, 2), (key2868, 2), (key2851, 2), (key2868, 2), (key2858, 2), (key3022, 2), (key3021, 2), (key3025, 2), (key3021, 2), (key3025, 2), (key3022, 2), (key2657, 2), (key2659, 2), (key2657, 2), (key2752, 2), (key2757, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2922, 2), (key2918, 2), (key2922, 2), (key2919, 2)]

def rawRow18593 : Integer.Sparse Key := [(key2669, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2752, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2724, 2), (key2614, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2827, 2), (key2807, 2), (key2807, 2), (key2801, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key2638, 2), (key2638, 2), (key2630, 2), (key2630, 2), (key2624, 2), (key2624, 2), (key2724, 2), (key2724, 2), (key2704, 2), (key2704, 2), (key2698, 2), (key2698, 2), (key2868, 2), (key2868, 2), (key2858, 2), (key2858, 2), (key2851, 2), (key2851, 2), (key3025, 2), (key3025, 2), (key3022, 2), (key3022, 2), (key3021, 2), (key3021, 2), (key2659, 2), (key2657, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, 2), (key2922, 2), (key2919, 2), (key2919, 2), (key2918, 2), (key2918, 2)]

def rawRow18594 : Integer.Sparse Key := [(key2698, 2), (key2704, 2), (key2724, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2752, 2), (key2724, 2), (key2757, 2), (key2669, 2), (key2704, 2), (key2752, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, 2), (key2614, 2), (key2801, 2), (key2827, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key2858, 2), (key3021, 2), (key3022, 2), (key2624, 2), (key2630, 2), (key2851, 2), (key2868, 2), (key3021, 2), (key3025, 2), (key2624, 2), (key2638, 2), (key2698, 2), (key2724, 2), (key3022, 2), (key3025, 2), (key2630, 2), (key2638, 2), (key2704, 2), (key2724, 2), (key2858, 2), (key2868, 2), (key2752, 2), (key2918, 2), (key2919, 2), (key2657, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2659, 2), (key2752, 2), (key2757, 2), (key2919, 2), (key2922, 2)]

def rawRow18595 : Integer.Sparse Key := [(key2704, 2), (key2698, 2), (key2724, 2), (key2669, 2), (key2663, 2), (key2752, 2), (key2698, 2), (key2757, 2), (key2724, 2), (key2669, 2), (key2752, 2), (key2704, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2704, 2), (key2698, 2), (key2858, 2), (key2851, 2), (key3022, 2), (key3021, 2), (key2630, 2), (key2624, 2), (key2868, 2), (key2851, 2), (key3025, 2), (key3021, 2), (key2638, 2), (key2624, 2), (key2724, 2), (key2698, 2), (key3025, 2), (key3022, 2), (key2638, 2), (key2630, 2), (key2724, 2), (key2704, 2), (key2868, 2), (key2858, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2918, 2), (key2659, 2), (key2657, 2), (key2757, 2), (key2752, 2), (key2922, 2), (key2919, 2)]

def rawRow18596 : Integer.Sparse Key := [(key2698, 2), (key2724, 2), (key2704, 2), (key2698, 2), (key2724, 2), (key2663, 2), (key2757, 2), (key2669, 2), (key2752, 2), (key2704, 2), (key2669, 2), (key2752, 2), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2608, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, 2), (key3021, 2), (key2698, 2), (key3022, 2), (key2704, 2), (key2858, 2), (key2851, 2), (key3021, 2), (key2624, 2), (key3025, 2), (key2630, 2), (key2868, 2), (key2698, 2), (key3022, 2), (key2624, 2), (key3025, 2), (key2638, 2), (key2724, 2), (key2704, 2), (key2858, 2), (key2630, 2), (key2868, 2), (key2638, 2), (key2724, 2), (key2918, 2), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2752, 2), (key2919, 2), (key2657, 2), (key2922, 2), (key2659, 2), (key2757, 2)]

def rawRow18597 : Integer.Sparse Key := [(key2724, 2), (key2698, 2), (key2704, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2663, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2752, 2), (key2669, 2), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key2608, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2698, 2), (key2858, 2), (key2704, 2), (key3021, 2), (key2851, 2), (key3025, 2), (key2624, 2), (key2868, 2), (key2630, 2), (key3022, 2), (key2698, 2), (key3025, 2), (key2624, 2), (key2724, 2), (key2638, 2), (key2858, 2), (key2704, 2), (key2868, 2), (key2630, 2), (key2724, 2), (key2638, 2), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2919, 2), (key2752, 2), (key2922, 2), (key2657, 2), (key2757, 2), (key2659, 2)]

def rawRow18598 : Integer.Sparse Key := [(key2704, 2), (key2724, 2), (key2698, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key2752, 2), (key2669, 2), (key2704, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2858, 2), (key3022, 2), (key2704, 2), (key3021, 2), (key2698, 2), (key2851, 2), (key2868, 2), (key3025, 2), (key2630, 2), (key3021, 2), (key2624, 2), (key2851, 2), (key2724, 2), (key3025, 2), (key2638, 2), (key3022, 2), (key2624, 2), (key2698, 2), (key2724, 2), (key2868, 2), (key2638, 2), (key2858, 2), (key2630, 2), (key2704, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, 2), (key2657, 2), (key2918, 2), (key2757, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2657, 2), (key2752, 2)]

def rawRow18599 : Integer.Sparse Key := [(key2724, 2), (key2704, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2724, 2), (key2669, 2), (key2698, 2), (key2663, 2), (key2752, 2), (key2704, 2), (key2669, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2827, 2), (key2614, 2), (key2801, 2), (key2608, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key3022, 2), (key2858, 2), (key3021, 2), (key2704, 2), (key2851, 2), (key2698, 2), (key3025, 2), (key2868, 2), (key3021, 2), (key2630, 2), (key2851, 2), (key2624, 2), (key3025, 2), (key2724, 2), (key3022, 2), (key2638, 2), (key2698, 2), (key2624, 2), (key2868, 2), (key2724, 2), (key2858, 2), (key2638, 2), (key2704, 2), (key2630, 2), (key2919, 2), (key2918, 2), (key2752, 2), (key2922, 2), (key2918, 2), (key2657, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2659, 2), (key2752, 2), (key2657, 2)]

def rawRow18600 : Integer.Sparse Key := [(key2752, 2), (key2752, 2), (key2757, 2), (key2669, 2), (key2669, 2), (key2704, 2), (key2704, 2), (key2724, 2), (key2724, 2), (key2663, 2), (key2698, 2), (key2698, 2), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2614, 2), (key2807, 2), (key2807, 2), (key2827, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2801, 2), (key2724, 2), (key2724, 2), (key2868, 2), (key2868, 2), (key3025, 2), (key3025, 2), (key2638, 2), (key2638, 2), (key2858, 2), (key2858, 2), (key3022, 2), (key3022, 2), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2), (key2624, 2), (key2624, 2), (key2698, 2), (key2698, 2), (key2851, 2), (key2851, 2), (key2757, 2), (key2922, 2), (key2922, 2), (key2659, 2), (key2919, 2), (key2919, 2), (key2657, 2), (key2657, 2), (key2752, 2), (key2752, 2), (key2918, 2), (key2918, 2)]

def rawRow18601 : Integer.Sparse Key := [(key2752, 2), (key2757, 2), (key2752, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2698, 2), (key2663, 2), (key2698, 2), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2608, 2), (key2801, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2922, 2), (key2757, 2), (key2922, 2), (key2919, 2), (key2659, 2), (key2919, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2918, 2), (key2657, 2), (key2752, 2)]

def rawRow18602 : Integer.Sparse Key := [(key2757, 2), (key2752, 2), (key2752, 2), (key2724, 2), (key2704, 2), (key2724, 2), (key2669, 2), (key2704, 2), (key2669, 2), (key2698, 2), (key2698, 2), (key2663, 2), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2614, 2), (key2801, 2), (key2801, 2), (key2608, 2), (key3025, 2), (key2868, 2), (key3025, 2), (key2724, 2), (key2868, 2), (key2724, 2), (key3022, 2), (key2858, 2), (key3022, 2), (key2638, 2), (key2858, 2), (key2638, 2), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2), (key2851, 2), (key2698, 2), (key2851, 2), (key2624, 2), (key2698, 2), (key2624, 2), (key2922, 2), (key2922, 2), (key2757, 2), (key2919, 2), (key2919, 2), (key2659, 2), (key2918, 2), (key2752, 2), (key2918, 2), (key2657, 2), (key2752, 2), (key2657, 2)]

def rawRow18603 : Integer.Sparse Key := [(key2778, 2), (key2784, 2), (key2792, 2), (key2801, 2), (key2807, 2), (key2851, 2), (key2918, 2), (key2858, 2), (key2919, 2), (key2827, 2), (key2868, 2), (key2922, 2), (key2624, 2), (key2630, 2), (key2638, 2), (key2698, 2), (key2704, 2), (key2851, 2), (key3021, 2), (key2858, 2), (key3022, 2), (key2724, 2), (key2868, 2), (key3025, 2), (key2608, 2), (key2614, 2), (key2624, 2), (key2638, 2), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 2), (key2698, 2), (key2724, 2), (key2752, 2), (key2757, 2), (key2778, 2), (key2792, 2), (key2801, 2), (key2827, 2), (key2919, 2), (key2922, 2), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3022, 2), (key3025, 2), (key2614, 2), (key2630, 2), (key2638, 2), (key2669, 2), (key2704, 2), (key2724, 2), (key2784, 2), (key2792, 2), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, 2)]

def rawRow18604 : Integer.Sparse Key := [(key2784, 2), (key2778, 2), (key2792, 2), (key2807, 2), (key2801, 2), (key2918, 2), (key2851, 2), (key2919, 2), (key2858, 2), (key2827, 2), (key2922, 2), (key2868, 2), (key2630, 2), (key2624, 2), (key2638, 2), (key2704, 2), (key2698, 2), (key3021, 2), (key2851, 2), (key3022, 2), (key2858, 2), (key2724, 2), (key3025, 2), (key2868, 2), (key2614, 2), (key2608, 2), (key2638, 2), (key2624, 2), (key2659, 2), (key2657, 2), (key2669, 2), (key2663, 2), (key2724, 2), (key2698, 2), (key2757, 2), (key2752, 2), (key2792, 2), (key2778, 2), (key2827, 2), (key2801, 2), (key2922, 2), (key2919, 2), (key3009, 2), (key3007, 2), (key3016, 2), (key3011, 2), (key3025, 2), (key3022, 2), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, 2), (key2724, 2), (key2704, 2), (key2792, 2), (key2784, 2), (key2827, 2), (key2807, 2), (key2868, 2), (key2858, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow168 : Integer.Sparse Key := [(key2612, -2), (key2612, 1), (key2618, 1), (key2628, 2), (key2628, -1), (key2641, -1), (key2646, -1), (key2648, -1), (key2646, 1), (key2653, 1), (key2667, 2), (key2667, -1), (key2673, -1), (key2702, -2), (key2702, 1), (key2728, 1), (key2735, 1), (key2737, 1), (key2735, -1), (key2747, -1), (key2782, -2), (key2782, 1), (key2795, 1), (key2805, 2), (key2805, -1), (key2831, -1), (key2893, -1), (key2897, -1), (key2893, 1), (key2904, 1), (key2936, 1), (key2938, 1), (key2936, -1), (key2943, -1), (key2948, -1), (key2950, -1), (key2948, 1), (key2960, 1), (key2972, 1), (key2976, 1), (key2972, -1), (key2983, -1)]

def rawRow169 : Integer.Sparse Key := [(key2616, -2), (key2618, 1), (key2612, 1), (key2628, 2), (key2641, -1), (key2628, -1), (key2648, -1), (key2646, -1), (key2653, 1), (key2646, 1), (key2667, 2), (key2673, -1), (key2667, -1), (key2702, -2), (key2728, 1), (key2702, 1), (key2737, 1), (key2735, 1), (key2747, -1), (key2735, -1), (key2782, -2), (key2795, 1), (key2782, 1), (key2805, 2), (key2831, -1), (key2805, -1), (key2897, -1), (key2893, -1), (key2904, 1), (key2893, 1), (key2938, 1), (key2936, 1), (key2943, -1), (key2936, -1), (key2950, -1), (key2948, -1), (key2960, 1), (key2948, 1), (key2976, 1), (key2972, 1), (key2983, -1), (key2972, -1)]

def rawRow170 : Integer.Sparse Key := [(key2621, -2), (key2616, 1), (key2616, 1), (key2641, 2), (key2628, -1), (key2628, -1), (key2653, -1), (key2653, -1), (key2648, 1), (key2648, 1), (key2673, 2), (key2667, -1), (key2667, -1), (key2728, -2), (key2702, 1), (key2702, 1), (key2747, 1), (key2747, 1), (key2737, -1), (key2737, -1), (key2795, -2), (key2782, 1), (key2782, 1), (key2831, 2), (key2805, -1), (key2805, -1), (key2904, -1), (key2904, -1), (key2897, 1), (key2897, 1), (key2943, 1), (key2943, 1), (key2938, -1), (key2938, -1), (key2960, -1), (key2960, -1), (key2950, 1), (key2950, 1), (key2983, 1), (key2983, 1), (key2976, -1), (key2976, -1)]

def rawRow171 : Integer.Sparse Key := [(key2632, -2), (key2640, 1), (key2644, 1), (key2612, 2), (key2646, -1), (key2653, -1), (key2612, -1), (key2618, -1), (key2628, 1), (key2641, 1), (key2702, 2), (key2735, -1), (key2737, -1), (key2667, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2673, 1), (key2702, -1), (key2728, -1), (key2805, -2), (key2893, 1), (key2897, 1), (key2782, 2), (key2893, -1), (key2904, -1), (key2782, -1), (key2795, -1), (key2805, 1), (key2831, 1), (key2948, 1), (key2950, 1), (key2972, -1), (key2976, -1), (key2936, -1), (key2938, -1), (key2972, 1), (key2983, 1), (key2936, 1), (key2943, 1), (key2948, -1), (key2960, -1)]

def rawRow172 : Integer.Sparse Key := [(key2632, -2), (key2644, 1), (key2640, 1), (key2616, 2), (key2653, -1), (key2646, -1), (key2618, -1), (key2612, -1), (key2641, 1), (key2628, 1), (key2702, 2), (key2737, -1), (key2735, -1), (key2667, -2), (key2747, 1), (key2735, 1), (key2673, 1), (key2667, 1), (key2728, -1), (key2702, -1), (key2805, -2), (key2897, 1), (key2893, 1), (key2782, 2), (key2904, -1), (key2893, -1), (key2795, -1), (key2782, -1), (key2831, 1), (key2805, 1), (key2950, 1), (key2948, 1), (key2976, -1), (key2972, -1), (key2938, -1), (key2936, -1), (key2983, 1), (key2972, 1), (key2943, 1), (key2936, 1), (key2960, -1), (key2948, -1)]

def rawRow173 : Integer.Sparse Key := [(key2644, -2), (key2632, 1), (key2640, 1), (key2660, 2), (key2616, -1), (key2640, -1), (key2641, -1), (key2653, -1), (key2618, 1), (key2648, 1), (key2737, 2), (key2702, -1), (key2735, -1), (key2747, -2), (key2667, 1), (key2735, 1), (key2728, 1), (key2747, 1), (key2673, -1), (key2737, -1), (key2897, -2), (key2805, 1), (key2893, 1), (key2904, 2), (key2782, -1), (key2893, -1), (key2831, -1), (key2904, -1), (key2795, 1), (key2897, 1), (key2976, 1), (key2998, 1), (key2950, -1), (key2997, -1), (key2983, -1), (key3000, -1), (key2938, 1), (key2997, 1), (key2960, 1), (key3000, 1), (key2943, -1), (key2998, -1)]

def rawRow174 : Integer.Sparse Key := [(key2644, -2), (key2640, 1), (key2632, 1), (key2660, 2), (key2640, -1), (key2616, -1), (key2653, -1), (key2641, -1), (key2648, 1), (key2618, 1), (key2737, 2), (key2735, -1), (key2702, -1), (key2747, -2), (key2735, 1), (key2667, 1), (key2747, 1), (key2728, 1), (key2737, -1), (key2673, -1), (key2897, -2), (key2893, 1), (key2805, 1), (key2904, 2), (key2893, -1), (key2782, -1), (key2904, -1), (key2831, -1), (key2897, 1), (key2795, 1), (key2998, 1), (key2976, 1), (key2997, -1), (key2950, -1), (key3000, -1), (key2983, -1), (key2997, 1), (key2938, 1), (key3000, 1), (key2960, 1), (key2998, -1), (key2943, -1)]

def rawRow175 : Integer.Sparse Key := [(key2658, -2), (key2660, 1), (key2660, 1), (key2621, 2), (key2644, -1), (key2644, -1), (key2616, -1), (key2616, -1), (key2632, 1), (key2632, 1), (key2728, 2), (key2747, -1), (key2747, -1), (key2673, -2), (key2737, 1), (key2737, 1), (key2667, 1), (key2667, 1), (key2702, -1), (key2702, -1), (key2831, -2), (key2904, 1), (key2904, 1), (key2795, 2), (key2897, -1), (key2897, -1), (key2782, -1), (key2782, -1), (key2805, 1), (key2805, 1), (key2960, 1), (key2960, 1), (key2983, -1), (key2983, -1), (key2943, -1), (key2943, -1), (key2976, 1), (key2976, 1), (key2938, 1), (key2938, 1), (key2950, -1), (key2950, -1)]

def rawRow176 : Integer.Sparse Key := [(key2660, -2), (key2658, 1), (key2660, 1), (key2644, 2), (key2621, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2616, 1), (key2640, 1), (key2747, 2), (key2728, -1), (key2747, -1), (key2737, -2), (key2673, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2667, -1), (key2735, -1), (key2904, -2), (key2831, 1), (key2904, 1), (key2897, 2), (key2795, -1), (key2897, -1), (key2805, -1), (key2893, -1), (key2782, 1), (key2893, 1), (key2983, 1), (key3000, 1), (key2960, -1), (key3000, -1), (key2976, -1), (key2998, -1), (key2943, 1), (key2998, 1), (key2950, 1), (key2997, 1), (key2938, -1), (key2997, -1)]

def rawRow177 : Integer.Sparse Key := [(key2660, -2), (key2660, 1), (key2658, 1), (key2644, 2), (key2644, -1), (key2621, -1), (key2640, -1), (key2632, -1), (key2640, 1), (key2616, 1), (key2747, 2), (key2747, -1), (key2728, -1), (key2737, -2), (key2737, 1), (key2673, 1), (key2735, 1), (key2702, 1), (key2735, -1), (key2667, -1), (key2904, -2), (key2904, 1), (key2831, 1), (key2897, 2), (key2897, -1), (key2795, -1), (key2893, -1), (key2805, -1), (key2893, 1), (key2782, 1), (key3000, 1), (key2983, 1), (key3000, -1), (key2960, -1), (key2998, -1), (key2976, -1), (key2998, 1), (key2943, 1), (key2997, 1), (key2950, 1), (key2997, -1), (key2938, -1)]

def rawRow178 : Integer.Sparse Key := [(key2671, -2), (key2671, 1), (key2676, 1), (key2706, 2), (key2706, -1), (key2753, -1), (key2726, -1), (key2732, -1), (key2726, 1), (key2758, 1), (key2612, 2), (key2612, -1), (key2618, -1), (key2805, -2), (key2805, 1), (key2831, 1), (key2948, 1), (key2950, 1), (key2948, -1), (key2960, -1), (key2628, -2), (key2628, 1), (key2641, 1), (key2702, 2), (key2702, -1), (key2728, -1), (key2972, -1), (key2976, -1), (key2972, 1), (key2983, 1), (key2646, 1), (key2648, 1), (key2646, -1), (key2653, -1), (key2735, -1), (key2737, -1), (key2735, 1), (key2747, 1), (key2893, 1), (key2897, 1), (key2893, -1), (key2904, -1)]

def rawRow179 : Integer.Sparse Key := [(key2671, -2), (key2676, 1), (key2671, 1), (key2706, 2), (key2753, -1), (key2706, -1), (key2732, -1), (key2726, -1), (key2758, 1), (key2726, 1), (key2616, 2), (key2618, -1), (key2612, -1), (key2805, -2), (key2831, 1), (key2805, 1), (key2950, 1), (key2948, 1), (key2960, -1), (key2948, -1), (key2628, -2), (key2641, 1), (key2628, 1), (key2702, 2), (key2728, -1), (key2702, -1), (key2976, -1), (key2972, -1), (key2983, 1), (key2972, 1), (key2648, 1), (key2646, 1), (key2653, -1), (key2646, -1), (key2737, -1), (key2735, -1), (key2747, 1), (key2735, 1), (key2897, 1), (key2893, 1), (key2904, -1), (key2893, -1)]

def rawRow180 : Integer.Sparse Key := [(key2676, -2), (key2671, 1), (key2671, 1), (key2753, 2), (key2706, -1), (key2706, -1), (key2758, -1), (key2758, -1), (key2732, 1), (key2732, 1), (key2621, 2), (key2616, -1), (key2616, -1), (key2831, -2), (key2805, 1), (key2805, 1), (key2960, 1), (key2960, 1), (key2950, -1), (key2950, -1), (key2641, -2), (key2628, 1), (key2628, 1), (key2728, 2), (key2702, -1), (key2702, -1), (key2983, -1), (key2983, -1), (key2976, 1), (key2976, 1), (key2653, 1), (key2653, 1), (key2648, -1), (key2648, -1), (key2747, -1), (key2747, -1), (key2737, 1), (key2737, 1), (key2904, 1), (key2904, 1), (key2897, -1), (key2897, -1)]

def rawRow181 : Integer.Sparse Key := [(key2706, -2), (key2726, 1), (key2732, 1), (key2671, 2), (key2726, -1), (key2758, -1), (key2671, -1), (key2676, -1), (key2706, 1), (key2753, 1), (key2809, 2), (key2829, -1), (key2835, -1), (key2612, -2), (key2948, 1), (key2960, 1), (key2612, 1), (key2618, 1), (key2805, -1), (key2831, -1), (key2702, -2), (key2972, 1), (key2976, 1), (key2628, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2641, -1), (key2702, 1), (key2728, 1), (key2735, 1), (key2737, 1), (key2893, -1), (key2897, -1), (key2646, -1), (key2648, -1), (key2893, 1), (key2904, 1), (key2646, 1), (key2653, 1), (key2735, -1), (key2747, -1)]

def rawRow182 : Integer.Sparse Key := [(key2706, -2), (key2732, 1), (key2726, 1), (key2671, 2), (key2758, -1), (key2726, -1), (key2676, -1), (key2671, -1), (key2753, 1), (key2706, 1), (key2809, 2), (key2835, -1), (key2829, -1), (key2616, -2), (key2960, 1), (key2948, 1), (key2618, 1), (key2612, 1), (key2831, -1), (key2805, -1), (key2702, -2), (key2976, 1), (key2972, 1), (key2628, 2), (key2983, -1), (key2972, -1), (key2641, -1), (key2628, -1), (key2728, 1), (key2702, 1), (key2737, 1), (key2735, 1), (key2897, -1), (key2893, -1), (key2648, -1), (key2646, -1), (key2904, 1), (key2893, 1), (key2653, 1), (key2646, 1), (key2747, -1), (key2735, -1)]

def rawRow183 : Integer.Sparse Key := [(key2732, -2), (key2706, 1), (key2726, 1), (key2758, 2), (key2671, -1), (key2726, -1), (key2753, -1), (key2758, -1), (key2676, 1), (key2732, 1), (key2835, 2), (key2809, -1), (key2829, -1), (key3017, -2), (key2616, 1), (key2829, 1), (key2831, 1), (key2960, 1), (key2618, -1), (key2950, -1), (key2976, -2), (key2702, 1), (key2972, 1), (key2983, 2), (key2628, -1), (key2972, -1), (key2728, -1), (key2983, -1), (key2641, 1), (key2976, 1), (key2897, 1), (key2998, 1), (key2737, -1), (key2997, -1), (key2904, -1), (key3000, -1), (key2648, 1), (key2997, 1), (key2747, 1), (key3000, 1), (key2653, -1), (key2998, -1)]

def rawRow184 : Integer.Sparse Key := [(key2732, -2), (key2726, 1), (key2706, 1), (key2758, 2), (key2726, -1), (key2671, -1), (key2758, -1), (key2753, -1), (key2732, 1), (key2676, 1), (key2835, 2), (key2829, -1), (key2809, -1), (key3017, -2), (key2829, 1), (key2616, 1), (key2960, 1), (key2831, 1), (key2950, -1), (key2618, -1), (key2976, -2), (key2972, 1), (key2702, 1), (key2983, 2), (key2972, -1), (key2628, -1), (key2983, -1), (key2728, -1), (key2976, 1), (key2641, 1), (key2998, 1), (key2897, 1), (key2997, -1), (key2737, -1), (key3000, -1), (key2904, -1), (key2997, 1), (key2648, 1), (key3000, 1), (key2747, 1), (key2998, -1), (key2653, -1)]

def rawRow185 : Integer.Sparse Key := [(key2753, -2), (key2758, 1), (key2758, 1), (key2676, 2), (key2732, -1), (key2732, -1), (key2671, -1), (key2671, -1), (key2706, 1), (key2706, 1), (key3012, 2), (key3017, -1), (key3017, -1), (key2621, -2), (key2835, 1), (key2835, 1), (key2616, 1), (key2616, 1), (key2809, -1), (key2809, -1), (key2728, -2), (key2983, 1), (key2983, 1), (key2641, 2), (key2976, -1), (key2976, -1), (key2628, -1), (key2628, -1), (key2702, 1), (key2702, 1), (key2747, 1), (key2747, 1), (key2904, -1), (key2904, -1), (key2653, -1), (key2653, -1), (key2897, 1), (key2897, 1), (key2648, 1), (key2648, 1), (key2737, -1), (key2737, -1)]

def rawRow186 : Integer.Sparse Key := [(key2758, -2), (key2753, 1), (key2758, 1), (key2732, 2), (key2676, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2671, 1), (key2726, 1), (key3017, 2), (key3012, -1), (key3017, -1), (key2835, -2), (key2621, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2616, -1), (key2829, -1), (key2983, -2), (key2728, 1), (key2983, 1), (key2976, 2), (key2641, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2628, 1), (key2972, 1), (key2904, 1), (key3000, 1), (key2747, -1), (key3000, -1), (key2897, -1), (key2998, -1), (key2653, 1), (key2998, 1), (key2737, 1), (key2997, 1), (key2648, -1), (key2997, -1)]

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

def rawRow1764 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2402, 1), (key2408, 1), (key2402, 1), (key2439, 1), (key2408, 1), (key2439, 1), (key2468, 2), (key2468, 2), (key2505, 2), (key2468, -1), (key2481, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2505, -1), (key2535, -1), (key2537, -1), (key2535, -1), (key2553, -1), (key2537, -1), (key2553, -1), (key2535, 1), (key2542, 1), (key2535, 1), (key2553, 1), (key2542, 1), (key2553, 1)]

def rawRow1765 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 1), (key2402, 1), (key2439, 1), (key2402, 1), (key2439, 1), (key2408, 1), (key2468, 2), (key2505, 2), (key2468, 2), (key2481, -1), (key2468, -1), (key2505, -1), (key2468, -1), (key2505, -1), (key2481, -1), (key2537, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2537, -1), (key2542, 1), (key2535, 1), (key2553, 1), (key2535, 1), (key2553, 1), (key2542, 1)]

def rawRow1766 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2439, 1), (key2439, 1), (key2408, 1), (key2408, 1), (key2402, 1), (key2402, 1), (key2505, 2), (key2468, 2), (key2468, 2), (key2505, -1), (key2505, -1), (key2481, -1), (key2481, -1), (key2468, -1), (key2468, -1), (key2553, -1), (key2553, -1), (key2537, -1), (key2537, -1), (key2535, -1), (key2535, -1), (key2553, 1), (key2553, 1), (key2542, 1), (key2542, 1), (key2535, 1), (key2535, 1)]

def rawRow1767 : Integer.Sparse Key := [(key2408, -2), (key2408, -2), (key2408, -2), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2402, 1), (key2481, 2), (key2481, 2), (key2481, 2), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2468, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2542, -1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1), (key2537, 1)]

def rawRow1768 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key3020, -2), (key2878, 1), (key2884, 1), (key2878, 1), (key3029, 1), (key2884, 1), (key3029, 1), (key2402, 2), (key2402, 2), (key2439, 2), (key2535, -1), (key2542, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2553, -1), (key2402, -1), (key2408, -1), (key2402, -1), (key2439, -1), (key2408, -1), (key2439, -1), (key2468, 1), (key2481, 1), (key2468, 1), (key2505, 1), (key2481, 1), (key2505, 1)]

def rawRow1769 : Integer.Sparse Key := [(key2847, -2), (key3020, -2), (key2847, -2), (key2884, 1), (key2878, 1), (key3029, 1), (key2878, 1), (key3029, 1), (key2884, 1), (key2402, 2), (key2439, 2), (key2402, 2), (key2542, -1), (key2535, -1), (key2553, -1), (key2535, -1), (key2553, -1), (key2542, -1), (key2408, -1), (key2402, -1), (key2439, -1), (key2402, -1), (key2439, -1), (key2408, -1), (key2481, 1), (key2468, 1), (key2505, 1), (key2468, 1), (key2505, 1), (key2481, 1)]

def rawRow1770 : Integer.Sparse Key := [(key3020, -2), (key2847, -2), (key2847, -2), (key3029, 1), (key3029, 1), (key2884, 1), (key2884, 1), (key2878, 1), (key2878, 1), (key2439, 2), (key2402, 2), (key2402, 2), (key2553, -1), (key2553, -1), (key2542, -1), (key2542, -1), (key2535, -1), (key2535, -1), (key2439, -1), (key2439, -1), (key2408, -1), (key2408, -1), (key2402, -1), (key2402, -1), (key2505, 1), (key2505, 1), (key2481, 1), (key2481, 1), (key2468, 1), (key2468, 1)]

def rawRow1771 : Integer.Sparse Key := [(key2596, -2), (key2884, -2), (key2884, -2), (key2591, 1), (key2591, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key2605, 2), (key2926, 2), (key2926, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2391, -1), (key2391, -1), (key2481, -1), (key2481, -1), (key2542, -1), (key2542, -1), (key2380, 1), (key2380, 1), (key2408, 1), (key2408, 1), (key2537, 1), (key2537, 1)]

def rawRow1772 : Integer.Sparse Key := [(key2884, -2), (key2596, -2), (key2884, -2), (key2847, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2926, 2), (key2605, 2), (key2926, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2481, -1), (key2542, -1), (key2391, -1), (key2542, -1), (key2391, -1), (key2481, -1), (key2408, 1), (key2537, 1), (key2380, 1), (key2537, 1), (key2380, 1), (key2408, 1)]

def rawRow1773 : Integer.Sparse Key := [(key2884, -2), (key2884, -2), (key2596, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2591, 1), (key2847, 1), (key2591, 1), (key2926, 2), (key2926, 2), (key2605, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2542, -1), (key2481, -1), (key2542, -1), (key2391, -1), (key2481, -1), (key2391, -1), (key2537, 1), (key2408, 1), (key2537, 1), (key2380, 1), (key2408, 1), (key2380, 1)]

def rawRow1774 : Integer.Sparse Key := [(key2917, -2), (key2917, -2), (key2917, -2), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2926, 1), (key2775, 2), (key2775, 2), (key2775, 2), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2884, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2770, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

def rawRow1775 : Integer.Sparse Key := [(key2605, -2), (key2926, -2), (key2926, -2), (key2605, 1), (key2605, 1), (key2917, 1), (key2917, 1), (key2926, 1), (key2926, 1), (key2596, 2), (key2884, 2), (key2884, 2), (key2596, -1), (key2596, -1), (key2775, -1), (key2775, -1), (key2884, -1), (key2884, -1), (key2591, -1), (key2591, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

def rawRow1776 : Integer.Sparse Key := [(key2926, -2), (key2605, -2), (key2926, -2), (key2917, 1), (key2926, 1), (key2605, 1), (key2926, 1), (key2605, 1), (key2917, 1), (key2884, 2), (key2596, 2), (key2884, 2), (key2775, -1), (key2884, -1), (key2596, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

def rawRow1777 : Integer.Sparse Key := [(key2926, -2), (key2926, -2), (key2605, -2), (key2926, 1), (key2917, 1), (key2926, 1), (key2605, 1), (key2917, 1), (key2605, 1), (key2884, 2), (key2884, 2), (key2596, 2), (key2884, -1), (key2775, -1), (key2884, -1), (key2596, -1), (key2775, -1), (key2596, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2591, -1), (key2847, -1), (key2591, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

def rawRow1781 : Integer.Sparse Key := [(key1269, -6), (key1250, 2), (key1250, 2), (key1250, 2), (key1892, 6), (key1525, -2), (key1525, -2), (key1525, -2), (key1914, -2), (key1914, -2), (key1914, -2), (key1677, 2), (key1677, 2), (key1677, 2)]

def rawRow1788 : Integer.Sparse Key := [(key1892, -6), (key1914, 2), (key1914, 2), (key1914, 2), (key1269, 6), (key1677, -2), (key1677, -2), (key1677, -2), (key1250, -2), (key1250, -2), (key1250, -2), (key1525, 2), (key1525, 2), (key1525, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow1795 : Integer.Sparse Key := [(key2388, -2), (key2388, -2), (key2388, -2), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2376, 1), (key2435, 2), (key2435, 2), (key2435, 2), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2404, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2501, -1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1), (key2478, 1)]

def rawRow1802 : Integer.Sparse Key := [(key3005, -2), (key3005, -2), (key3005, -2), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key3019, 1), (key2604, 2), (key2604, 2), (key2604, 2), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2916, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2589, -1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1), (key2768, 1)]

def rawRow1809 : Integer.Sparse Key := [(key979, -2), (key979, -2), (key979, -2), (key971, 6), (key1228, 2), (key1228, 2), (key1228, 2), (key1085, -2), (key1085, -2), (key1085, -2), (key1245, -6), (key1164, 2), (key1164, 2), (key1164, 2)]

def rawRow1816 : Integer.Sparse Key := [(key1228, -2), (key1228, -2), (key1228, -2), (key1245, 6), (key979, 2), (key979, 2), (key979, 2), (key1164, -2), (key1164, -2), (key1164, -2), (key971, -6), (key1085, 2), (key1085, 2), (key1085, 2)]

def rawRow1823 : Integer.Sparse Key := [(key2385, -6), (key2372, 2), (key2372, 2), (key2372, 2), (key2432, 6), (key2400, -2), (key2400, -2), (key2400, -2), (key2498, -2), (key2498, -2), (key2498, -2), (key2475, 2), (key2475, 2), (key2475, 2)]

def rawRow1830 : Integer.Sparse Key := [(key2432, -6), (key2498, 2), (key2498, 2), (key2498, 2), (key2385, 6), (key2475, -2), (key2475, -2), (key2475, -2), (key2372, -2), (key2372, -2), (key2372, -2), (key2400, 2), (key2400, 2), (key2400, 2)]

def rawRow1837 : Integer.Sparse Key := [(key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1526, 2), (key1526, 2), (key1526, 2), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1604, -1), (key1693, -2), (key1693, -2), (key1693, -2), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1), (key1640, 1)]

def rawRow1844 : Integer.Sparse Key := [(key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1693, 2), (key1693, 2), (key1693, 2), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1640, -1), (key1526, -2), (key1526, -2), (key1526, -2), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1), (key1604, 1)]

def rawRow1848 : Integer.Sparse Key := [(key2414, -2), (key2426, -2), (key2426, -2), (key2419, 2), (key2426, 2), (key2426, 2), (key2487, 2), (key2494, 2), (key2494, 2), (key2494, -6), (key2572, -2), (key2573, -2), (key2573, -2), (key2573, 6)]

def rawRow1849 : Integer.Sparse Key := [(key2426, -2), (key2414, -2), (key2426, -2), (key2426, 2), (key2419, 2), (key2426, 2), (key2494, 2), (key2487, 2), (key2494, 2), (key2494, -6), (key2573, -2), (key2572, -2), (key2573, -2), (key2573, 6)]

def rawRow1850 : Integer.Sparse Key := [(key2426, -2), (key2426, -2), (key2414, -2), (key2426, 2), (key2426, 2), (key2419, 2), (key2494, 2), (key2494, 2), (key2487, 2), (key2494, -6), (key2573, -2), (key2573, -2), (key2572, -2), (key2573, 6)]

def rawRow1851 : Integer.Sparse Key := [(key2419, -2), (key2419, -2), (key2419, -2), (key2414, 2), (key2414, 2), (key2414, 2), (key2494, 2), (key2494, 2), (key2494, 2), (key2487, -6), (key2573, -2), (key2573, -2), (key2573, -2), (key2572, 6)]

def rawRow1852 : Integer.Sparse Key := [(key3120, -2), (key3141, -2), (key3141, -2), (key3130, 2), (key3144, 2), (key3144, 2), (key2414, 2), (key2426, 2), (key2426, 2), (key2573, -6), (key2419, -2), (key2426, -2), (key2426, -2), (key2494, 6)]

def rawRow1853 : Integer.Sparse Key := [(key3141, -2), (key3120, -2), (key3141, -2), (key3144, 2), (key3130, 2), (key3144, 2), (key2426, 2), (key2414, 2), (key2426, 2), (key2573, -6), (key2426, -2), (key2419, -2), (key2426, -2), (key2494, 6)]

def rawRow1854 : Integer.Sparse Key := [(key3141, -2), (key3141, -2), (key3120, -2), (key3144, 2), (key3144, 2), (key3130, 2), (key2426, 2), (key2426, 2), (key2414, 2), (key2573, -6), (key2426, -2), (key2426, -2), (key2419, -2), (key2494, 6)]

def rawRow1858 : Integer.Sparse Key := [(key3141, -2), (key3141, -2), (key3141, -2), (key3144, 2), (key3144, 2), (key3144, 2), (key3038, 2), (key3038, 2), (key3038, 2), (key3130, -6), (key2414, -2), (key2414, -2), (key2414, -2), (key2487, 6)]

def rawRow1865 : Integer.Sparse Key := [(key1271, -2), (key1271, -2), (key1271, -2), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1259, 1), (key1894, 2), (key1894, 2), (key1894, 2), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1534, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1916, -1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1), (key1679, 1)]

def rawRow1872 : Integer.Sparse Key := [(key1894, -2), (key1894, -2), (key1894, -2), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1916, 1), (key1271, 2), (key1271, 2), (key1271, 2), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1679, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1259, -1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1), (key1534, 1)]

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

def rawRow8835 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2566, -6), (key2578, -6), (key2566, -6), (key2566, -6)]

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

def nodeValue1178 : Sparse Master := [(Sum.inr 1178, (1 / 1))]

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

def nodeValue1236 : Sparse Master := [(Sum.inr 1236, (1 / 1))]

def nodeValue1237 : Sparse Master := [(Sum.inr 1237, (1 / 1))]

def nodeValue1238 : Sparse Master := [(Sum.inr 1238, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


