-- Prove2me | Definitions.Def_OAIQ106D095
-- name    : OAIQ106D095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:58:35.688565+00:00
-- url     : https://prove2.me/theorems/ea135ff0-f7b3-4bfa-9dfd-066a850a175c
-- title:
--   Definitions bundle OAIQ106D095 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 540 declarations of OpenAI's Lean: 540 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow10950`, `OAI.MUB6.Certificate.GramRows.rawRow10951`, `OAI.MUB6.Certificate.GramRows.rawRow10952`, `OAI.MUB6.Certificate.GramRows.rawRow10953`, `OAI.MUB6.Certificate.GramRows.rawRow10954`, `OAI.MUB6.Certificate.GramRows.rawRow10955`, `OAI.MUB6.Certificate.GramRows.rawRow10956`, `OAI.MUB6.Certificate.GramRows.rawRow10957`, `OAI.MUB6.Certificate.GramRows.rawRow10958`, `OAI.MUB6.Certificate.GramRows.rawRow10959`, `OAI.MUB6.Certificate.GramRows.rawRow10960`, `OAI.MUB6.Certificate.GramRows.rawRow10961`, `OAI.MUB6.Certificate.GramRows.rawRow10962`, `OAI.MUB6.Certificate.GramRows.rawRow10963`, `OAI.MUB6.Certificate.GramRows.rawRow10964`, `OAI.MUB6.Certificate.GramRows.rawRow10965`, `OAI.MUB6.Certificate.GramRows.rawRow10966`, `OAI.MUB6.Certificate.GramRows.rawRow10967`, `OAI.MUB6.Certificate.GramRows.rawRow10968`, `OAI.MUB6.Certificate.GramRows.rawRow10969`, `OAI.MUB6.Certificate.GramRows.rawRow10970`, `OAI.MUB6.Certificate.GramRows.rawRow10971`, `OAI.MUB6.Certificate.GramRows.rawRow10972`, `OAI.MUB6.Certificate.GramRows.rawRow10973`, `OAI.MUB6.Certificate.GramRows.rawRow10974`, `OAI.MUB6.Certificate.GramRows.rawRow10975`, `OAI.MUB6.Certificate.GramRows.rawRow10976`, `OAI.MUB6.Certificate.GramRows.rawRow10977`, `OAI.MUB6.Certificate.GramRows.rawRow10978`, `OAI.MUB6.Certificate.GramRows.rawRow10979`, `OAI.MUB6.Certificate.GramRows.rawRow10980`, `OAI.MUB6.Certificate.GramRows.rawRow10981`, `OAI.MUB6.Certificate.GramRows.rawRow10982`, `OAI.MUB6.Certificate.GramRows.rawRow10983`, `OAI.MUB6.Certificate.GramRows.rawRow10984`, `OAI.MUB6.Certificate.GramRows.rawRow10985`, `OAI.MUB6.Certificate.GramRows.rawRow10986`, `OAI.MUB6.Certificate.GramRows.rawRow10987`, `OAI.MUB6.Certificate.GramRows.rawRow10988`, `OAI.MUB6.Certificate.GramRows.rawRow10989` and 500 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block109`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block111`, `MutuallyUnbiased_GramRows_Block112`, `MutuallyUnbiased_GramRows_Block113`, `MutuallyUnbiased_GramRows_Block114`, `MutuallyUnbiased_GramRows_Block115`, `MutuallyUnbiased_GramRows_Block116`, `MutuallyUnbiased_GramRows_Block117`, `MutuallyUnbiased_GramRows_Block118`, `MutuallyUnbiased_GramRows_Block119`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block92`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values19`.
--
--   **Imports.** It imports the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D209`, `OAIQ106D210`, `OAIQ106D211` and `OAIQ106D215`; the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval21_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval22_9`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_0`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEval23_22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow12`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow21`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow22`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow23`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block3.entryEvalRow9`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval13_0`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval14_0` and `OAI.MUB6.Certificate.GramEntries.Block4.entryEval6_0`.
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

def rawRow12 : Integer.Sparse Key := [(key305, -1), (key305, -1), (key302, 2), (key335, 1), (key335, 1), (key316, -1), (key316, -1), (key340, -2), (key328, 1), (key328, 1), (key239, 1), (key239, 1), (key236, -2), (key418, -1), (key418, -1), (key406, 1), (key406, 1), (key583, 2), (key578, -1), (key578, -1), (key260, -1), (key260, -1), (key248, 1), (key248, 1), (key328, 1), (key328, 1), (key316, -1), (key316, -1), (key601, -1), (key601, -1), (key595, 1), (key595, 1), (key271, 2), (key267, -1), (key267, -1), (key340, -2), (key335, 1), (key335, 1), (key475, 1), (key475, 1), (key469, -1), (key469, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10950 : Integer.Sparse Key := [(key2783, -2), (key2791, -2), (key2779, -2), (key2894, -2), (key2896, -2), (key2806, -2), (key2857, -2), (key2802, -2), (key2852, -2), (key2903, -2), (key2826, -2), (key2867, -2), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, 2), (key2975, 2), (key2703, 2), (key2857, 2), (key2699, 2), (key2852, 2), (key2982, 2), (key2723, 2), (key2867, 2)]

def rawRow10951 : Integer.Sparse Key := [(key2791, -2), (key2783, -2), (key2779, -2), (key2896, -2), (key2894, -2), (key2857, -2), (key2806, -2), (key2852, -2), (key2802, -2), (key2903, -2), (key2867, -2), (key2826, -2), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, 2), (key2973, 2), (key2857, 2), (key2703, 2), (key2852, 2), (key2699, 2), (key2982, 2), (key2867, 2), (key2723, 2)]

def rawRow10952 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2779, -2), (key2783, -2), (key2852, -2), (key2894, -2), (key2867, -2), (key2903, -2), (key2791, -2), (key2857, -2), (key2896, -2), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, 2), (key2629, 2), (key2852, 2), (key2973, 2), (key2867, 2), (key2982, 2), (key2637, 2), (key2857, 2), (key2975, 2)]

def rawRow10953 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2783, -2), (key2779, -2), (key2894, -2), (key2852, -2), (key2903, -2), (key2867, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, 2), (key2625, 2), (key2973, 2), (key2852, 2), (key2982, 2), (key2867, 2), (key2637, 2), (key2975, 2), (key2857, 2)]

def rawRow10954 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2852, -2), (key2867, -2), (key2779, -2), (key2903, -2), (key2783, -2), (key2894, -2), (key2857, -2), (key2791, -2), (key2896, -2), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, 2), (key2867, 2), (key2625, 2), (key2982, 2), (key2629, 2), (key2973, 2), (key2857, 2), (key2637, 2), (key2975, 2)]

def rawRow10955 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2867, -2), (key2852, -2), (key2903, -2), (key2779, -2), (key2894, -2), (key2783, -2), (key2857, -2), (key2896, -2), (key2791, -2), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, 2), (key2852, 2), (key2982, 2), (key2625, 2), (key2973, 2), (key2629, 2), (key2857, 2), (key2975, 2), (key2637, 2)]

def rawRow10956 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2894, -2), (key2903, -2), (key2783, -2), (key2867, -2), (key2779, -2), (key2852, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, 2), (key2982, 2), (key2629, 2), (key2867, 2), (key2625, 2), (key2852, 2), (key2975, 2), (key2637, 2), (key2857, 2)]

def rawRow10957 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2903, -2), (key2894, -2), (key2867, -2), (key2783, -2), (key2852, -2), (key2779, -2), (key2896, -2), (key2857, -2), (key2791, -2), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, 2), (key2973, 2), (key2867, 2), (key2629, 2), (key2852, 2), (key2625, 2), (key2975, 2), (key2857, 2), (key2637, 2)]

def rawRow10958 : Integer.Sparse Key := [(key2852, -2), (key2857, -2), (key2867, -2), (key2779, -2), (key2791, -2), (key2802, -2), (key2896, -2), (key2826, -2), (key2903, -2), (key2783, -2), (key2806, -2), (key2894, -2), (key2852, 2), (key2857, 2), (key2867, 2), (key2625, 2), (key2637, 2), (key2699, 2), (key2975, 2), (key2723, 2), (key2982, 2), (key2629, 2), (key2703, 2), (key2973, 2)]

def rawRow10959 : Integer.Sparse Key := [(key2857, -2), (key2852, -2), (key2867, -2), (key2791, -2), (key2779, -2), (key2896, -2), (key2802, -2), (key2903, -2), (key2826, -2), (key2783, -2), (key2894, -2), (key2806, -2), (key2857, 2), (key2852, 2), (key2867, 2), (key2637, 2), (key2625, 2), (key2975, 2), (key2699, 2), (key2982, 2), (key2723, 2), (key2629, 2), (key2973, 2), (key2703, 2)]

def rawRow10960 : Integer.Sparse Key := [(key2852, -2), (key2867, -2), (key2857, -2), (key2802, -2), (key2826, -2), (key2779, -2), (key2903, -2), (key2791, -2), (key2896, -2), (key2806, -2), (key2783, -2), (key2894, -2), (key2852, 2), (key2867, 2), (key2857, 2), (key2699, 2), (key2723, 2), (key2625, 2), (key2982, 2), (key2637, 2), (key2975, 2), (key2703, 2), (key2629, 2), (key2973, 2)]

def rawRow10961 : Integer.Sparse Key := [(key2867, -2), (key2852, -2), (key2857, -2), (key2826, -2), (key2802, -2), (key2903, -2), (key2779, -2), (key2896, -2), (key2791, -2), (key2806, -2), (key2894, -2), (key2783, -2), (key2867, 2), (key2852, 2), (key2857, 2), (key2723, 2), (key2699, 2), (key2982, 2), (key2625, 2), (key2975, 2), (key2637, 2), (key2703, 2), (key2973, 2), (key2629, 2)]

def rawRow10962 : Integer.Sparse Key := [(key2857, -2), (key2867, -2), (key2852, -2), (key2896, -2), (key2903, -2), (key2791, -2), (key2826, -2), (key2779, -2), (key2802, -2), (key2894, -2), (key2783, -2), (key2806, -2), (key2857, 2), (key2867, 2), (key2852, 2), (key2975, 2), (key2982, 2), (key2637, 2), (key2723, 2), (key2625, 2), (key2699, 2), (key2973, 2), (key2629, 2), (key2703, 2)]

def rawRow10963 : Integer.Sparse Key := [(key2867, -2), (key2857, -2), (key2852, -2), (key2903, -2), (key2896, -2), (key2826, -2), (key2791, -2), (key2802, -2), (key2779, -2), (key2894, -2), (key2806, -2), (key2783, -2), (key2867, 2), (key2857, 2), (key2852, 2), (key2982, 2), (key2975, 2), (key2723, 2), (key2637, 2), (key2699, 2), (key2625, 2), (key2973, 2), (key2703, 2), (key2629, 2)]

def rawRow10964 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2783, -2), (key2791, -2), (key2806, -2), (key2857, -2), (key2826, -2), (key2867, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2973, 2), (key2975, 2), (key2982, 2), (key2629, 2), (key2637, 2), (key2703, 2), (key2857, 2), (key2723, 2), (key2867, 2), (key2625, 2), (key2699, 2), (key2852, 2)]

def rawRow10965 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2791, -2), (key2783, -2), (key2857, -2), (key2806, -2), (key2867, -2), (key2826, -2), (key2779, -2), (key2852, -2), (key2802, -2), (key2975, 2), (key2973, 2), (key2982, 2), (key2637, 2), (key2629, 2), (key2857, 2), (key2703, 2), (key2867, 2), (key2723, 2), (key2625, 2), (key2852, 2), (key2699, 2)]

def rawRow10966 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2806, -2), (key2826, -2), (key2783, -2), (key2867, -2), (key2791, -2), (key2857, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2973, 2), (key2982, 2), (key2975, 2), (key2703, 2), (key2723, 2), (key2629, 2), (key2867, 2), (key2637, 2), (key2857, 2), (key2699, 2), (key2625, 2), (key2852, 2)]

def rawRow10967 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2826, -2), (key2806, -2), (key2867, -2), (key2783, -2), (key2857, -2), (key2791, -2), (key2802, -2), (key2852, -2), (key2779, -2), (key2982, 2), (key2973, 2), (key2975, 2), (key2723, 2), (key2703, 2), (key2867, 2), (key2629, 2), (key2857, 2), (key2637, 2), (key2699, 2), (key2852, 2), (key2625, 2)]

def rawRow10968 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2857, -2), (key2867, -2), (key2791, -2), (key2826, -2), (key2783, -2), (key2806, -2), (key2852, -2), (key2779, -2), (key2802, -2), (key2975, 2), (key2982, 2), (key2973, 2), (key2857, 2), (key2867, 2), (key2637, 2), (key2723, 2), (key2629, 2), (key2703, 2), (key2852, 2), (key2625, 2), (key2699, 2)]

def rawRow10969 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2867, -2), (key2857, -2), (key2826, -2), (key2791, -2), (key2806, -2), (key2783, -2), (key2852, -2), (key2802, -2), (key2779, -2), (key2982, 2), (key2975, 2), (key2973, 2), (key2867, 2), (key2857, 2), (key2723, 2), (key2637, 2), (key2703, 2), (key2629, 2), (key2852, 2), (key2699, 2), (key2625, 2)]

def rawRow10970 : Integer.Sparse Key := [(key2937, -2), (key2937, -2), (key2942, -2), (key2949, -2), (key2949, -2), (key2973, -2), (key2973, -2), (key2975, -2), (key2975, -2), (key2959, -2), (key2982, -2), (key2982, -2), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, 2), (key2736, 2), (key2894, 2), (key2894, 2), (key2896, 2), (key2896, 2), (key2746, 2), (key2903, 2), (key2903, 2)]

def rawRow10971 : Integer.Sparse Key := [(key2937, -2), (key2942, -2), (key2937, -2), (key2973, -2), (key2975, -2), (key2949, -2), (key2975, -2), (key2949, -2), (key2973, -2), (key2982, -2), (key2959, -2), (key2982, -2), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, 2), (key2896, 2), (key2736, 2), (key2896, 2), (key2736, 2), (key2894, 2), (key2903, 2), (key2746, 2), (key2903, 2)]

def rawRow10972 : Integer.Sparse Key := [(key2942, -2), (key2937, -2), (key2937, -2), (key2975, -2), (key2973, -2), (key2975, -2), (key2949, -2), (key2973, -2), (key2949, -2), (key2982, -2), (key2982, -2), (key2959, -2), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, 2), (key2894, 2), (key2896, 2), (key2736, 2), (key2894, 2), (key2736, 2), (key2903, 2), (key2903, 2), (key2746, 2)]

def rawRow10973 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2937, -2), (key2937, -2), (key2973, -2), (key2973, -2), (key2982, -2), (key2982, -2), (key2942, -2), (key2975, -2), (key2975, -2), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, 2), (key2647, 2), (key2894, 2), (key2894, 2), (key2903, 2), (key2903, 2), (key2652, 2), (key2896, 2), (key2896, 2)]

def rawRow10974 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2973, -2), (key2982, -2), (key2937, -2), (key2982, -2), (key2937, -2), (key2973, -2), (key2975, -2), (key2942, -2), (key2975, -2), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, 2), (key2903, 2), (key2647, 2), (key2903, 2), (key2647, 2), (key2894, 2), (key2896, 2), (key2652, 2), (key2896, 2)]

def rawRow10975 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2982, -2), (key2973, -2), (key2982, -2), (key2937, -2), (key2973, -2), (key2937, -2), (key2975, -2), (key2975, -2), (key2942, -2), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, 2), (key2894, 2), (key2903, 2), (key2647, 2), (key2894, 2), (key2647, 2), (key2896, 2), (key2896, 2), (key2652, 2)]

def rawRow10976 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2937, -2), (key2942, -2), (key2949, -2), (key2975, -2), (key2959, -2), (key2982, -2), (key2937, -2), (key2949, -2), (key2973, -2), (key2894, 2), (key2896, 2), (key2903, 2), (key2647, 2), (key2652, 2), (key2736, 2), (key2896, 2), (key2746, 2), (key2903, 2), (key2647, 2), (key2736, 2), (key2894, 2)]

def rawRow10977 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2942, -2), (key2937, -2), (key2975, -2), (key2949, -2), (key2982, -2), (key2959, -2), (key2937, -2), (key2973, -2), (key2949, -2), (key2896, 2), (key2894, 2), (key2903, 2), (key2652, 2), (key2647, 2), (key2896, 2), (key2736, 2), (key2903, 2), (key2746, 2), (key2647, 2), (key2894, 2), (key2736, 2)]

def rawRow10978 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2949, -2), (key2959, -2), (key2937, -2), (key2982, -2), (key2942, -2), (key2975, -2), (key2949, -2), (key2937, -2), (key2973, -2), (key2894, 2), (key2903, 2), (key2896, 2), (key2736, 2), (key2746, 2), (key2647, 2), (key2903, 2), (key2652, 2), (key2896, 2), (key2736, 2), (key2647, 2), (key2894, 2)]

def rawRow10979 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2959, -2), (key2949, -2), (key2982, -2), (key2937, -2), (key2975, -2), (key2942, -2), (key2949, -2), (key2973, -2), (key2937, -2), (key2903, 2), (key2894, 2), (key2896, 2), (key2746, 2), (key2736, 2), (key2903, 2), (key2647, 2), (key2896, 2), (key2652, 2), (key2736, 2), (key2894, 2), (key2647, 2)]

def rawRow10980 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2975, -2), (key2982, -2), (key2942, -2), (key2959, -2), (key2937, -2), (key2949, -2), (key2973, -2), (key2937, -2), (key2949, -2), (key2896, 2), (key2903, 2), (key2894, 2), (key2896, 2), (key2903, 2), (key2652, 2), (key2746, 2), (key2647, 2), (key2736, 2), (key2894, 2), (key2647, 2), (key2736, 2)]

def rawRow10981 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2982, -2), (key2975, -2), (key2959, -2), (key2942, -2), (key2949, -2), (key2937, -2), (key2973, -2), (key2949, -2), (key2937, -2), (key2903, 2), (key2896, 2), (key2894, 2), (key2903, 2), (key2896, 2), (key2746, 2), (key2652, 2), (key2736, 2), (key2647, 2), (key2894, 2), (key2736, 2), (key2647, 2)]

def rawRow10982 : Integer.Sparse Key := [(key1312, -2), (key1317, -2), (key1325, -2), (key1420, -2), (key1425, -2), (key1618, -2), (key1814, -2), (key1623, -2), (key1816, -2), (key1443, -2), (key1632, -2), (key1824, -2), (key1292, 1), (key1297, 1), (key1312, 1), (key1338, 1), (key1325, 1), (key1344, 1), (key1387, 1), (key1392, 1), (key1542, 1), (key1773, 1), (key1555, 1), (key1779, 1), (key1420, 1), (key1456, 1), (key1569, 1), (key1789, 1), (key1658, 1), (key1816, 1), (key1443, 1), (key1465, 1), (key1592, 1), (key1797, 1), (key1666, 1), (key1824, 1)]

def rawRow10983 : Integer.Sparse Key := [(key1317, -2), (key1312, -2), (key1325, -2), (key1425, -2), (key1420, -2), (key1814, -2), (key1618, -2), (key1816, -2), (key1623, -2), (key1443, -2), (key1824, -2), (key1632, -2), (key1297, 1), (key1292, 1), (key1338, 1), (key1312, 1), (key1344, 1), (key1325, 1), (key1392, 1), (key1387, 1), (key1773, 1), (key1542, 1), (key1779, 1), (key1555, 1), (key1456, 1), (key1420, 1), (key1789, 1), (key1569, 1), (key1816, 1), (key1658, 1), (key1465, 1), (key1443, 1), (key1797, 1), (key1592, 1), (key1824, 1), (key1666, 1)]

def rawRow10984 : Integer.Sparse Key := [(key1312, -2), (key1325, -2), (key1317, -2), (key1618, -2), (key1623, -2), (key1420, -2), (key1816, -2), (key1425, -2), (key1814, -2), (key1632, -2), (key1443, -2), (key1824, -2), (key1312, 1), (key1325, 1), (key1292, 1), (key1344, 1), (key1297, 1), (key1338, 1), (key1542, 1), (key1555, 1), (key1387, 1), (key1779, 1), (key1392, 1), (key1773, 1), (key1569, 1), (key1658, 1), (key1420, 1), (key1816, 1), (key1456, 1), (key1789, 1), (key1592, 1), (key1666, 1), (key1443, 1), (key1824, 1), (key1465, 1), (key1797, 1)]

def rawRow10985 : Integer.Sparse Key := [(key1325, -2), (key1312, -2), (key1317, -2), (key1623, -2), (key1618, -2), (key1816, -2), (key1420, -2), (key1814, -2), (key1425, -2), (key1632, -2), (key1824, -2), (key1443, -2), (key1325, 1), (key1312, 1), (key1344, 1), (key1292, 1), (key1338, 1), (key1297, 1), (key1555, 1), (key1542, 1), (key1779, 1), (key1387, 1), (key1773, 1), (key1392, 1), (key1658, 1), (key1569, 1), (key1816, 1), (key1420, 1), (key1789, 1), (key1456, 1), (key1666, 1), (key1592, 1), (key1824, 1), (key1443, 1), (key1797, 1), (key1465, 1)]

def rawRow10986 : Integer.Sparse Key := [(key1317, -2), (key1325, -2), (key1312, -2), (key1814, -2), (key1816, -2), (key1425, -2), (key1623, -2), (key1420, -2), (key1618, -2), (key1824, -2), (key1443, -2), (key1632, -2), (key1338, 1), (key1344, 1), (key1297, 1), (key1325, 1), (key1292, 1), (key1312, 1), (key1773, 1), (key1779, 1), (key1392, 1), (key1555, 1), (key1387, 1), (key1542, 1), (key1789, 1), (key1816, 1), (key1456, 1), (key1658, 1), (key1420, 1), (key1569, 1), (key1797, 1), (key1824, 1), (key1465, 1), (key1666, 1), (key1443, 1), (key1592, 1)]

def rawRow10987 : Integer.Sparse Key := [(key1325, -2), (key1317, -2), (key1312, -2), (key1816, -2), (key1814, -2), (key1623, -2), (key1425, -2), (key1618, -2), (key1420, -2), (key1824, -2), (key1632, -2), (key1443, -2), (key1344, 1), (key1338, 1), (key1325, 1), (key1297, 1), (key1312, 1), (key1292, 1), (key1779, 1), (key1773, 1), (key1555, 1), (key1392, 1), (key1542, 1), (key1387, 1), (key1816, 1), (key1789, 1), (key1658, 1), (key1456, 1), (key1569, 1), (key1420, 1), (key1824, 1), (key1797, 1), (key1666, 1), (key1465, 1), (key1592, 1), (key1443, 1)]

def rawRow10988 : Integer.Sparse Key := [(key1420, -2), (key1425, -2), (key1443, -2), (key1312, -2), (key1317, -2), (key1618, -2), (key1814, -2), (key1632, -2), (key1824, -2), (key1325, -2), (key1623, -2), (key1816, -2), (key1387, 1), (key1392, 1), (key1420, 1), (key1456, 1), (key1443, 1), (key1465, 1), (key1292, 1), (key1297, 1), (key1569, 1), (key1789, 1), (key1592, 1), (key1797, 1), (key1312, 1), (key1338, 1), (key1542, 1), (key1773, 1), (key1666, 1), (key1824, 1), (key1325, 1), (key1344, 1), (key1555, 1), (key1779, 1), (key1658, 1), (key1816, 1)]

def rawRow10989 : Integer.Sparse Key := [(key1425, -2), (key1420, -2), (key1443, -2), (key1317, -2), (key1312, -2), (key1814, -2), (key1618, -2), (key1824, -2), (key1632, -2), (key1325, -2), (key1816, -2), (key1623, -2), (key1392, 1), (key1387, 1), (key1456, 1), (key1420, 1), (key1465, 1), (key1443, 1), (key1297, 1), (key1292, 1), (key1789, 1), (key1569, 1), (key1797, 1), (key1592, 1), (key1338, 1), (key1312, 1), (key1773, 1), (key1542, 1), (key1824, 1), (key1666, 1), (key1344, 1), (key1325, 1), (key1779, 1), (key1555, 1), (key1816, 1), (key1658, 1)]

def rawRow10990 : Integer.Sparse Key := [(key1420, -2), (key1443, -2), (key1425, -2), (key1618, -2), (key1632, -2), (key1312, -2), (key1824, -2), (key1317, -2), (key1814, -2), (key1623, -2), (key1325, -2), (key1816, -2), (key1420, 1), (key1443, 1), (key1387, 1), (key1465, 1), (key1392, 1), (key1456, 1), (key1569, 1), (key1592, 1), (key1292, 1), (key1797, 1), (key1297, 1), (key1789, 1), (key1542, 1), (key1666, 1), (key1312, 1), (key1824, 1), (key1338, 1), (key1773, 1), (key1555, 1), (key1658, 1), (key1325, 1), (key1816, 1), (key1344, 1), (key1779, 1)]

def rawRow10991 : Integer.Sparse Key := [(key1443, -2), (key1420, -2), (key1425, -2), (key1632, -2), (key1618, -2), (key1824, -2), (key1312, -2), (key1814, -2), (key1317, -2), (key1623, -2), (key1816, -2), (key1325, -2), (key1443, 1), (key1420, 1), (key1465, 1), (key1387, 1), (key1456, 1), (key1392, 1), (key1592, 1), (key1569, 1), (key1797, 1), (key1292, 1), (key1789, 1), (key1297, 1), (key1666, 1), (key1542, 1), (key1824, 1), (key1312, 1), (key1773, 1), (key1338, 1), (key1658, 1), (key1555, 1), (key1816, 1), (key1325, 1), (key1779, 1), (key1344, 1)]

def rawRow10992 : Integer.Sparse Key := [(key1425, -2), (key1443, -2), (key1420, -2), (key1814, -2), (key1824, -2), (key1317, -2), (key1632, -2), (key1312, -2), (key1618, -2), (key1816, -2), (key1325, -2), (key1623, -2), (key1456, 1), (key1465, 1), (key1392, 1), (key1443, 1), (key1387, 1), (key1420, 1), (key1789, 1), (key1797, 1), (key1297, 1), (key1592, 1), (key1292, 1), (key1569, 1), (key1773, 1), (key1824, 1), (key1338, 1), (key1666, 1), (key1312, 1), (key1542, 1), (key1779, 1), (key1816, 1), (key1344, 1), (key1658, 1), (key1325, 1), (key1555, 1)]

def rawRow10993 : Integer.Sparse Key := [(key1443, -2), (key1425, -2), (key1420, -2), (key1824, -2), (key1814, -2), (key1632, -2), (key1317, -2), (key1618, -2), (key1312, -2), (key1816, -2), (key1623, -2), (key1325, -2), (key1465, 1), (key1456, 1), (key1443, 1), (key1392, 1), (key1420, 1), (key1387, 1), (key1797, 1), (key1789, 1), (key1592, 1), (key1297, 1), (key1569, 1), (key1292, 1), (key1824, 1), (key1773, 1), (key1666, 1), (key1338, 1), (key1542, 1), (key1312, 1), (key1816, 1), (key1779, 1), (key1658, 1), (key1344, 1), (key1555, 1), (key1325, 1)]

def rawRow10994 : Integer.Sparse Key := [(key1618, -2), (key1623, -2), (key1632, -2), (key1312, -2), (key1325, -2), (key1420, -2), (key1816, -2), (key1443, -2), (key1824, -2), (key1317, -2), (key1425, -2), (key1814, -2), (key1542, 1), (key1555, 1), (key1569, 1), (key1658, 1), (key1592, 1), (key1666, 1), (key1312, 1), (key1325, 1), (key1420, 1), (key1816, 1), (key1443, 1), (key1824, 1), (key1292, 1), (key1344, 1), (key1387, 1), (key1779, 1), (key1465, 1), (key1797, 1), (key1297, 1), (key1338, 1), (key1392, 1), (key1773, 1), (key1456, 1), (key1789, 1)]

def rawRow10995 : Integer.Sparse Key := [(key1623, -2), (key1618, -2), (key1632, -2), (key1325, -2), (key1312, -2), (key1816, -2), (key1420, -2), (key1824, -2), (key1443, -2), (key1317, -2), (key1814, -2), (key1425, -2), (key1555, 1), (key1542, 1), (key1658, 1), (key1569, 1), (key1666, 1), (key1592, 1), (key1325, 1), (key1312, 1), (key1816, 1), (key1420, 1), (key1824, 1), (key1443, 1), (key1344, 1), (key1292, 1), (key1779, 1), (key1387, 1), (key1797, 1), (key1465, 1), (key1338, 1), (key1297, 1), (key1773, 1), (key1392, 1), (key1789, 1), (key1456, 1)]

def rawRow10996 : Integer.Sparse Key := [(key1618, -2), (key1632, -2), (key1623, -2), (key1420, -2), (key1443, -2), (key1312, -2), (key1824, -2), (key1325, -2), (key1816, -2), (key1425, -2), (key1317, -2), (key1814, -2), (key1569, 1), (key1592, 1), (key1542, 1), (key1666, 1), (key1555, 1), (key1658, 1), (key1420, 1), (key1443, 1), (key1312, 1), (key1824, 1), (key1325, 1), (key1816, 1), (key1387, 1), (key1465, 1), (key1292, 1), (key1797, 1), (key1344, 1), (key1779, 1), (key1392, 1), (key1456, 1), (key1297, 1), (key1789, 1), (key1338, 1), (key1773, 1)]

def rawRow10997 : Integer.Sparse Key := [(key1632, -2), (key1618, -2), (key1623, -2), (key1443, -2), (key1420, -2), (key1824, -2), (key1312, -2), (key1816, -2), (key1325, -2), (key1425, -2), (key1814, -2), (key1317, -2), (key1592, 1), (key1569, 1), (key1666, 1), (key1542, 1), (key1658, 1), (key1555, 1), (key1443, 1), (key1420, 1), (key1824, 1), (key1312, 1), (key1816, 1), (key1325, 1), (key1465, 1), (key1387, 1), (key1797, 1), (key1292, 1), (key1779, 1), (key1344, 1), (key1456, 1), (key1392, 1), (key1789, 1), (key1297, 1), (key1773, 1), (key1338, 1)]

def rawRow10998 : Integer.Sparse Key := [(key1623, -2), (key1632, -2), (key1618, -2), (key1816, -2), (key1824, -2), (key1325, -2), (key1443, -2), (key1312, -2), (key1420, -2), (key1814, -2), (key1317, -2), (key1425, -2), (key1658, 1), (key1666, 1), (key1555, 1), (key1592, 1), (key1542, 1), (key1569, 1), (key1816, 1), (key1824, 1), (key1325, 1), (key1443, 1), (key1312, 1), (key1420, 1), (key1779, 1), (key1797, 1), (key1344, 1), (key1465, 1), (key1292, 1), (key1387, 1), (key1773, 1), (key1789, 1), (key1338, 1), (key1456, 1), (key1297, 1), (key1392, 1)]

def rawRow10999 : Integer.Sparse Key := [(key1632, -2), (key1623, -2), (key1618, -2), (key1824, -2), (key1816, -2), (key1443, -2), (key1325, -2), (key1420, -2), (key1312, -2), (key1814, -2), (key1425, -2), (key1317, -2), (key1666, 1), (key1658, 1), (key1592, 1), (key1555, 1), (key1569, 1), (key1542, 1), (key1824, 1), (key1816, 1), (key1443, 1), (key1325, 1), (key1420, 1), (key1312, 1), (key1797, 1), (key1779, 1), (key1465, 1), (key1344, 1), (key1387, 1), (key1292, 1), (key1789, 1), (key1773, 1), (key1456, 1), (key1338, 1), (key1392, 1), (key1297, 1)]

def rawRow11000 : Integer.Sparse Key := [(key1814, -2), (key1816, -2), (key1824, -2), (key1317, -2), (key1325, -2), (key1425, -2), (key1623, -2), (key1443, -2), (key1632, -2), (key1312, -2), (key1420, -2), (key1618, -2), (key1773, 1), (key1779, 1), (key1789, 1), (key1816, 1), (key1797, 1), (key1824, 1), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1), (key1297, 1), (key1325, 1), (key1392, 1), (key1555, 1), (key1443, 1), (key1592, 1), (key1292, 1), (key1312, 1), (key1387, 1), (key1542, 1), (key1420, 1), (key1569, 1)]

def rawRow11001 : Integer.Sparse Key := [(key1816, -2), (key1814, -2), (key1824, -2), (key1325, -2), (key1317, -2), (key1623, -2), (key1425, -2), (key1632, -2), (key1443, -2), (key1312, -2), (key1618, -2), (key1420, -2), (key1779, 1), (key1773, 1), (key1816, 1), (key1789, 1), (key1824, 1), (key1797, 1), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1), (key1325, 1), (key1297, 1), (key1555, 1), (key1392, 1), (key1592, 1), (key1443, 1), (key1312, 1), (key1292, 1), (key1542, 1), (key1387, 1), (key1569, 1), (key1420, 1)]

def rawRow11002 : Integer.Sparse Key := [(key1814, -2), (key1824, -2), (key1816, -2), (key1425, -2), (key1443, -2), (key1317, -2), (key1632, -2), (key1325, -2), (key1623, -2), (key1420, -2), (key1312, -2), (key1618, -2), (key1789, 1), (key1797, 1), (key1773, 1), (key1824, 1), (key1779, 1), (key1816, 1), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1), (key1392, 1), (key1443, 1), (key1297, 1), (key1592, 1), (key1325, 1), (key1555, 1), (key1387, 1), (key1420, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1542, 1)]

def rawRow11003 : Integer.Sparse Key := [(key1824, -2), (key1814, -2), (key1816, -2), (key1443, -2), (key1425, -2), (key1632, -2), (key1317, -2), (key1623, -2), (key1325, -2), (key1420, -2), (key1618, -2), (key1312, -2), (key1797, 1), (key1789, 1), (key1824, 1), (key1773, 1), (key1816, 1), (key1779, 1), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1), (key1443, 1), (key1392, 1), (key1592, 1), (key1297, 1), (key1555, 1), (key1325, 1), (key1420, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1542, 1), (key1312, 1)]

def rawRow11004 : Integer.Sparse Key := [(key1816, -2), (key1824, -2), (key1814, -2), (key1623, -2), (key1632, -2), (key1325, -2), (key1443, -2), (key1317, -2), (key1425, -2), (key1618, -2), (key1312, -2), (key1420, -2), (key1816, 1), (key1824, 1), (key1779, 1), (key1797, 1), (key1773, 1), (key1789, 1), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1), (key1555, 1), (key1592, 1), (key1325, 1), (key1443, 1), (key1297, 1), (key1392, 1), (key1542, 1), (key1569, 1), (key1312, 1), (key1420, 1), (key1292, 1), (key1387, 1)]

def rawRow11005 : Integer.Sparse Key := [(key1824, -2), (key1816, -2), (key1814, -2), (key1632, -2), (key1623, -2), (key1443, -2), (key1325, -2), (key1425, -2), (key1317, -2), (key1618, -2), (key1420, -2), (key1312, -2), (key1824, 1), (key1816, 1), (key1797, 1), (key1779, 1), (key1789, 1), (key1773, 1), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1), (key1592, 1), (key1555, 1), (key1443, 1), (key1325, 1), (key1392, 1), (key1297, 1), (key1569, 1), (key1542, 1), (key1420, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

def rawRow11006 : Integer.Sparse Key := [(key1338, -2), (key1338, -2), (key1344, -2), (key1456, -2), (key1456, -2), (key1656, -2), (key1656, -2), (key1658, -2), (key1658, -2), (key1465, -2), (key1666, -2), (key1666, -2), (key1297, 1), (key1297, 1), (key1317, 1), (key1317, 1), (key1325, 1), (key1325, 1), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1), (key1425, 1), (key1425, 1), (key1574, 1), (key1574, 1), (key1623, 1), (key1623, 1), (key1443, 1), (key1443, 1), (key1592, 1), (key1592, 1), (key1632, 1), (key1632, 1)]

def rawRow11007 : Integer.Sparse Key := [(key1338, -2), (key1344, -2), (key1338, -2), (key1656, -2), (key1658, -2), (key1456, -2), (key1658, -2), (key1456, -2), (key1656, -2), (key1666, -2), (key1465, -2), (key1666, -2), (key1317, 1), (key1325, 1), (key1297, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1574, 1), (key1623, 1), (key1425, 1), (key1623, 1), (key1425, 1), (key1574, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1632, 1), (key1443, 1), (key1592, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11008 : Integer.Sparse Key := [(key1344, -2), (key1338, -2), (key1338, -2), (key1658, -2), (key1656, -2), (key1658, -2), (key1456, -2), (key1656, -2), (key1456, -2), (key1666, -2), (key1666, -2), (key1465, -2), (key1325, 1), (key1317, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1297, 1), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1), (key1623, 1), (key1574, 1), (key1623, 1), (key1425, 1), (key1574, 1), (key1425, 1), (key1632, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1592, 1), (key1443, 1)]

def rawRow11009 : Integer.Sparse Key := [(key1456, -2), (key1456, -2), (key1465, -2), (key1338, -2), (key1338, -2), (key1656, -2), (key1656, -2), (key1666, -2), (key1666, -2), (key1344, -2), (key1658, -2), (key1658, -2), (key1392, 1), (key1392, 1), (key1425, 1), (key1425, 1), (key1443, 1), (key1443, 1), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1), (key1317, 1), (key1317, 1), (key1547, 1), (key1547, 1), (key1632, 1), (key1632, 1), (key1325, 1), (key1325, 1), (key1555, 1), (key1555, 1), (key1623, 1), (key1623, 1)]

def rawRow11010 : Integer.Sparse Key := [(key1456, -2), (key1465, -2), (key1456, -2), (key1656, -2), (key1666, -2), (key1338, -2), (key1666, -2), (key1338, -2), (key1656, -2), (key1658, -2), (key1344, -2), (key1658, -2), (key1425, 1), (key1443, 1), (key1392, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1623, 1), (key1325, 1), (key1555, 1)]

def rawRow11011 : Integer.Sparse Key := [(key1465, -2), (key1456, -2), (key1456, -2), (key1666, -2), (key1656, -2), (key1666, -2), (key1338, -2), (key1656, -2), (key1338, -2), (key1658, -2), (key1658, -2), (key1344, -2), (key1443, 1), (key1425, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1392, 1), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1), (key1632, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1317, 1), (key1623, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1555, 1), (key1325, 1)]

def rawRow11012 : Integer.Sparse Key := [(key1656, -2), (key1658, -2), (key1666, -2), (key1338, -2), (key1344, -2), (key1456, -2), (key1658, -2), (key1465, -2), (key1666, -2), (key1338, -2), (key1456, -2), (key1656, -2), (key1547, 1), (key1555, 1), (key1574, 1), (key1623, 1), (key1592, 1), (key1632, 1), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1), (key1297, 1), (key1325, 1), (key1392, 1), (key1555, 1), (key1443, 1), (key1592, 1), (key1297, 1), (key1317, 1), (key1392, 1), (key1547, 1), (key1425, 1), (key1574, 1)]

def rawRow11013 : Integer.Sparse Key := [(key1658, -2), (key1656, -2), (key1666, -2), (key1344, -2), (key1338, -2), (key1658, -2), (key1456, -2), (key1666, -2), (key1465, -2), (key1338, -2), (key1656, -2), (key1456, -2), (key1555, 1), (key1547, 1), (key1623, 1), (key1574, 1), (key1632, 1), (key1592, 1), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1), (key1325, 1), (key1297, 1), (key1555, 1), (key1392, 1), (key1592, 1), (key1443, 1), (key1317, 1), (key1297, 1), (key1547, 1), (key1392, 1), (key1574, 1), (key1425, 1)]

def rawRow11014 : Integer.Sparse Key := [(key1656, -2), (key1666, -2), (key1658, -2), (key1456, -2), (key1465, -2), (key1338, -2), (key1666, -2), (key1344, -2), (key1658, -2), (key1456, -2), (key1338, -2), (key1656, -2), (key1574, 1), (key1592, 1), (key1547, 1), (key1632, 1), (key1555, 1), (key1623, 1), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1), (key1392, 1), (key1443, 1), (key1297, 1), (key1592, 1), (key1325, 1), (key1555, 1), (key1392, 1), (key1425, 1), (key1297, 1), (key1574, 1), (key1317, 1), (key1547, 1)]

def rawRow11015 : Integer.Sparse Key := [(key1666, -2), (key1656, -2), (key1658, -2), (key1465, -2), (key1456, -2), (key1666, -2), (key1338, -2), (key1658, -2), (key1344, -2), (key1456, -2), (key1656, -2), (key1338, -2), (key1592, 1), (key1574, 1), (key1632, 1), (key1547, 1), (key1623, 1), (key1555, 1), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1), (key1443, 1), (key1392, 1), (key1592, 1), (key1297, 1), (key1555, 1), (key1325, 1), (key1425, 1), (key1392, 1), (key1574, 1), (key1297, 1), (key1547, 1), (key1317, 1)]

def rawRow11016 : Integer.Sparse Key := [(key1658, -2), (key1666, -2), (key1656, -2), (key1658, -2), (key1666, -2), (key1344, -2), (key1465, -2), (key1338, -2), (key1456, -2), (key1656, -2), (key1338, -2), (key1456, -2), (key1623, 1), (key1632, 1), (key1555, 1), (key1592, 1), (key1547, 1), (key1574, 1), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1), (key1555, 1), (key1592, 1), (key1325, 1), (key1443, 1), (key1297, 1), (key1392, 1), (key1547, 1), (key1574, 1), (key1317, 1), (key1425, 1), (key1297, 1), (key1392, 1)]

def rawRow11017 : Integer.Sparse Key := [(key1666, -2), (key1658, -2), (key1656, -2), (key1666, -2), (key1658, -2), (key1465, -2), (key1344, -2), (key1456, -2), (key1338, -2), (key1656, -2), (key1456, -2), (key1338, -2), (key1632, 1), (key1623, 1), (key1592, 1), (key1555, 1), (key1574, 1), (key1547, 1), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1), (key1592, 1), (key1555, 1), (key1443, 1), (key1325, 1), (key1392, 1), (key1297, 1), (key1574, 1), (key1547, 1), (key1425, 1), (key1317, 1), (key1392, 1), (key1297, 1)]

def rawRow11018 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2699, 1), (key2736, 1), (key2802, 1), (key2949, 1), (key2896, 1), (key2975, 1), (key2723, 1), (key2746, 1), (key2826, 1), (key2959, 1), (key2903, 1), (key2982, 1), (key2613, -2), (key2629, -2), (key2647, -2), (key2668, -2), (key2783, -2), (key2937, -2), (key2703, -2), (key2736, -2), (key2806, -2), (key2949, -2), (key2894, -2), (key2973, -2)]

def rawRow11019 : Integer.Sparse Key := [(key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2736, 1), (key2699, 1), (key2949, 1), (key2802, 1), (key2975, 1), (key2896, 1), (key2746, 1), (key2723, 1), (key2959, 1), (key2826, 1), (key2982, 1), (key2903, 1), (key2613, -2), (key2647, -2), (key2629, -2), (key2668, -2), (key2937, -2), (key2783, -2), (key2736, -2), (key2703, -2), (key2949, -2), (key2806, -2), (key2973, -2), (key2894, -2)]

def rawRow11020 : Integer.Sparse Key := [(key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2802, 1), (key2896, 1), (key2699, 1), (key2975, 1), (key2736, 1), (key2949, 1), (key2826, 1), (key2903, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2959, 1), (key2629, -2), (key2613, -2), (key2647, -2), (key2783, -2), (key2668, -2), (key2937, -2), (key2806, -2), (key2894, -2), (key2703, -2), (key2973, -2), (key2736, -2), (key2949, -2)]

def rawRow11021 : Integer.Sparse Key := [(key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2896, 1), (key2802, 1), (key2975, 1), (key2699, 1), (key2949, 1), (key2736, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2959, 1), (key2746, 1), (key2629, -2), (key2647, -2), (key2613, -2), (key2783, -2), (key2937, -2), (key2668, -2), (key2894, -2), (key2806, -2), (key2973, -2), (key2703, -2), (key2949, -2), (key2736, -2)]

def rawRow11022 : Integer.Sparse Key := [(key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2949, 1), (key2975, 1), (key2736, 1), (key2896, 1), (key2699, 1), (key2802, 1), (key2959, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2723, 1), (key2826, 1), (key2647, -2), (key2613, -2), (key2629, -2), (key2937, -2), (key2668, -2), (key2783, -2), (key2949, -2), (key2973, -2), (key2736, -2), (key2894, -2), (key2703, -2), (key2806, -2)]

def rawRow11023 : Integer.Sparse Key := [(key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2975, 1), (key2949, 1), (key2896, 1), (key2736, 1), (key2802, 1), (key2699, 1), (key2982, 1), (key2959, 1), (key2903, 1), (key2746, 1), (key2826, 1), (key2723, 1), (key2647, -2), (key2629, -2), (key2613, -2), (key2937, -2), (key2783, -2), (key2668, -2), (key2973, -2), (key2949, -2), (key2894, -2), (key2736, -2), (key2806, -2), (key2703, -2)]

def rawRow11024 : Integer.Sparse Key := [(key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1), (key2668, -2), (key2703, -2), (key2736, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2629, -2), (key2647, -2), (key2783, -2), (key2937, -2), (key2894, -2), (key2973, -2)]

def rawRow11025 : Integer.Sparse Key := [(key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1), (key2668, -2), (key2736, -2), (key2703, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2647, -2), (key2629, -2), (key2937, -2), (key2783, -2), (key2973, -2), (key2894, -2)]

def rawRow11026 : Integer.Sparse Key := [(key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1), (key2703, -2), (key2668, -2), (key2736, -2), (key2806, -2), (key2613, -2), (key2949, -2), (key2783, -2), (key2894, -2), (key2629, -2), (key2973, -2), (key2647, -2), (key2937, -2)]

def rawRow11027 : Integer.Sparse Key := [(key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1), (key2703, -2), (key2736, -2), (key2668, -2), (key2806, -2), (key2949, -2), (key2613, -2), (key2894, -2), (key2783, -2), (key2973, -2), (key2629, -2), (key2937, -2), (key2647, -2)]

def rawRow11028 : Integer.Sparse Key := [(key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1), (key2736, -2), (key2668, -2), (key2703, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2937, -2), (key2973, -2), (key2647, -2), (key2894, -2), (key2629, -2), (key2783, -2)]

def rawRow11029 : Integer.Sparse Key := [(key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1), (key2736, -2), (key2703, -2), (key2668, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2973, -2), (key2937, -2), (key2894, -2), (key2647, -2), (key2783, -2), (key2629, -2)]

def rawRow11030 : Integer.Sparse Key := [(key2779, 1), (key2791, 1), (key2802, 1), (key2896, 1), (key2826, 1), (key2903, 1), (key2625, 1), (key2637, 1), (key2699, 1), (key2975, 1), (key2723, 1), (key2982, 1), (key2609, 1), (key2652, 1), (key2664, 1), (key2942, 1), (key2746, 1), (key2959, 1), (key2613, 1), (key2647, 1), (key2668, 1), (key2937, 1), (key2736, 1), (key2949, 1), (key2783, -2), (key2806, -2), (key2894, -2), (key2629, -2), (key2703, -2), (key2973, -2), (key2613, -2), (key2647, -2), (key2668, -2), (key2937, -2), (key2736, -2), (key2949, -2)]

def rawRow11031 : Integer.Sparse Key := [(key2791, 1), (key2779, 1), (key2896, 1), (key2802, 1), (key2903, 1), (key2826, 1), (key2637, 1), (key2625, 1), (key2975, 1), (key2699, 1), (key2982, 1), (key2723, 1), (key2652, 1), (key2609, 1), (key2942, 1), (key2664, 1), (key2959, 1), (key2746, 1), (key2647, 1), (key2613, 1), (key2937, 1), (key2668, 1), (key2949, 1), (key2736, 1), (key2783, -2), (key2894, -2), (key2806, -2), (key2629, -2), (key2973, -2), (key2703, -2), (key2647, -2), (key2613, -2), (key2937, -2), (key2668, -2), (key2949, -2), (key2736, -2)]

def rawRow11032 : Integer.Sparse Key := [(key2802, 1), (key2826, 1), (key2779, 1), (key2903, 1), (key2791, 1), (key2896, 1), (key2699, 1), (key2723, 1), (key2625, 1), (key2982, 1), (key2637, 1), (key2975, 1), (key2664, 1), (key2746, 1), (key2609, 1), (key2959, 1), (key2652, 1), (key2942, 1), (key2668, 1), (key2736, 1), (key2613, 1), (key2949, 1), (key2647, 1), (key2937, 1), (key2806, -2), (key2783, -2), (key2894, -2), (key2703, -2), (key2629, -2), (key2973, -2), (key2668, -2), (key2736, -2), (key2613, -2), (key2949, -2), (key2647, -2), (key2937, -2)]

def rawRow11033 : Integer.Sparse Key := [(key2826, 1), (key2802, 1), (key2903, 1), (key2779, 1), (key2896, 1), (key2791, 1), (key2723, 1), (key2699, 1), (key2982, 1), (key2625, 1), (key2975, 1), (key2637, 1), (key2746, 1), (key2664, 1), (key2959, 1), (key2609, 1), (key2942, 1), (key2652, 1), (key2736, 1), (key2668, 1), (key2949, 1), (key2613, 1), (key2937, 1), (key2647, 1), (key2806, -2), (key2894, -2), (key2783, -2), (key2703, -2), (key2973, -2), (key2629, -2), (key2736, -2), (key2668, -2), (key2949, -2), (key2613, -2), (key2937, -2), (key2647, -2)]

def rawRow11034 : Integer.Sparse Key := [(key2896, 1), (key2903, 1), (key2791, 1), (key2826, 1), (key2779, 1), (key2802, 1), (key2975, 1), (key2982, 1), (key2637, 1), (key2723, 1), (key2625, 1), (key2699, 1), (key2942, 1), (key2959, 1), (key2652, 1), (key2746, 1), (key2609, 1), (key2664, 1), (key2937, 1), (key2949, 1), (key2647, 1), (key2736, 1), (key2613, 1), (key2668, 1), (key2894, -2), (key2783, -2), (key2806, -2), (key2973, -2), (key2629, -2), (key2703, -2), (key2937, -2), (key2949, -2), (key2647, -2), (key2736, -2), (key2613, -2), (key2668, -2)]

def rawRow11035 : Integer.Sparse Key := [(key2903, 1), (key2896, 1), (key2826, 1), (key2791, 1), (key2802, 1), (key2779, 1), (key2982, 1), (key2975, 1), (key2723, 1), (key2637, 1), (key2699, 1), (key2625, 1), (key2959, 1), (key2942, 1), (key2746, 1), (key2652, 1), (key2664, 1), (key2609, 1), (key2949, 1), (key2937, 1), (key2736, 1), (key2647, 1), (key2668, 1), (key2613, 1), (key2894, -2), (key2806, -2), (key2783, -2), (key2973, -2), (key2703, -2), (key2629, -2), (key2949, -2), (key2937, -2), (key2736, -2), (key2647, -2), (key2668, -2), (key2613, -2)]

def rawRow11036 : Integer.Sparse Key := [(key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1), (key2937, -2), (key2949, -2), (key2973, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2613, -2), (key2629, -2), (key2668, -2), (key2783, -2), (key2703, -2), (key2806, -2)]

def rawRow11037 : Integer.Sparse Key := [(key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1), (key2937, -2), (key2973, -2), (key2949, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2629, -2), (key2613, -2), (key2783, -2), (key2668, -2), (key2806, -2), (key2703, -2)]

def rawRow11038 : Integer.Sparse Key := [(key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1), (key2949, -2), (key2937, -2), (key2973, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2668, -2), (key2703, -2), (key2613, -2), (key2806, -2), (key2629, -2), (key2783, -2)]

def rawRow11039 : Integer.Sparse Key := [(key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1), (key2949, -2), (key2973, -2), (key2937, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2703, -2), (key2668, -2), (key2806, -2), (key2613, -2), (key2783, -2), (key2629, -2)]

def rawRow11040 : Integer.Sparse Key := [(key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1), (key2973, -2), (key2937, -2), (key2949, -2), (key2894, -2), (key2647, -2), (key2736, -2), (key2783, -2), (key2806, -2), (key2629, -2), (key2703, -2), (key2613, -2), (key2668, -2)]

def rawRow11041 : Integer.Sparse Key := [(key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1), (key2973, -2), (key2949, -2), (key2937, -2), (key2894, -2), (key2736, -2), (key2647, -2), (key2806, -2), (key2783, -2), (key2703, -2), (key2629, -2), (key2668, -2), (key2613, -2)]

def rawRow11042 : Integer.Sparse Key := [(key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2703, 1), (key2703, 1), (key2806, 1), (key2806, 1), (key2857, 1), (key2857, 1), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1), (key2609, -2), (key2625, -2), (key2625, -2), (key2664, -2), (key2779, -2), (key2779, -2), (key2699, -2), (key2699, -2), (key2802, -2), (key2802, -2), (key2852, -2), (key2852, -2)]

def rawRow11043 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2625, -2), (key2609, -2), (key2625, -2), (key2779, -2), (key2664, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2699, -2), (key2852, -2), (key2699, -2), (key2802, -2)]

def rawRow11044 : Integer.Sparse Key := [(key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2857, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2703, 1), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1), (key2625, -2), (key2625, -2), (key2609, -2), (key2779, -2), (key2779, -2), (key2664, -2), (key2852, -2), (key2802, -2), (key2852, -2), (key2699, -2), (key2802, -2), (key2699, -2)]

def rawRow11045 : Integer.Sparse Key := [(key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1), (key2664, -2), (key2699, -2), (key2699, -2), (key2609, -2), (key2802, -2), (key2802, -2), (key2625, -2), (key2625, -2), (key2779, -2), (key2779, -2), (key2852, -2), (key2852, -2)]

def rawRow11046 : Integer.Sparse Key := [(key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2699, -2), (key2664, -2), (key2699, -2), (key2802, -2), (key2609, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2625, -2), (key2852, -2), (key2625, -2), (key2779, -2)]

def rawRow11047 : Integer.Sparse Key := [(key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1), (key2699, -2), (key2699, -2), (key2664, -2), (key2802, -2), (key2802, -2), (key2609, -2), (key2852, -2), (key2779, -2), (key2852, -2), (key2625, -2), (key2779, -2), (key2625, -2)]

def rawRow11048 : Integer.Sparse Key := [(key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1), (key2779, -2), (key2802, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2852, -2), (key2609, -2), (key2625, -2), (key2664, -2), (key2779, -2), (key2699, -2), (key2802, -2)]

def rawRow11049 : Integer.Sparse Key := [(key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1), (key2779, -2), (key2852, -2), (key2802, -2), (key2625, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2609, -2), (key2779, -2), (key2664, -2), (key2802, -2), (key2699, -2)]

def rawRow11050 : Integer.Sparse Key := [(key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1), (key2802, -2), (key2779, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2852, -2), (key2664, -2), (key2699, -2), (key2609, -2), (key2802, -2), (key2625, -2), (key2779, -2)]

def rawRow11051 : Integer.Sparse Key := [(key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1), (key2802, -2), (key2852, -2), (key2779, -2), (key2699, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2664, -2), (key2802, -2), (key2609, -2), (key2779, -2), (key2625, -2)]

def rawRow11052 : Integer.Sparse Key := [(key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1), (key2852, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2779, -2), (key2802, -2), (key2625, -2), (key2699, -2), (key2609, -2), (key2664, -2)]

def rawRow11053 : Integer.Sparse Key := [(key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1), (key2852, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2802, -2), (key2779, -2), (key2699, -2), (key2625, -2), (key2664, -2), (key2609, -2)]

def rawRow11115 : Integer.Sparse Key := [(key2534, 6), (key2540, 6), (key2534, 6), (key2551, 6), (key2370, -6), (key2839, -6), (key2762, -6), (key2839, -6)]

def rawRow11116 : Integer.Sparse Key := [(key2540, 6), (key2534, 6), (key2534, 6), (key2551, 6), (key2370, -6), (key2839, -6), (key2839, -6), (key2762, -6)]

def rawRow11117 : Integer.Sparse Key := [(key2534, 6), (key2534, 6), (key2551, 6), (key2540, 6), (key2398, -6), (key2583, -6), (key2839, -6), (key2839, -6)]

def rawRow11118 : Integer.Sparse Key := [(key2534, 6), (key2551, 6), (key2534, 6), (key2540, 6), (key2398, -6), (key2839, -6), (key2583, -6), (key2839, -6)]

def rawRow11119 : Integer.Sparse Key := [(key2551, 6), (key2534, 6), (key2534, 6), (key2540, 6), (key2398, -6), (key2839, -6), (key2839, -6), (key2583, -6)]

def rawRow11120 : Integer.Sparse Key := [(key2534, 6), (key2540, 6), (key2551, 6), (key2534, 6), (key2464, -6), (key2370, -6), (key2762, -6), (key2839, -6)]

def rawRow11121 : Integer.Sparse Key := [(key2540, 6), (key2534, 6), (key2551, 6), (key2534, 6), (key2464, -6), (key2370, -6), (key2839, -6), (key2762, -6)]

def rawRow11122 : Integer.Sparse Key := [(key2534, 6), (key2551, 6), (key2540, 6), (key2534, 6), (key2464, -6), (key2398, -6), (key2583, -6), (key2839, -6)]

def rawRow11123 : Integer.Sparse Key := [(key2551, 6), (key2534, 6), (key2540, 6), (key2534, 6), (key2464, -6), (key2398, -6), (key2839, -6), (key2583, -6)]

def rawRow11124 : Integer.Sparse Key := [(key2540, 6), (key2551, 6), (key2534, 6), (key2534, 6), (key2464, -6), (key2464, -6), (key2370, -6), (key2762, -6)]

def rawRow11125 : Integer.Sparse Key := [(key2551, 6), (key2540, 6), (key2534, 6), (key2534, 6), (key2464, -6), (key2464, -6), (key2398, -6), (key2583, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11150 : Integer.Sparse Key := [(key2536, 6), (key2536, 6), (key2541, 6), (key2552, 6), (key2371, -6), (key2399, -6), (key2465, -6), (key2465, -6)]

def rawRow11151 : Integer.Sparse Key := [(key2536, 6), (key2541, 6), (key2536, 6), (key2552, 6), (key2371, -6), (key2465, -6), (key2399, -6), (key2465, -6)]

def rawRow11152 : Integer.Sparse Key := [(key2541, 6), (key2536, 6), (key2536, 6), (key2552, 6), (key2371, -6), (key2465, -6), (key2465, -6), (key2399, -6)]

def rawRow11153 : Integer.Sparse Key := [(key2536, 6), (key2536, 6), (key2552, 6), (key2541, 6), (key2399, -6), (key2371, -6), (key2465, -6), (key2465, -6)]

def rawRow11154 : Integer.Sparse Key := [(key2536, 6), (key2552, 6), (key2536, 6), (key2541, 6), (key2399, -6), (key2465, -6), (key2371, -6), (key2465, -6)]

def rawRow11155 : Integer.Sparse Key := [(key2552, 6), (key2536, 6), (key2536, 6), (key2541, 6), (key2399, -6), (key2465, -6), (key2465, -6), (key2371, -6)]

def rawRow11156 : Integer.Sparse Key := [(key2536, 6), (key2541, 6), (key2552, 6), (key2536, 6), (key2465, -6), (key2371, -6), (key2399, -6), (key2465, -6)]

def rawRow11157 : Integer.Sparse Key := [(key2541, 6), (key2536, 6), (key2552, 6), (key2536, 6), (key2465, -6), (key2371, -6), (key2465, -6), (key2399, -6)]

def rawRow11158 : Integer.Sparse Key := [(key2536, 6), (key2552, 6), (key2541, 6), (key2536, 6), (key2465, -6), (key2399, -6), (key2371, -6), (key2465, -6)]

def rawRow11159 : Integer.Sparse Key := [(key2552, 6), (key2536, 6), (key2541, 6), (key2536, 6), (key2465, -6), (key2399, -6), (key2465, -6), (key2371, -6)]

def rawRow11160 : Integer.Sparse Key := [(key2541, 6), (key2552, 6), (key2536, 6), (key2536, 6), (key2465, -6), (key2465, -6), (key2371, -6), (key2399, -6)]

def rawRow11161 : Integer.Sparse Key := [(key2552, 6), (key2541, 6), (key2536, 6), (key2536, 6), (key2465, -6), (key2465, -6), (key2399, -6), (key2371, -6)]

def rawRow11222 : Integer.Sparse Key := [(key1191, 6), (key1191, 6), (key1197, 6), (key1210, 6), (key994, -6), (key1029, -6), (key1107, -6), (key1107, -6)]

def rawRow11223 : Integer.Sparse Key := [(key1191, 6), (key1197, 6), (key1191, 6), (key1210, 6), (key994, -6), (key1107, -6), (key1029, -6), (key1107, -6)]

def rawRow11224 : Integer.Sparse Key := [(key1197, 6), (key1191, 6), (key1191, 6), (key1210, 6), (key994, -6), (key1107, -6), (key1107, -6), (key1029, -6)]

def rawRow11225 : Integer.Sparse Key := [(key1191, 6), (key1191, 6), (key1210, 6), (key1197, 6), (key1029, -6), (key994, -6), (key1107, -6), (key1107, -6)]

def rawRow11226 : Integer.Sparse Key := [(key1191, 6), (key1210, 6), (key1191, 6), (key1197, 6), (key1029, -6), (key1107, -6), (key994, -6), (key1107, -6)]

def rawRow11227 : Integer.Sparse Key := [(key1210, 6), (key1191, 6), (key1191, 6), (key1197, 6), (key1029, -6), (key1107, -6), (key1107, -6), (key994, -6)]

def rawRow11228 : Integer.Sparse Key := [(key1191, 6), (key1197, 6), (key1210, 6), (key1191, 6), (key1107, -6), (key994, -6), (key1029, -6), (key1107, -6)]

def rawRow11229 : Integer.Sparse Key := [(key1197, 6), (key1191, 6), (key1210, 6), (key1191, 6), (key1107, -6), (key994, -6), (key1107, -6), (key1029, -6)]

def rawRow11230 : Integer.Sparse Key := [(key1191, 6), (key1210, 6), (key1197, 6), (key1191, 6), (key1107, -6), (key1029, -6), (key994, -6), (key1107, -6)]

def rawRow11231 : Integer.Sparse Key := [(key1210, 6), (key1191, 6), (key1197, 6), (key1191, 6), (key1107, -6), (key1029, -6), (key1107, -6), (key994, -6)]

def rawRow11232 : Integer.Sparse Key := [(key1197, 6), (key1210, 6), (key1191, 6), (key1191, 6), (key1107, -6), (key1107, -6), (key994, -6), (key1029, -6)]

def rawRow11233 : Integer.Sparse Key := [(key1210, 6), (key1197, 6), (key1191, 6), (key1191, 6), (key1107, -6), (key1107, -6), (key1029, -6), (key994, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11294 : Integer.Sparse Key := [(key2720, -6), (key2823, -6), (key2864, -6), (key2864, -6), (key2634, 6), (key2788, 6), (key2854, 6), (key2854, 6)]

def rawRow11295 : Integer.Sparse Key := [(key2720, -6), (key2864, -6), (key2823, -6), (key2864, -6), (key2634, 6), (key2854, 6), (key2788, 6), (key2854, 6)]

def rawRow11296 : Integer.Sparse Key := [(key2720, -6), (key2864, -6), (key2864, -6), (key2823, -6), (key2634, 6), (key2854, 6), (key2854, 6), (key2788, 6)]

def rawRow11297 : Integer.Sparse Key := [(key2823, -6), (key2720, -6), (key2864, -6), (key2864, -6), (key2788, 6), (key2634, 6), (key2854, 6), (key2854, 6)]

def rawRow11298 : Integer.Sparse Key := [(key2823, -6), (key2864, -6), (key2720, -6), (key2864, -6), (key2788, 6), (key2854, 6), (key2634, 6), (key2854, 6)]

def rawRow11299 : Integer.Sparse Key := [(key2823, -6), (key2864, -6), (key2864, -6), (key2720, -6), (key2788, 6), (key2854, 6), (key2854, 6), (key2634, 6)]

def rawRow11300 : Integer.Sparse Key := [(key2864, -6), (key2720, -6), (key2823, -6), (key2864, -6), (key2854, 6), (key2634, 6), (key2788, 6), (key2854, 6)]

def rawRow11301 : Integer.Sparse Key := [(key2864, -6), (key2720, -6), (key2864, -6), (key2823, -6), (key2854, 6), (key2634, 6), (key2854, 6), (key2788, 6)]

def rawRow11302 : Integer.Sparse Key := [(key2864, -6), (key2823, -6), (key2720, -6), (key2864, -6), (key2854, 6), (key2788, 6), (key2634, 6), (key2854, 6)]

def rawRow11303 : Integer.Sparse Key := [(key2864, -6), (key2823, -6), (key2864, -6), (key2720, -6), (key2854, 6), (key2788, 6), (key2854, 6), (key2634, 6)]

def rawRow11304 : Integer.Sparse Key := [(key2864, -6), (key2864, -6), (key2720, -6), (key2823, -6), (key2854, 6), (key2854, 6), (key2634, 6), (key2788, 6)]

def rawRow11305 : Integer.Sparse Key := [(key2864, -6), (key2864, -6), (key2823, -6), (key2720, -6), (key2854, 6), (key2854, 6), (key2788, 6), (key2634, 6)]

def rawRow11306 : Integer.Sparse Key := [(key2632, -2), (key2640, -2), (key2642, -2), (key2706, -2), (key2860, -2), (key2977, -2), (key2726, -2), (key2729, -2), (key2870, -2), (key2984, -2), (key2883, -2), (key2992, -2), (key2616, 2), (key2640, 2), (key2654, 2), (key2671, 2), (key2794, 2), (key2944, 2), (key2726, 2), (key2748, 2), (key2829, 2), (key2961, 2), (key2913, 2), (key2992, 2)]

def rawRow11307 : Integer.Sparse Key := [(key2632, -2), (key2642, -2), (key2640, -2), (key2706, -2), (key2977, -2), (key2860, -2), (key2729, -2), (key2726, -2), (key2984, -2), (key2870, -2), (key2992, -2), (key2883, -2), (key2616, 2), (key2654, 2), (key2640, 2), (key2671, 2), (key2944, 2), (key2794, 2), (key2748, 2), (key2726, 2), (key2961, 2), (key2829, 2), (key2992, 2), (key2913, 2)]

def rawRow11308 : Integer.Sparse Key := [(key2640, -2), (key2632, -2), (key2642, -2), (key2860, -2), (key2706, -2), (key2977, -2), (key2870, -2), (key2883, -2), (key2726, -2), (key2992, -2), (key2729, -2), (key2984, -2), (key2640, 2), (key2616, 2), (key2654, 2), (key2794, 2), (key2671, 2), (key2944, 2), (key2829, 2), (key2913, 2), (key2726, 2), (key2992, 2), (key2748, 2), (key2961, 2)]

def rawRow11309 : Integer.Sparse Key := [(key2640, -2), (key2642, -2), (key2632, -2), (key2860, -2), (key2977, -2), (key2706, -2), (key2883, -2), (key2870, -2), (key2992, -2), (key2726, -2), (key2984, -2), (key2729, -2), (key2640, 2), (key2654, 2), (key2616, 2), (key2794, 2), (key2944, 2), (key2671, 2), (key2913, 2), (key2829, 2), (key2992, 2), (key2726, 2), (key2961, 2), (key2748, 2)]

def rawRow11310 : Integer.Sparse Key := [(key2642, -2), (key2632, -2), (key2640, -2), (key2977, -2), (key2706, -2), (key2860, -2), (key2984, -2), (key2992, -2), (key2729, -2), (key2883, -2), (key2726, -2), (key2870, -2), (key2654, 2), (key2616, 2), (key2640, 2), (key2944, 2), (key2671, 2), (key2794, 2), (key2961, 2), (key2992, 2), (key2748, 2), (key2913, 2), (key2726, 2), (key2829, 2)]

def rawRow11311 : Integer.Sparse Key := [(key2642, -2), (key2640, -2), (key2632, -2), (key2977, -2), (key2860, -2), (key2706, -2), (key2992, -2), (key2984, -2), (key2883, -2), (key2729, -2), (key2870, -2), (key2726, -2), (key2654, 2), (key2640, 2), (key2616, 2), (key2944, 2), (key2794, 2), (key2671, 2), (key2992, 2), (key2961, 2), (key2913, 2), (key2748, 2), (key2829, 2), (key2726, 2)]

def rawRow11312 : Integer.Sparse Key := [(key2706, -2), (key2726, -2), (key2729, -2), (key2632, -2), (key2870, -2), (key2984, -2), (key2640, -2), (key2642, -2), (key2860, -2), (key2977, -2), (key2883, -2), (key2992, -2), (key2671, 2), (key2726, 2), (key2748, 2), (key2616, 2), (key2829, 2), (key2961, 2), (key2640, 2), (key2654, 2), (key2794, 2), (key2944, 2), (key2913, 2), (key2992, 2)]

def rawRow11313 : Integer.Sparse Key := [(key2706, -2), (key2729, -2), (key2726, -2), (key2632, -2), (key2984, -2), (key2870, -2), (key2642, -2), (key2640, -2), (key2977, -2), (key2860, -2), (key2992, -2), (key2883, -2), (key2671, 2), (key2748, 2), (key2726, 2), (key2616, 2), (key2961, 2), (key2829, 2), (key2654, 2), (key2640, 2), (key2944, 2), (key2794, 2), (key2992, 2), (key2913, 2)]

def rawRow11314 : Integer.Sparse Key := [(key2726, -2), (key2706, -2), (key2729, -2), (key2870, -2), (key2632, -2), (key2984, -2), (key2860, -2), (key2883, -2), (key2640, -2), (key2992, -2), (key2642, -2), (key2977, -2), (key2726, 2), (key2671, 2), (key2748, 2), (key2829, 2), (key2616, 2), (key2961, 2), (key2794, 2), (key2913, 2), (key2640, 2), (key2992, 2), (key2654, 2), (key2944, 2)]

def rawRow11315 : Integer.Sparse Key := [(key2726, -2), (key2729, -2), (key2706, -2), (key2870, -2), (key2984, -2), (key2632, -2), (key2883, -2), (key2860, -2), (key2992, -2), (key2640, -2), (key2977, -2), (key2642, -2), (key2726, 2), (key2748, 2), (key2671, 2), (key2829, 2), (key2961, 2), (key2616, 2), (key2913, 2), (key2794, 2), (key2992, 2), (key2640, 2), (key2944, 2), (key2654, 2)]

def rawRow11316 : Integer.Sparse Key := [(key2729, -2), (key2706, -2), (key2726, -2), (key2984, -2), (key2632, -2), (key2870, -2), (key2977, -2), (key2992, -2), (key2642, -2), (key2883, -2), (key2640, -2), (key2860, -2), (key2748, 2), (key2671, 2), (key2726, 2), (key2961, 2), (key2616, 2), (key2829, 2), (key2944, 2), (key2992, 2), (key2654, 2), (key2913, 2), (key2640, 2), (key2794, 2)]

def rawRow11317 : Integer.Sparse Key := [(key2729, -2), (key2726, -2), (key2706, -2), (key2984, -2), (key2870, -2), (key2632, -2), (key2992, -2), (key2977, -2), (key2883, -2), (key2642, -2), (key2860, -2), (key2640, -2), (key2748, 2), (key2726, 2), (key2671, 2), (key2961, 2), (key2829, 2), (key2616, 2), (key2992, 2), (key2944, 2), (key2913, 2), (key2654, 2), (key2794, 2), (key2640, 2)]

def rawRow11318 : Integer.Sparse Key := [(key2860, -2), (key2870, -2), (key2883, -2), (key2640, -2), (key2726, -2), (key2992, -2), (key2632, -2), (key2642, -2), (key2706, -2), (key2977, -2), (key2729, -2), (key2984, -2), (key2794, 2), (key2829, 2), (key2913, 2), (key2640, 2), (key2726, 2), (key2992, 2), (key2616, 2), (key2654, 2), (key2671, 2), (key2944, 2), (key2748, 2), (key2961, 2)]

def rawRow11319 : Integer.Sparse Key := [(key2860, -2), (key2883, -2), (key2870, -2), (key2640, -2), (key2992, -2), (key2726, -2), (key2642, -2), (key2632, -2), (key2977, -2), (key2706, -2), (key2984, -2), (key2729, -2), (key2794, 2), (key2913, 2), (key2829, 2), (key2640, 2), (key2992, 2), (key2726, 2), (key2654, 2), (key2616, 2), (key2944, 2), (key2671, 2), (key2961, 2), (key2748, 2)]

def rawRow11320 : Integer.Sparse Key := [(key2870, -2), (key2860, -2), (key2883, -2), (key2726, -2), (key2640, -2), (key2992, -2), (key2706, -2), (key2729, -2), (key2632, -2), (key2984, -2), (key2642, -2), (key2977, -2), (key2829, 2), (key2794, 2), (key2913, 2), (key2726, 2), (key2640, 2), (key2992, 2), (key2671, 2), (key2748, 2), (key2616, 2), (key2961, 2), (key2654, 2), (key2944, 2)]

def rawRow11321 : Integer.Sparse Key := [(key2870, -2), (key2883, -2), (key2860, -2), (key2726, -2), (key2992, -2), (key2640, -2), (key2729, -2), (key2706, -2), (key2984, -2), (key2632, -2), (key2977, -2), (key2642, -2), (key2829, 2), (key2913, 2), (key2794, 2), (key2726, 2), (key2992, 2), (key2640, 2), (key2748, 2), (key2671, 2), (key2961, 2), (key2616, 2), (key2944, 2), (key2654, 2)]

def rawRow11322 : Integer.Sparse Key := [(key2883, -2), (key2860, -2), (key2870, -2), (key2992, -2), (key2640, -2), (key2726, -2), (key2977, -2), (key2984, -2), (key2642, -2), (key2729, -2), (key2632, -2), (key2706, -2), (key2913, 2), (key2794, 2), (key2829, 2), (key2992, 2), (key2640, 2), (key2726, 2), (key2944, 2), (key2961, 2), (key2654, 2), (key2748, 2), (key2616, 2), (key2671, 2)]

def rawRow11323 : Integer.Sparse Key := [(key2883, -2), (key2870, -2), (key2860, -2), (key2992, -2), (key2726, -2), (key2640, -2), (key2984, -2), (key2977, -2), (key2729, -2), (key2642, -2), (key2706, -2), (key2632, -2), (key2913, 2), (key2829, 2), (key2794, 2), (key2992, 2), (key2726, 2), (key2640, 2), (key2961, 2), (key2944, 2), (key2748, 2), (key2654, 2), (key2671, 2), (key2616, 2)]

def rawRow11324 : Integer.Sparse Key := [(key2977, -2), (key2984, -2), (key2992, -2), (key2642, -2), (key2729, -2), (key2883, -2), (key2632, -2), (key2640, -2), (key2706, -2), (key2860, -2), (key2726, -2), (key2870, -2), (key2944, 2), (key2961, 2), (key2992, 2), (key2654, 2), (key2748, 2), (key2913, 2), (key2616, 2), (key2640, 2), (key2671, 2), (key2794, 2), (key2726, 2), (key2829, 2)]

def rawRow11325 : Integer.Sparse Key := [(key2977, -2), (key2992, -2), (key2984, -2), (key2642, -2), (key2883, -2), (key2729, -2), (key2640, -2), (key2632, -2), (key2860, -2), (key2706, -2), (key2870, -2), (key2726, -2), (key2944, 2), (key2992, 2), (key2961, 2), (key2654, 2), (key2913, 2), (key2748, 2), (key2640, 2), (key2616, 2), (key2794, 2), (key2671, 2), (key2829, 2), (key2726, 2)]

def rawRow11326 : Integer.Sparse Key := [(key2984, -2), (key2977, -2), (key2992, -2), (key2729, -2), (key2642, -2), (key2883, -2), (key2706, -2), (key2726, -2), (key2632, -2), (key2870, -2), (key2640, -2), (key2860, -2), (key2961, 2), (key2944, 2), (key2992, 2), (key2748, 2), (key2654, 2), (key2913, 2), (key2671, 2), (key2726, 2), (key2616, 2), (key2829, 2), (key2640, 2), (key2794, 2)]

def rawRow11327 : Integer.Sparse Key := [(key2984, -2), (key2992, -2), (key2977, -2), (key2729, -2), (key2883, -2), (key2642, -2), (key2726, -2), (key2706, -2), (key2870, -2), (key2632, -2), (key2860, -2), (key2640, -2), (key2961, 2), (key2992, 2), (key2944, 2), (key2748, 2), (key2913, 2), (key2654, 2), (key2726, 2), (key2671, 2), (key2829, 2), (key2616, 2), (key2794, 2), (key2640, 2)]

def rawRow11328 : Integer.Sparse Key := [(key2992, -2), (key2977, -2), (key2984, -2), (key2883, -2), (key2642, -2), (key2729, -2), (key2860, -2), (key2870, -2), (key2640, -2), (key2726, -2), (key2632, -2), (key2706, -2), (key2992, 2), (key2944, 2), (key2961, 2), (key2913, 2), (key2654, 2), (key2748, 2), (key2794, 2), (key2829, 2), (key2640, 2), (key2726, 2), (key2616, 2), (key2671, 2)]

def rawRow11329 : Integer.Sparse Key := [(key2992, -2), (key2984, -2), (key2977, -2), (key2883, -2), (key2729, -2), (key2642, -2), (key2870, -2), (key2860, -2), (key2726, -2), (key2640, -2), (key2706, -2), (key2632, -2), (key2992, 2), (key2961, 2), (key2944, 2), (key2913, 2), (key2748, 2), (key2654, 2), (key2829, 2), (key2794, 2), (key2726, 2), (key2640, 2), (key2671, 2), (key2616, 2)]

def rawRow11330 : Integer.Sparse Key := [(key2649, -2), (key2654, -2), (key2654, -2), (key2738, -2), (key2898, -2), (key2898, -2), (key2748, -2), (key2748, -2), (key2905, -2), (key2905, -2), (key2913, -2), (key2913, -2), (key2619, 2), (key2642, 2), (key2642, 2), (key2674, 2), (key2796, 2), (key2796, 2), (key2729, 2), (key2729, 2), (key2832, 2), (key2832, 2), (key2883, 2), (key2883, 2)]

def rawRow11331 : Integer.Sparse Key := [(key2654, -2), (key2649, -2), (key2654, -2), (key2898, -2), (key2738, -2), (key2898, -2), (key2905, -2), (key2913, -2), (key2748, -2), (key2913, -2), (key2748, -2), (key2905, -2), (key2642, 2), (key2619, 2), (key2642, 2), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, 2), (key2883, 2), (key2729, 2), (key2883, 2), (key2729, 2), (key2832, 2)]

def rawRow11332 : Integer.Sparse Key := [(key2654, -2), (key2654, -2), (key2649, -2), (key2898, -2), (key2898, -2), (key2738, -2), (key2913, -2), (key2905, -2), (key2913, -2), (key2748, -2), (key2905, -2), (key2748, -2), (key2642, 2), (key2642, 2), (key2619, 2), (key2796, 2), (key2796, 2), (key2674, 2), (key2883, 2), (key2832, 2), (key2883, 2), (key2729, 2), (key2832, 2), (key2729, 2)]

def rawRow11333 : Integer.Sparse Key := [(key2738, -2), (key2748, -2), (key2748, -2), (key2649, -2), (key2905, -2), (key2905, -2), (key2654, -2), (key2654, -2), (key2898, -2), (key2898, -2), (key2913, -2), (key2913, -2), (key2674, 2), (key2729, 2), (key2729, 2), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, 2), (key2642, 2), (key2796, 2), (key2796, 2), (key2883, 2), (key2883, 2)]

def rawRow11334 : Integer.Sparse Key := [(key2748, -2), (key2738, -2), (key2748, -2), (key2905, -2), (key2649, -2), (key2905, -2), (key2898, -2), (key2913, -2), (key2654, -2), (key2913, -2), (key2654, -2), (key2898, -2), (key2729, 2), (key2674, 2), (key2729, 2), (key2832, 2), (key2619, 2), (key2832, 2), (key2796, 2), (key2883, 2), (key2642, 2), (key2883, 2), (key2642, 2), (key2796, 2)]

def rawRow11335 : Integer.Sparse Key := [(key2748, -2), (key2748, -2), (key2738, -2), (key2905, -2), (key2905, -2), (key2649, -2), (key2913, -2), (key2898, -2), (key2913, -2), (key2654, -2), (key2898, -2), (key2654, -2), (key2729, 2), (key2729, 2), (key2674, 2), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, 2), (key2796, 2), (key2883, 2), (key2642, 2), (key2796, 2), (key2642, 2)]

def rawRow11336 : Integer.Sparse Key := [(key2898, -2), (key2905, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2913, -2), (key2649, -2), (key2654, -2), (key2738, -2), (key2898, -2), (key2748, -2), (key2905, -2), (key2796, 2), (key2832, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2883, 2), (key2619, 2), (key2642, 2), (key2674, 2), (key2796, 2), (key2729, 2), (key2832, 2)]

def rawRow11337 : Integer.Sparse Key := [(key2898, -2), (key2913, -2), (key2905, -2), (key2654, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2649, -2), (key2898, -2), (key2738, -2), (key2905, -2), (key2748, -2), (key2796, 2), (key2883, 2), (key2832, 2), (key2642, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2619, 2), (key2796, 2), (key2674, 2), (key2832, 2), (key2729, 2)]

def rawRow11338 : Integer.Sparse Key := [(key2905, -2), (key2898, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2913, -2), (key2738, -2), (key2748, -2), (key2649, -2), (key2905, -2), (key2654, -2), (key2898, -2), (key2832, 2), (key2796, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2883, 2), (key2674, 2), (key2729, 2), (key2619, 2), (key2832, 2), (key2642, 2), (key2796, 2)]

def rawRow11339 : Integer.Sparse Key := [(key2905, -2), (key2913, -2), (key2898, -2), (key2748, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2738, -2), (key2905, -2), (key2649, -2), (key2898, -2), (key2654, -2), (key2832, 2), (key2883, 2), (key2796, 2), (key2729, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2674, 2), (key2832, 2), (key2619, 2), (key2796, 2), (key2642, 2)]

def rawRow11340 : Integer.Sparse Key := [(key2913, -2), (key2898, -2), (key2905, -2), (key2913, -2), (key2654, -2), (key2748, -2), (key2898, -2), (key2905, -2), (key2654, -2), (key2748, -2), (key2649, -2), (key2738, -2), (key2883, 2), (key2796, 2), (key2832, 2), (key2883, 2), (key2642, 2), (key2729, 2), (key2796, 2), (key2832, 2), (key2642, 2), (key2729, 2), (key2619, 2), (key2674, 2)]

def rawRow11341 : Integer.Sparse Key := [(key2913, -2), (key2905, -2), (key2898, -2), (key2913, -2), (key2748, -2), (key2654, -2), (key2905, -2), (key2898, -2), (key2748, -2), (key2654, -2), (key2738, -2), (key2649, -2), (key2883, 2), (key2832, 2), (key2796, 2), (key2883, 2), (key2729, 2), (key2642, 2), (key2832, 2), (key2796, 2), (key2729, 2), (key2642, 2), (key2674, 2), (key2619, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11450 : Integer.Sparse Key := [(key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1), (key2611, -2), (key2627, -2), (key2636, -2), (key2666, -2), (key2701, -2), (key2722, -2), (key2781, -2), (key2790, -2), (key2804, -2), (key2825, -2), (key2856, -2), (key2866, -2)]

def rawRow11451 : Integer.Sparse Key := [(key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2790, 1), (key2778, 1), (key2825, 1), (key2801, 1), (key2902, 1), (key2895, 1), (key2941, 1), (key2935, 1), (key2958, 1), (key2947, 1), (key2981, 1), (key2974, 1), (key2611, -2), (key2636, -2), (key2627, -2), (key2666, -2), (key2722, -2), (key2701, -2), (key2790, -2), (key2781, -2), (key2825, -2), (key2804, -2), (key2866, -2), (key2856, -2)]

def rawRow11452 : Integer.Sparse Key := [(key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2801, 1), (key2895, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2947, 1), (key2974, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2627, -2), (key2611, -2), (key2636, -2), (key2701, -2), (key2666, -2), (key2722, -2), (key2804, -2), (key2856, -2), (key2781, -2), (key2866, -2), (key2790, -2), (key2825, -2)]

def rawRow11453 : Integer.Sparse Key := [(key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2825, 1), (key2790, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2958, 1), (key2941, 1), (key2627, -2), (key2636, -2), (key2611, -2), (key2701, -2), (key2722, -2), (key2666, -2), (key2856, -2), (key2804, -2), (key2866, -2), (key2781, -2), (key2825, -2), (key2790, -2)]

def rawRow11454 : Integer.Sparse Key := [(key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2825, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2778, 1), (key2801, 1), (key2958, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2935, 1), (key2947, 1), (key2636, -2), (key2611, -2), (key2627, -2), (key2722, -2), (key2666, -2), (key2701, -2), (key2825, -2), (key2866, -2), (key2790, -2), (key2856, -2), (key2781, -2), (key2804, -2)]

def rawRow11455 : Integer.Sparse Key := [(key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2902, 1), (key2825, 1), (key2895, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2958, 1), (key2974, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2636, -2), (key2627, -2), (key2611, -2), (key2722, -2), (key2701, -2), (key2666, -2), (key2866, -2), (key2825, -2), (key2856, -2), (key2790, -2), (key2804, -2), (key2781, -2)]

def rawRow11456 : Integer.Sparse Key := [(key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1), (key2666, -2), (key2781, -2), (key2790, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2627, -2), (key2636, -2), (key2701, -2), (key2722, -2), (key2856, -2), (key2866, -2)]

def rawRow11457 : Integer.Sparse Key := [(key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1), (key2666, -2), (key2790, -2), (key2781, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2636, -2), (key2627, -2), (key2722, -2), (key2701, -2), (key2866, -2), (key2856, -2)]

def rawRow11458 : Integer.Sparse Key := [(key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2781, -2), (key2666, -2), (key2790, -2), (key2804, -2), (key2611, -2), (key2825, -2), (key2701, -2), (key2856, -2), (key2627, -2), (key2866, -2), (key2636, -2), (key2722, -2)]

def rawRow11459 : Integer.Sparse Key := [(key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1), (key2781, -2), (key2790, -2), (key2666, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2856, -2), (key2701, -2), (key2866, -2), (key2627, -2), (key2722, -2), (key2636, -2)]

def rawRow11460 : Integer.Sparse Key := [(key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1), (key2790, -2), (key2666, -2), (key2781, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2722, -2), (key2866, -2), (key2636, -2), (key2856, -2), (key2627, -2), (key2701, -2)]

def rawRow11461 : Integer.Sparse Key := [(key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2790, -2), (key2781, -2), (key2666, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2866, -2), (key2722, -2), (key2856, -2), (key2636, -2), (key2701, -2), (key2627, -2)]

def rawRow11462 : Integer.Sparse Key := [(key2778, 1), (key2790, 1), (key2801, 1), (key2895, 1), (key2825, 1), (key2902, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2974, 1), (key2722, 1), (key2981, 1), (key2608, 1), (key2651, 1), (key2663, 1), (key2745, 1), (key2941, 1), (key2958, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2722, 1), (key2790, 1), (key2825, 1), (key2701, -2), (key2804, -2), (key2856, -2), (key2627, -2), (key2781, -2), (key2866, -2), (key2611, -2), (key2636, -2), (key2666, -2), (key2722, -2), (key2790, -2), (key2825, -2)]

def rawRow11463 : Integer.Sparse Key := [(key2790, 1), (key2778, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2825, 1), (key2636, 1), (key2624, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2722, 1), (key2651, 1), (key2608, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2941, 1), (key2636, 1), (key2611, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2790, 1), (key2701, -2), (key2856, -2), (key2804, -2), (key2627, -2), (key2866, -2), (key2781, -2), (key2636, -2), (key2611, -2), (key2722, -2), (key2666, -2), (key2825, -2), (key2790, -2)]

def rawRow11464 : Integer.Sparse Key := [(key2801, 1), (key2825, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2698, 1), (key2722, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2663, 1), (key2745, 1), (key2608, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2666, 1), (key2790, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2804, -2), (key2701, -2), (key2856, -2), (key2781, -2), (key2627, -2), (key2866, -2), (key2666, -2), (key2790, -2), (key2611, -2), (key2825, -2), (key2636, -2), (key2722, -2)]

def rawRow11465 : Integer.Sparse Key := [(key2825, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2895, 1), (key2790, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2974, 1), (key2636, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2608, 1), (key2745, 1), (key2651, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2722, 1), (key2636, 1), (key2804, -2), (key2856, -2), (key2701, -2), (key2781, -2), (key2866, -2), (key2627, -2), (key2790, -2), (key2666, -2), (key2825, -2), (key2611, -2), (key2722, -2), (key2636, -2)]

def rawRow11466 : Integer.Sparse Key := [(key2895, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2778, 1), (key2801, 1), (key2974, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2624, 1), (key2698, 1), (key2941, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2608, 1), (key2663, 1), (key2722, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2611, 1), (key2666, 1), (key2856, -2), (key2701, -2), (key2804, -2), (key2866, -2), (key2627, -2), (key2781, -2), (key2722, -2), (key2825, -2), (key2636, -2), (key2790, -2), (key2611, -2), (key2666, -2)]

def rawRow11467 : Integer.Sparse Key := [(key2902, 1), (key2895, 1), (key2825, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2974, 1), (key2722, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2958, 1), (key2941, 1), (key2745, 1), (key2651, 1), (key2663, 1), (key2608, 1), (key2825, 1), (key2722, 1), (key2790, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2856, -2), (key2804, -2), (key2701, -2), (key2866, -2), (key2781, -2), (key2627, -2), (key2825, -2), (key2722, -2), (key2790, -2), (key2636, -2), (key2666, -2), (key2611, -2)]

def rawRow11468 : Integer.Sparse Key := [(key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1), (key2722, -2), (key2825, -2), (key2866, -2), (key2636, -2), (key2790, -2), (key2856, -2), (key2611, -2), (key2627, -2), (key2666, -2), (key2701, -2), (key2781, -2), (key2804, -2)]

def rawRow11469 : Integer.Sparse Key := [(key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1), (key2722, -2), (key2866, -2), (key2825, -2), (key2636, -2), (key2856, -2), (key2790, -2), (key2627, -2), (key2611, -2), (key2701, -2), (key2666, -2), (key2804, -2), (key2781, -2)]

def rawRow11470 : Integer.Sparse Key := [(key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2825, -2), (key2722, -2), (key2866, -2), (key2790, -2), (key2636, -2), (key2856, -2), (key2666, -2), (key2781, -2), (key2611, -2), (key2804, -2), (key2627, -2), (key2701, -2)]

def rawRow11471 : Integer.Sparse Key := [(key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1), (key2825, -2), (key2866, -2), (key2722, -2), (key2790, -2), (key2856, -2), (key2636, -2), (key2781, -2), (key2666, -2), (key2804, -2), (key2611, -2), (key2701, -2), (key2627, -2)]

def rawRow11472 : Integer.Sparse Key := [(key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1), (key2866, -2), (key2722, -2), (key2825, -2), (key2856, -2), (key2636, -2), (key2790, -2), (key2701, -2), (key2804, -2), (key2627, -2), (key2781, -2), (key2611, -2), (key2666, -2)]

def rawRow11473 : Integer.Sparse Key := [(key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1), (key2866, -2), (key2825, -2), (key2722, -2), (key2856, -2), (key2790, -2), (key2636, -2), (key2804, -2), (key2701, -2), (key2781, -2), (key2627, -2), (key2666, -2), (key2611, -2)]

def rawRow11474 : Integer.Sparse Key := [(key2611, 1), (key2611, 1), (key2627, 1), (key2627, 1), (key2636, 1), (key2636, 1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1), (key2701, 1), (key2701, 1), (key2804, 1), (key2804, 1), (key2856, 1), (key2856, 1), (key2722, 1), (key2722, 1), (key2825, 1), (key2825, 1), (key2866, 1), (key2866, 1), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2778, -2), (key2778, -2), (key2801, -2), (key2801, -2), (key2851, -2), (key2851, -2)]

def rawRow11475 : Integer.Sparse Key := [(key2627, 1), (key2636, 1), (key2611, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2804, 1), (key2856, 1), (key2701, 1), (key2856, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2866, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2825, 1), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2851, -2), (key2778, -2), (key2801, -2)]

def rawRow11476 : Integer.Sparse Key := [(key2636, 1), (key2627, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2611, 1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1), (key2856, 1), (key2804, 1), (key2856, 1), (key2701, 1), (key2804, 1), (key2701, 1), (key2866, 1), (key2825, 1), (key2866, 1), (key2722, 1), (key2825, 1), (key2722, 1), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2851, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2778, -2)]

def rawRow11477 : Integer.Sparse Key := [(key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2722, 1), (key2722, 1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2627, 1), (key2627, 1), (key2781, 1), (key2781, 1), (key2866, 1), (key2866, 1), (key2636, 1), (key2636, 1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, -2), (key2624, -2), (key2698, -2), (key2698, -2), (key2851, -2), (key2851, -2)]

def rawRow11478 : Integer.Sparse Key := [(key2701, 1), (key2722, 1), (key2666, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2781, 1), (key2866, 1), (key2627, 1), (key2866, 1), (key2627, 1), (key2781, 1), (key2790, 1), (key2856, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2790, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2851, -2), (key2624, -2), (key2698, -2)]

def rawRow11479 : Integer.Sparse Key := [(key2722, 1), (key2701, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2866, 1), (key2781, 1), (key2866, 1), (key2627, 1), (key2781, 1), (key2627, 1), (key2856, 1), (key2790, 1), (key2856, 1), (key2636, 1), (key2790, 1), (key2636, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2624, -2)]

def rawRow11480 : Integer.Sparse Key := [(key2781, 1), (key2790, 1), (key2804, 1), (key2856, 1), (key2825, 1), (key2866, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2611, 1), (key2627, 1), (key2666, 1), (key2781, 1), (key2701, 1), (key2804, 1), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, -2), (key2624, -2), (key2663, -2), (key2698, -2), (key2778, -2), (key2801, -2)]

def rawRow11481 : Integer.Sparse Key := [(key2790, 1), (key2781, 1), (key2856, 1), (key2804, 1), (key2866, 1), (key2825, 1), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2627, 1), (key2611, 1), (key2781, 1), (key2666, 1), (key2804, 1), (key2701, 1), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2608, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2778, -2)]

def rawRow11482 : Integer.Sparse Key := [(key2804, 1), (key2825, 1), (key2781, 1), (key2866, 1), (key2790, 1), (key2856, 1), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2666, 1), (key2701, 1), (key2611, 1), (key2804, 1), (key2627, 1), (key2781, 1), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, -2), (key2698, -2), (key2608, -2), (key2801, -2), (key2624, -2), (key2698, -2)]

def rawRow11483 : Integer.Sparse Key := [(key2825, 1), (key2804, 1), (key2866, 1), (key2781, 1), (key2856, 1), (key2790, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2701, 1), (key2666, 1), (key2804, 1), (key2611, 1), (key2781, 1), (key2627, 1), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2663, -2), (key2801, -2), (key2608, -2), (key2698, -2), (key2624, -2)]

def rawRow11484 : Integer.Sparse Key := [(key2856, 1), (key2866, 1), (key2790, 1), (key2825, 1), (key2781, 1), (key2804, 1), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2781, 1), (key2804, 1), (key2627, 1), (key2701, 1), (key2611, 1), (key2666, 1), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, -2), (key2801, -2), (key2624, -2), (key2698, -2), (key2608, -2), (key2663, -2)]

def rawRow11485 : Integer.Sparse Key := [(key2866, 1), (key2856, 1), (key2825, 1), (key2790, 1), (key2804, 1), (key2781, 1), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2804, 1), (key2781, 1), (key2701, 1), (key2627, 1), (key2666, 1), (key2611, 1), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, -2), (key2778, -2), (key2698, -2), (key2624, -2), (key2663, -2), (key2608, -2)]

def rawRow11486 : Integer.Sparse Key := [(key2378, 2), (key2378, 2), (key2381, 2), (key2472, 2), (key2472, 2), (key2538, 2), (key2503, 2), (key2506, 2), (key2503, 2), (key2554, 2), (key2506, 2), (key2554, 2), (key2390, -2), (key2392, -2), (key2392, -2), (key2480, -2), (key2482, -2), (key2480, -2), (key2543, -2), (key2482, -2), (key2543, -2), (key2522, -2), (key2522, -2), (key2563, -2)]

def rawRow11487 : Integer.Sparse Key := [(key2378, 2), (key2381, 2), (key2378, 2), (key2472, 2), (key2538, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2554, 2), (key2503, 2), (key2554, 2), (key2506, 2), (key2392, -2), (key2390, -2), (key2392, -2), (key2482, -2), (key2480, -2), (key2543, -2), (key2480, -2), (key2543, -2), (key2482, -2), (key2522, -2), (key2563, -2), (key2522, -2)]

def rawRow11488 : Integer.Sparse Key := [(key2381, 2), (key2378, 2), (key2378, 2), (key2538, 2), (key2472, 2), (key2472, 2), (key2554, 2), (key2554, 2), (key2506, 2), (key2506, 2), (key2503, 2), (key2503, 2), (key2392, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2543, -2), (key2482, -2), (key2482, -2), (key2480, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2522, -2)]

def rawRow11489 : Integer.Sparse Key := [(key2472, 2), (key2503, 2), (key2506, 2), (key2378, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2381, 2), (key2472, 2), (key2538, 2), (key2506, 2), (key2554, 2), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, -2), (key2392, -2), (key2480, -2), (key2543, -2), (key2522, -2), (key2563, -2), (key2392, -2), (key2482, -2), (key2543, -2)]

def rawRow11490 : Integer.Sparse Key := [(key2472, 2), (key2506, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2503, 2), (key2381, 2), (key2378, 2), (key2538, 2), (key2472, 2), (key2554, 2), (key2506, 2), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, -2), (key2390, -2), (key2543, -2), (key2480, -2), (key2563, -2), (key2522, -2), (key2392, -2), (key2543, -2), (key2482, -2)]

def rawRow11491 : Integer.Sparse Key := [(key2503, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2472, 2), (key2506, 2), (key2378, 2), (key2554, 2), (key2381, 2), (key2538, 2), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, -2), (key2522, -2), (key2390, -2), (key2563, -2), (key2392, -2), (key2543, -2), (key2482, -2), (key2392, -2), (key2543, -2)]

def rawRow11492 : Integer.Sparse Key := [(key2503, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2506, 2), (key2472, 2), (key2554, 2), (key2378, 2), (key2538, 2), (key2381, 2), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, -2), (key2480, -2), (key2563, -2), (key2390, -2), (key2543, -2), (key2392, -2), (key2482, -2), (key2543, -2), (key2392, -2)]

def rawRow11493 : Integer.Sparse Key := [(key2506, 2), (key2472, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2503, 2), (key2538, 2), (key2554, 2), (key2381, 2), (key2506, 2), (key2378, 2), (key2472, 2), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2543, -2), (key2392, -2), (key2482, -2)]

def rawRow11494 : Integer.Sparse Key := [(key2506, 2), (key2503, 2), (key2472, 2), (key2554, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2538, 2), (key2506, 2), (key2381, 2), (key2472, 2), (key2378, 2), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, -2), (key2543, -2), (key2522, -2), (key2392, -2), (key2480, -2), (key2390, -2), (key2543, -2), (key2482, -2), (key2392, -2)]

def rawRow11495 : Integer.Sparse Key := [(key2538, 2), (key2554, 2), (key2554, 2), (key2381, 2), (key2506, 2), (key2506, 2), (key2378, 2), (key2378, 2), (key2472, 2), (key2472, 2), (key2503, 2), (key2503, 2), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, -2), (key2392, -2), (key2482, -2), (key2482, -2), (key2522, -2), (key2522, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

def rawRow11496 : Integer.Sparse Key := [(key2554, 2), (key2538, 2), (key2554, 2), (key2506, 2), (key2381, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

def rawRow11497 : Integer.Sparse Key := [(key2554, 2), (key2554, 2), (key2538, 2), (key2506, 2), (key2506, 2), (key2381, 2), (key2503, 2), (key2472, 2), (key2503, 2), (key2378, 2), (key2472, 2), (key2378, 2), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2392, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11546 : Integer.Sparse Key := [(key2609, -2), (key2613, -2), (key2613, -2), (key2802, -2), (key2806, -2), (key2802, -2), (key2949, -2), (key2806, -2), (key2949, -2), (key2826, -2), (key2826, -2), (key2959, -2), (key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2852, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2973, 1), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1)]

def rawRow11547 : Integer.Sparse Key := [(key2613, -2), (key2609, -2), (key2613, -2), (key2806, -2), (key2802, -2), (key2949, -2), (key2802, -2), (key2949, -2), (key2806, -2), (key2826, -2), (key2959, -2), (key2826, -2), (key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1)]

def rawRow11548 : Integer.Sparse Key := [(key2613, -2), (key2613, -2), (key2609, -2), (key2949, -2), (key2949, -2), (key2806, -2), (key2806, -2), (key2802, -2), (key2802, -2), (key2959, -2), (key2826, -2), (key2826, -2), (key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2973, 1), (key2973, 1), (key2894, 1), (key2894, 1), (key2852, 1), (key2852, 1), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1)]

def rawRow11549 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2609, -2), (key2613, -2), (key2802, -2), (key2949, -2), (key2826, -2), (key2959, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1)]

def rawRow11550 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2613, -2), (key2609, -2), (key2949, -2), (key2802, -2), (key2959, -2), (key2826, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1)]

def rawRow11551 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2802, -2), (key2826, -2), (key2609, -2), (key2959, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2949, -2), (key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1)]

def rawRow11552 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2826, -2), (key2802, -2), (key2959, -2), (key2609, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2613, -2), (key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1)]

def rawRow11553 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2949, -2), (key2959, -2), (key2613, -2), (key2826, -2), (key2609, -2), (key2802, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1)]

def rawRow11554 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2959, -2), (key2949, -2), (key2826, -2), (key2613, -2), (key2802, -2), (key2609, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

def rawRow11555 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2613, -2), (key2613, -2), (key2806, -2), (key2806, -2), (key2826, -2), (key2826, -2), (key2609, -2), (key2802, -2), (key2802, -2), (key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1)]

def rawRow11556 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2806, -2), (key2826, -2), (key2613, -2), (key2826, -2), (key2613, -2), (key2806, -2), (key2802, -2), (key2609, -2), (key2802, -2), (key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1)]

def rawRow11557 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2826, -2), (key2806, -2), (key2826, -2), (key2613, -2), (key2806, -2), (key2613, -2), (key2802, -2), (key2802, -2), (key2609, -2), (key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1)]

def rawRow11570 : Integer.Sparse Key := [(key2664, -2), (key2668, -2), (key2668, -2), (key2699, -2), (key2703, -2), (key2699, -2), (key2736, -2), (key2703, -2), (key2736, -2), (key2723, -2), (key2723, -2), (key2746, -2), (key2609, 2), (key2613, 2), (key2613, 2), (key2802, 2), (key2806, 2), (key2802, 2), (key2949, 2), (key2806, 2), (key2949, 2), (key2826, 2), (key2826, 2), (key2959, 2)]

def rawRow11571 : Integer.Sparse Key := [(key2668, -2), (key2664, -2), (key2668, -2), (key2703, -2), (key2699, -2), (key2736, -2), (key2699, -2), (key2736, -2), (key2703, -2), (key2723, -2), (key2746, -2), (key2723, -2), (key2613, 2), (key2609, 2), (key2613, 2), (key2806, 2), (key2802, 2), (key2949, 2), (key2802, 2), (key2949, 2), (key2806, 2), (key2826, 2), (key2959, 2), (key2826, 2)]

def rawRow11572 : Integer.Sparse Key := [(key2668, -2), (key2668, -2), (key2664, -2), (key2736, -2), (key2736, -2), (key2703, -2), (key2703, -2), (key2699, -2), (key2699, -2), (key2746, -2), (key2723, -2), (key2723, -2), (key2613, 2), (key2613, 2), (key2609, 2), (key2949, 2), (key2949, 2), (key2806, 2), (key2806, 2), (key2802, 2), (key2802, 2), (key2959, 2), (key2826, 2), (key2826, 2)]

def rawRow11573 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2664, -2), (key2668, -2), (key2699, -2), (key2736, -2), (key2723, -2), (key2746, -2), (key2668, -2), (key2703, -2), (key2736, -2), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, 2), (key2613, 2), (key2802, 2), (key2949, 2), (key2826, 2), (key2959, 2), (key2613, 2), (key2806, 2), (key2949, 2)]

def rawRow11574 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2668, -2), (key2664, -2), (key2736, -2), (key2699, -2), (key2746, -2), (key2723, -2), (key2668, -2), (key2736, -2), (key2703, -2), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, 2), (key2609, 2), (key2949, 2), (key2802, 2), (key2959, 2), (key2826, 2), (key2613, 2), (key2949, 2), (key2806, 2)]

def rawRow11575 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2699, -2), (key2723, -2), (key2664, -2), (key2746, -2), (key2668, -2), (key2736, -2), (key2703, -2), (key2668, -2), (key2736, -2), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, 2), (key2826, 2), (key2609, 2), (key2959, 2), (key2613, 2), (key2949, 2), (key2806, 2), (key2613, 2), (key2949, 2)]

def rawRow11576 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2723, -2), (key2699, -2), (key2746, -2), (key2664, -2), (key2736, -2), (key2668, -2), (key2703, -2), (key2736, -2), (key2668, -2), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, 2), (key2802, 2), (key2959, 2), (key2609, 2), (key2949, 2), (key2613, 2), (key2806, 2), (key2949, 2), (key2613, 2)]

def rawRow11577 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2736, -2), (key2746, -2), (key2668, -2), (key2723, -2), (key2664, -2), (key2699, -2), (key2736, -2), (key2668, -2), (key2703, -2), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, 2), (key2959, 2), (key2613, 2), (key2826, 2), (key2609, 2), (key2802, 2), (key2949, 2), (key2613, 2), (key2806, 2)]

def rawRow11578 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2746, -2), (key2736, -2), (key2723, -2), (key2668, -2), (key2699, -2), (key2664, -2), (key2736, -2), (key2703, -2), (key2668, -2), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, 2), (key2949, 2), (key2826, 2), (key2613, 2), (key2802, 2), (key2609, 2), (key2949, 2), (key2806, 2), (key2613, 2)]

def rawRow11579 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2668, -2), (key2668, -2), (key2703, -2), (key2703, -2), (key2723, -2), (key2723, -2), (key2664, -2), (key2699, -2), (key2699, -2), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, 2), (key2613, 2), (key2806, 2), (key2806, 2), (key2826, 2), (key2826, 2), (key2609, 2), (key2802, 2), (key2802, 2)]

def rawRow11580 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2703, -2), (key2723, -2), (key2668, -2), (key2723, -2), (key2668, -2), (key2703, -2), (key2699, -2), (key2664, -2), (key2699, -2), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, 2), (key2826, 2), (key2613, 2), (key2826, 2), (key2613, 2), (key2806, 2), (key2802, 2), (key2609, 2), (key2802, 2)]

def rawRow11581 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2723, -2), (key2703, -2), (key2723, -2), (key2668, -2), (key2703, -2), (key2668, -2), (key2699, -2), (key2699, -2), (key2664, -2), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, 2), (key2806, 2), (key2826, 2), (key2613, 2), (key2806, 2), (key2613, 2), (key2802, 2), (key2802, 2), (key2609, 2)]

def rawRow11582 : Integer.Sparse Key := [(key1292, -2), (key1297, -2), (key1297, -2), (key1569, -2), (key1574, -2), (key1569, -2), (key1789, -2), (key1574, -2), (key1789, -2), (key1592, -2), (key1592, -2), (key1797, -2), (key1312, 1), (key1317, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1338, 1), (key1542, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1773, 1), (key1618, 1), (key1656, 1), (key1618, 1), (key1814, 1), (key1656, 1), (key1814, 1), (key1632, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1666, 1), (key1824, 1)]

def rawRow11583 : Integer.Sparse Key := [(key1297, -2), (key1292, -2), (key1297, -2), (key1574, -2), (key1569, -2), (key1789, -2), (key1569, -2), (key1789, -2), (key1574, -2), (key1592, -2), (key1797, -2), (key1592, -2), (key1317, 1), (key1312, 1), (key1338, 1), (key1312, 1), (key1338, 1), (key1317, 1), (key1547, 1), (key1542, 1), (key1773, 1), (key1542, 1), (key1773, 1), (key1547, 1), (key1656, 1), (key1618, 1), (key1814, 1), (key1618, 1), (key1814, 1), (key1656, 1), (key1666, 1), (key1632, 1), (key1824, 1), (key1632, 1), (key1824, 1), (key1666, 1)]

def rawRow11584 : Integer.Sparse Key := [(key1297, -2), (key1297, -2), (key1292, -2), (key1789, -2), (key1789, -2), (key1574, -2), (key1574, -2), (key1569, -2), (key1569, -2), (key1797, -2), (key1592, -2), (key1592, -2), (key1338, 1), (key1338, 1), (key1317, 1), (key1317, 1), (key1312, 1), (key1312, 1), (key1773, 1), (key1773, 1), (key1547, 1), (key1547, 1), (key1542, 1), (key1542, 1), (key1814, 1), (key1814, 1), (key1656, 1), (key1656, 1), (key1618, 1), (key1618, 1), (key1824, 1), (key1824, 1), (key1666, 1), (key1666, 1), (key1632, 1), (key1632, 1)]

def rawRow11585 : Integer.Sparse Key := [(key1569, -2), (key1574, -2), (key1592, -2), (key1292, -2), (key1297, -2), (key1569, -2), (key1789, -2), (key1592, -2), (key1797, -2), (key1297, -2), (key1574, -2), (key1789, -2), (key1542, 1), (key1547, 1), (key1618, 1), (key1656, 1), (key1632, 1), (key1666, 1), (key1312, 1), (key1317, 1), (key1618, 1), (key1814, 1), (key1632, 1), (key1824, 1), (key1312, 1), (key1338, 1), (key1542, 1), (key1773, 1), (key1666, 1), (key1824, 1), (key1317, 1), (key1338, 1), (key1547, 1), (key1773, 1), (key1656, 1), (key1814, 1)]

def rawRow11586 : Integer.Sparse Key := [(key1574, -2), (key1569, -2), (key1592, -2), (key1297, -2), (key1292, -2), (key1789, -2), (key1569, -2), (key1797, -2), (key1592, -2), (key1297, -2), (key1789, -2), (key1574, -2), (key1547, 1), (key1542, 1), (key1656, 1), (key1618, 1), (key1666, 1), (key1632, 1), (key1317, 1), (key1312, 1), (key1814, 1), (key1618, 1), (key1824, 1), (key1632, 1), (key1338, 1), (key1312, 1), (key1773, 1), (key1542, 1), (key1824, 1), (key1666, 1), (key1338, 1), (key1317, 1), (key1773, 1), (key1547, 1), (key1814, 1), (key1656, 1)]

def rawRow11587 : Integer.Sparse Key := [(key1569, -2), (key1592, -2), (key1574, -2), (key1569, -2), (key1592, -2), (key1292, -2), (key1797, -2), (key1297, -2), (key1789, -2), (key1574, -2), (key1297, -2), (key1789, -2), (key1618, 1), (key1632, 1), (key1542, 1), (key1666, 1), (key1547, 1), (key1656, 1), (key1618, 1), (key1632, 1), (key1312, 1), (key1824, 1), (key1317, 1), (key1814, 1), (key1542, 1), (key1666, 1), (key1312, 1), (key1824, 1), (key1338, 1), (key1773, 1), (key1547, 1), (key1656, 1), (key1317, 1), (key1814, 1), (key1338, 1), (key1773, 1)]

def rawRow11588 : Integer.Sparse Key := [(key1592, -2), (key1569, -2), (key1574, -2), (key1592, -2), (key1569, -2), (key1797, -2), (key1292, -2), (key1789, -2), (key1297, -2), (key1574, -2), (key1789, -2), (key1297, -2), (key1632, 1), (key1618, 1), (key1666, 1), (key1542, 1), (key1656, 1), (key1547, 1), (key1632, 1), (key1618, 1), (key1824, 1), (key1312, 1), (key1814, 1), (key1317, 1), (key1666, 1), (key1542, 1), (key1824, 1), (key1312, 1), (key1773, 1), (key1338, 1), (key1656, 1), (key1547, 1), (key1814, 1), (key1317, 1), (key1773, 1), (key1338, 1)]

def rawRow11589 : Integer.Sparse Key := [(key1574, -2), (key1592, -2), (key1569, -2), (key1789, -2), (key1797, -2), (key1297, -2), (key1592, -2), (key1292, -2), (key1569, -2), (key1789, -2), (key1297, -2), (key1574, -2), (key1656, 1), (key1666, 1), (key1547, 1), (key1632, 1), (key1542, 1), (key1618, 1), (key1814, 1), (key1824, 1), (key1317, 1), (key1632, 1), (key1312, 1), (key1618, 1), (key1773, 1), (key1824, 1), (key1338, 1), (key1666, 1), (key1312, 1), (key1542, 1), (key1773, 1), (key1814, 1), (key1338, 1), (key1656, 1), (key1317, 1), (key1547, 1)]

def rawRow11590 : Integer.Sparse Key := [(key1592, -2), (key1574, -2), (key1569, -2), (key1797, -2), (key1789, -2), (key1592, -2), (key1297, -2), (key1569, -2), (key1292, -2), (key1789, -2), (key1574, -2), (key1297, -2), (key1666, 1), (key1656, 1), (key1632, 1), (key1547, 1), (key1618, 1), (key1542, 1), (key1824, 1), (key1814, 1), (key1632, 1), (key1317, 1), (key1618, 1), (key1312, 1), (key1824, 1), (key1773, 1), (key1666, 1), (key1338, 1), (key1542, 1), (key1312, 1), (key1814, 1), (key1773, 1), (key1656, 1), (key1338, 1), (key1547, 1), (key1317, 1)]

def rawRow11591 : Integer.Sparse Key := [(key1789, -2), (key1789, -2), (key1797, -2), (key1297, -2), (key1297, -2), (key1574, -2), (key1574, -2), (key1592, -2), (key1592, -2), (key1292, -2), (key1569, -2), (key1569, -2), (key1773, 1), (key1773, 1), (key1814, 1), (key1814, 1), (key1824, 1), (key1824, 1), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1), (key1317, 1), (key1317, 1), (key1547, 1), (key1547, 1), (key1632, 1), (key1632, 1), (key1312, 1), (key1312, 1), (key1542, 1), (key1542, 1), (key1618, 1), (key1618, 1)]

def rawRow11592 : Integer.Sparse Key := [(key1789, -2), (key1797, -2), (key1789, -2), (key1574, -2), (key1592, -2), (key1297, -2), (key1592, -2), (key1297, -2), (key1574, -2), (key1569, -2), (key1292, -2), (key1569, -2), (key1814, 1), (key1824, 1), (key1773, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1542, 1)]

def rawRow11593 : Integer.Sparse Key := [(key1797, -2), (key1789, -2), (key1789, -2), (key1592, -2), (key1574, -2), (key1592, -2), (key1297, -2), (key1574, -2), (key1297, -2), (key1569, -2), (key1569, -2), (key1292, -2), (key1824, 1), (key1814, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1773, 1), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1), (key1632, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1317, 1), (key1618, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1542, 1), (key1312, 1)]

def rawRow11594 : Integer.Sparse Key := [(key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2852, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2973, 1), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1), (key2637, -2), (key2637, -2), (key2652, -2), (key2791, -2), (key2791, -2), (key2942, -2), (key2857, -2), (key2896, -2), (key2857, -2), (key2975, -2), (key2896, -2), (key2975, -2)]

def rawRow11595 : Integer.Sparse Key := [(key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2973, 1), (key2852, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2637, -2), (key2652, -2), (key2637, -2), (key2791, -2), (key2942, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2975, -2), (key2857, -2), (key2975, -2), (key2896, -2)]

def rawRow11596 : Integer.Sparse Key := [(key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2973, 1), (key2973, 1), (key2894, 1), (key2894, 1), (key2852, 1), (key2852, 1), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1), (key2652, -2), (key2637, -2), (key2637, -2), (key2942, -2), (key2791, -2), (key2791, -2), (key2975, -2), (key2975, -2), (key2896, -2), (key2896, -2), (key2857, -2), (key2857, -2)]

def rawRow11597 : Integer.Sparse Key := [(key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1), (key2791, -2), (key2857, -2), (key2896, -2), (key2637, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2652, -2), (key2791, -2), (key2942, -2), (key2896, -2), (key2975, -2)]

def rawRow11598 : Integer.Sparse Key := [(key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1), (key2791, -2), (key2896, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2857, -2), (key2652, -2), (key2637, -2), (key2942, -2), (key2791, -2), (key2975, -2), (key2896, -2)]

def rawRow11599 : Integer.Sparse Key := [(key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1), (key2857, -2), (key2791, -2), (key2896, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2791, -2), (key2896, -2), (key2637, -2), (key2975, -2), (key2652, -2), (key2942, -2)]

def rawRow11600 : Integer.Sparse Key := [(key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1), (key2857, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2896, -2), (key2791, -2), (key2975, -2), (key2637, -2), (key2942, -2), (key2652, -2)]

def rawRow11601 : Integer.Sparse Key := [(key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1), (key2896, -2), (key2791, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2857, -2), (key2942, -2), (key2975, -2), (key2652, -2), (key2896, -2), (key2637, -2), (key2791, -2)]

def rawRow11602 : Integer.Sparse Key := [(key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1), (key2896, -2), (key2857, -2), (key2791, -2), (key2975, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2942, -2), (key2896, -2), (key2652, -2), (key2791, -2), (key2637, -2)]

def rawRow11603 : Integer.Sparse Key := [(key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1), (key2942, -2), (key2975, -2), (key2975, -2), (key2652, -2), (key2896, -2), (key2896, -2), (key2637, -2), (key2637, -2), (key2791, -2), (key2791, -2), (key2857, -2), (key2857, -2)]

def rawRow11604 : Integer.Sparse Key := [(key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2975, -2), (key2942, -2), (key2975, -2), (key2896, -2), (key2652, -2), (key2896, -2), (key2791, -2), (key2857, -2), (key2637, -2), (key2857, -2), (key2637, -2), (key2791, -2)]

def rawRow11605 : Integer.Sparse Key := [(key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1), (key2975, -2), (key2975, -2), (key2942, -2), (key2896, -2), (key2896, -2), (key2652, -2), (key2857, -2), (key2791, -2), (key2857, -2), (key2637, -2), (key2791, -2), (key2637, -2)]

def rawRow11618 : Integer.Sparse Key := [(key2398, 6), (key2401, 6), (key2401, 6), (key2433, 6), (key2597, -6), (key2886, -6), (key2886, -6), (key2908, -6)]

def rawRow11619 : Integer.Sparse Key := [(key2401, 6), (key2398, 6), (key2401, 6), (key2433, 6), (key2597, -6), (key2886, -6), (key2908, -6), (key2886, -6)]

def rawRow11620 : Integer.Sparse Key := [(key2401, 6), (key2401, 6), (key2398, 6), (key2433, 6), (key2597, -6), (key2908, -6), (key2886, -6), (key2886, -6)]

def rawRow11621 : Integer.Sparse Key := [(key2398, 6), (key2401, 6), (key2433, 6), (key2401, 6), (key2886, -6), (key2597, -6), (key2886, -6), (key2908, -6)]

def rawRow11622 : Integer.Sparse Key := [(key2401, 6), (key2398, 6), (key2433, 6), (key2401, 6), (key2886, -6), (key2597, -6), (key2908, -6), (key2886, -6)]

def rawRow11623 : Integer.Sparse Key := [(key2398, 6), (key2433, 6), (key2401, 6), (key2401, 6), (key2886, -6), (key2886, -6), (key2597, -6), (key2908, -6)]

def rawRow11624 : Integer.Sparse Key := [(key2433, 6), (key2398, 6), (key2401, 6), (key2401, 6), (key2886, -6), (key2886, -6), (key2908, -6), (key2597, -6)]

def rawRow11625 : Integer.Sparse Key := [(key2401, 6), (key2433, 6), (key2398, 6), (key2401, 6), (key2886, -6), (key2908, -6), (key2597, -6), (key2886, -6)]

def rawRow11626 : Integer.Sparse Key := [(key2433, 6), (key2401, 6), (key2398, 6), (key2401, 6), (key2886, -6), (key2908, -6), (key2886, -6), (key2597, -6)]

def rawRow11627 : Integer.Sparse Key := [(key2401, 6), (key2401, 6), (key2433, 6), (key2398, 6), (key2908, -6), (key2597, -6), (key2886, -6), (key2886, -6)]

def rawRow11628 : Integer.Sparse Key := [(key2401, 6), (key2433, 6), (key2401, 6), (key2398, 6), (key2908, -6), (key2886, -6), (key2597, -6), (key2886, -6)]

def rawRow11629 : Integer.Sparse Key := [(key2433, 6), (key2401, 6), (key2401, 6), (key2398, 6), (key2908, -6), (key2886, -6), (key2886, -6), (key2597, -6)]

def rawRow11630 : Integer.Sparse Key := [(key2399, 6), (key2403, 6), (key2403, 6), (key2434, 6), (key2387, -6), (key2477, -6), (key2477, -6), (key2541, -6)]

def rawRow11631 : Integer.Sparse Key := [(key2403, 6), (key2399, 6), (key2403, 6), (key2434, 6), (key2387, -6), (key2477, -6), (key2541, -6), (key2477, -6)]

def rawRow11632 : Integer.Sparse Key := [(key2403, 6), (key2403, 6), (key2399, 6), (key2434, 6), (key2387, -6), (key2541, -6), (key2477, -6), (key2477, -6)]

def rawRow11633 : Integer.Sparse Key := [(key2399, 6), (key2403, 6), (key2434, 6), (key2403, 6), (key2477, -6), (key2387, -6), (key2477, -6), (key2541, -6)]

def rawRow11634 : Integer.Sparse Key := [(key2403, 6), (key2399, 6), (key2434, 6), (key2403, 6), (key2477, -6), (key2387, -6), (key2541, -6), (key2477, -6)]

def rawRow11635 : Integer.Sparse Key := [(key2399, 6), (key2434, 6), (key2403, 6), (key2403, 6), (key2477, -6), (key2477, -6), (key2387, -6), (key2541, -6)]

def rawRow11636 : Integer.Sparse Key := [(key2434, 6), (key2399, 6), (key2403, 6), (key2403, 6), (key2477, -6), (key2477, -6), (key2541, -6), (key2387, -6)]

def rawRow11637 : Integer.Sparse Key := [(key2403, 6), (key2434, 6), (key2399, 6), (key2403, 6), (key2477, -6), (key2541, -6), (key2387, -6), (key2477, -6)]

def rawRow11638 : Integer.Sparse Key := [(key2434, 6), (key2403, 6), (key2399, 6), (key2403, 6), (key2477, -6), (key2541, -6), (key2477, -6), (key2387, -6)]

def rawRow11639 : Integer.Sparse Key := [(key2403, 6), (key2403, 6), (key2434, 6), (key2399, 6), (key2541, -6), (key2387, -6), (key2477, -6), (key2477, -6)]

def rawRow11640 : Integer.Sparse Key := [(key2403, 6), (key2434, 6), (key2403, 6), (key2399, 6), (key2541, -6), (key2477, -6), (key2387, -6), (key2477, -6)]

def rawRow11641 : Integer.Sparse Key := [(key2434, 6), (key2403, 6), (key2403, 6), (key2399, 6), (key2541, -6), (key2477, -6), (key2477, -6), (key2387, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11654 : Integer.Sparse Key := [(key1029, 6), (key1034, 6), (key1034, 6), (key1069, 6), (key1013, -6), (key1121, -6), (key1121, -6), (key1197, -6)]

def rawRow11655 : Integer.Sparse Key := [(key1034, 6), (key1029, 6), (key1034, 6), (key1069, 6), (key1013, -6), (key1121, -6), (key1197, -6), (key1121, -6)]

def rawRow11656 : Integer.Sparse Key := [(key1034, 6), (key1034, 6), (key1029, 6), (key1069, 6), (key1013, -6), (key1197, -6), (key1121, -6), (key1121, -6)]

def rawRow11657 : Integer.Sparse Key := [(key1029, 6), (key1034, 6), (key1069, 6), (key1034, 6), (key1121, -6), (key1013, -6), (key1121, -6), (key1197, -6)]

def rawRow11658 : Integer.Sparse Key := [(key1034, 6), (key1029, 6), (key1069, 6), (key1034, 6), (key1121, -6), (key1013, -6), (key1197, -6), (key1121, -6)]

def rawRow11659 : Integer.Sparse Key := [(key1029, 6), (key1069, 6), (key1034, 6), (key1034, 6), (key1121, -6), (key1121, -6), (key1013, -6), (key1197, -6)]

def rawRow11660 : Integer.Sparse Key := [(key1069, 6), (key1029, 6), (key1034, 6), (key1034, 6), (key1121, -6), (key1121, -6), (key1197, -6), (key1013, -6)]

def rawRow11661 : Integer.Sparse Key := [(key1034, 6), (key1069, 6), (key1029, 6), (key1034, 6), (key1121, -6), (key1197, -6), (key1013, -6), (key1121, -6)]

def rawRow11662 : Integer.Sparse Key := [(key1069, 6), (key1034, 6), (key1029, 6), (key1034, 6), (key1121, -6), (key1197, -6), (key1121, -6), (key1013, -6)]

def rawRow11663 : Integer.Sparse Key := [(key1034, 6), (key1034, 6), (key1069, 6), (key1029, 6), (key1197, -6), (key1013, -6), (key1121, -6), (key1121, -6)]

def rawRow11664 : Integer.Sparse Key := [(key1034, 6), (key1069, 6), (key1034, 6), (key1029, 6), (key1197, -6), (key1121, -6), (key1013, -6), (key1121, -6)]

def rawRow11665 : Integer.Sparse Key := [(key1069, 6), (key1034, 6), (key1034, 6), (key1029, 6), (key1197, -6), (key1121, -6), (key1121, -6), (key1013, -6)]

def rawRow11678 : Integer.Sparse Key := [(key2662, -6), (key2777, -6), (key2777, -6), (key2788, -6), (key2607, 6), (key2800, 6), (key2800, 6), (key2823, 6)]

def rawRow11679 : Integer.Sparse Key := [(key2662, -6), (key2777, -6), (key2788, -6), (key2777, -6), (key2607, 6), (key2800, 6), (key2823, 6), (key2800, 6)]

def rawRow11680 : Integer.Sparse Key := [(key2662, -6), (key2788, -6), (key2777, -6), (key2777, -6), (key2607, 6), (key2823, 6), (key2800, 6), (key2800, 6)]

def rawRow11681 : Integer.Sparse Key := [(key2777, -6), (key2662, -6), (key2777, -6), (key2788, -6), (key2800, 6), (key2607, 6), (key2800, 6), (key2823, 6)]

def rawRow11682 : Integer.Sparse Key := [(key2777, -6), (key2662, -6), (key2788, -6), (key2777, -6), (key2800, 6), (key2607, 6), (key2823, 6), (key2800, 6)]

def rawRow11683 : Integer.Sparse Key := [(key2777, -6), (key2777, -6), (key2662, -6), (key2788, -6), (key2800, 6), (key2800, 6), (key2607, 6), (key2823, 6)]

def rawRow11684 : Integer.Sparse Key := [(key2777, -6), (key2777, -6), (key2788, -6), (key2662, -6), (key2800, 6), (key2800, 6), (key2823, 6), (key2607, 6)]

def rawRow11685 : Integer.Sparse Key := [(key2777, -6), (key2788, -6), (key2662, -6), (key2777, -6), (key2800, 6), (key2823, 6), (key2607, 6), (key2800, 6)]

def rawRow11686 : Integer.Sparse Key := [(key2777, -6), (key2788, -6), (key2777, -6), (key2662, -6), (key2800, 6), (key2823, 6), (key2800, 6), (key2607, 6)]

def rawRow11687 : Integer.Sparse Key := [(key2788, -6), (key2662, -6), (key2777, -6), (key2777, -6), (key2823, 6), (key2607, 6), (key2800, 6), (key2800, 6)]

def rawRow11688 : Integer.Sparse Key := [(key2788, -6), (key2777, -6), (key2662, -6), (key2777, -6), (key2823, 6), (key2800, 6), (key2607, 6), (key2800, 6)]

def rawRow11689 : Integer.Sparse Key := [(key2788, -6), (key2777, -6), (key2777, -6), (key2662, -6), (key2823, 6), (key2800, 6), (key2800, 6), (key2607, 6)]

def rawRow11690 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2809, -2), (key2809, -2), (key2951, -2), (key2829, -2), (key2832, -2), (key2829, -2), (key2961, -2), (key2832, -2), (key2961, -2), (key2632, 2), (key2632, 2), (key2649, 2), (key2786, 2), (key2786, 2), (key2939, 2), (key2870, 2), (key2905, 2), (key2870, 2), (key2984, 2), (key2905, 2), (key2984, 2)]

def rawRow11691 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2809, -2), (key2951, -2), (key2809, -2), (key2832, -2), (key2829, -2), (key2961, -2), (key2829, -2), (key2961, -2), (key2832, -2), (key2632, 2), (key2649, 2), (key2632, 2), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, 2), (key2870, 2), (key2984, 2), (key2870, 2), (key2984, 2), (key2905, 2)]

def rawRow11692 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2951, -2), (key2809, -2), (key2809, -2), (key2961, -2), (key2961, -2), (key2832, -2), (key2832, -2), (key2829, -2), (key2829, -2), (key2649, 2), (key2632, 2), (key2632, 2), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, 2), (key2984, 2), (key2905, 2), (key2905, 2), (key2870, 2), (key2870, 2)]

def rawRow11693 : Integer.Sparse Key := [(key2809, -2), (key2829, -2), (key2832, -2), (key2616, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2619, -2), (key2809, -2), (key2951, -2), (key2832, -2), (key2961, -2), (key2786, 2), (key2870, 2), (key2905, 2), (key2632, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2649, 2), (key2786, 2), (key2939, 2), (key2905, 2), (key2984, 2)]

def rawRow11694 : Integer.Sparse Key := [(key2809, -2), (key2832, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2829, -2), (key2619, -2), (key2616, -2), (key2951, -2), (key2809, -2), (key2961, -2), (key2832, -2), (key2786, 2), (key2905, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2870, 2), (key2649, 2), (key2632, 2), (key2939, 2), (key2786, 2), (key2984, 2), (key2905, 2)]

def rawRow11695 : Integer.Sparse Key := [(key2829, -2), (key2809, -2), (key2832, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2809, -2), (key2832, -2), (key2616, -2), (key2961, -2), (key2619, -2), (key2951, -2), (key2870, 2), (key2786, 2), (key2905, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2786, 2), (key2905, 2), (key2632, 2), (key2984, 2), (key2649, 2), (key2939, 2)]

def rawRow11696 : Integer.Sparse Key := [(key2829, -2), (key2832, -2), (key2809, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2832, -2), (key2809, -2), (key2961, -2), (key2616, -2), (key2951, -2), (key2619, -2), (key2870, 2), (key2905, 2), (key2786, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2905, 2), (key2786, 2), (key2984, 2), (key2632, 2), (key2939, 2), (key2649, 2)]

def rawRow11697 : Integer.Sparse Key := [(key2832, -2), (key2809, -2), (key2829, -2), (key2961, -2), (key2616, -2), (key2829, -2), (key2951, -2), (key2961, -2), (key2619, -2), (key2832, -2), (key2616, -2), (key2809, -2), (key2905, 2), (key2786, 2), (key2870, 2), (key2984, 2), (key2632, 2), (key2870, 2), (key2939, 2), (key2984, 2), (key2649, 2), (key2905, 2), (key2632, 2), (key2786, 2)]

def rawRow11698 : Integer.Sparse Key := [(key2832, -2), (key2829, -2), (key2809, -2), (key2961, -2), (key2829, -2), (key2616, -2), (key2961, -2), (key2951, -2), (key2832, -2), (key2619, -2), (key2809, -2), (key2616, -2), (key2905, 2), (key2870, 2), (key2786, 2), (key2984, 2), (key2870, 2), (key2632, 2), (key2984, 2), (key2939, 2), (key2905, 2), (key2649, 2), (key2786, 2), (key2632, 2)]

def rawRow11699 : Integer.Sparse Key := [(key2951, -2), (key2961, -2), (key2961, -2), (key2619, -2), (key2832, -2), (key2832, -2), (key2616, -2), (key2616, -2), (key2809, -2), (key2809, -2), (key2829, -2), (key2829, -2), (key2939, 2), (key2984, 2), (key2984, 2), (key2649, 2), (key2905, 2), (key2905, 2), (key2632, 2), (key2632, 2), (key2786, 2), (key2786, 2), (key2870, 2), (key2870, 2)]

def rawRow11700 : Integer.Sparse Key := [(key2961, -2), (key2951, -2), (key2961, -2), (key2832, -2), (key2619, -2), (key2832, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2984, 2), (key2939, 2), (key2984, 2), (key2905, 2), (key2649, 2), (key2905, 2), (key2786, 2), (key2870, 2), (key2632, 2), (key2870, 2), (key2632, 2), (key2786, 2)]

def rawRow11701 : Integer.Sparse Key := [(key2961, -2), (key2961, -2), (key2951, -2), (key2832, -2), (key2832, -2), (key2619, -2), (key2829, -2), (key2809, -2), (key2829, -2), (key2616, -2), (key2809, -2), (key2616, -2), (key2984, 2), (key2984, 2), (key2939, 2), (key2905, 2), (key2905, 2), (key2649, 2), (key2870, 2), (key2786, 2), (key2870, 2), (key2632, 2), (key2786, 2), (key2632, 2)]

def rawRow11738 : Integer.Sparse Key := [(key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1), (key2851, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2866, 1), (key2971, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2981, 1), (key2645, -2), (key2645, -2), (key2651, -2), (key2734, -2), (key2734, -2), (key2745, -2), (key2892, -2), (key2895, -2), (key2892, -2), (key2902, -2), (key2895, -2), (key2902, -2)]

def rawRow11739 : Integer.Sparse Key := [(key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2645, -2), (key2651, -2), (key2645, -2), (key2734, -2), (key2745, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2902, -2), (key2892, -2), (key2902, -2), (key2895, -2)]

def rawRow11740 : Integer.Sparse Key := [(key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2866, 1), (key2866, 1), (key2856, 1), (key2856, 1), (key2851, 1), (key2851, 1), (key2981, 1), (key2981, 1), (key2974, 1), (key2974, 1), (key2971, 1), (key2971, 1), (key2651, -2), (key2645, -2), (key2645, -2), (key2745, -2), (key2734, -2), (key2734, -2), (key2902, -2), (key2902, -2), (key2895, -2), (key2895, -2), (key2892, -2), (key2892, -2)]

def rawRow11741 : Integer.Sparse Key := [(key2698, 1), (key2701, 1), (key2851, 1), (key2856, 1), (key2971, 1), (key2974, 1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1), (key2734, -2), (key2892, -2), (key2895, -2), (key2645, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2651, -2), (key2734, -2), (key2745, -2), (key2895, -2), (key2902, -2)]

def rawRow11742 : Integer.Sparse Key := [(key2701, 1), (key2698, 1), (key2856, 1), (key2851, 1), (key2974, 1), (key2971, 1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2892, -2), (key2651, -2), (key2645, -2), (key2745, -2), (key2734, -2), (key2902, -2), (key2895, -2)]

def rawRow11743 : Integer.Sparse Key := [(key2851, 1), (key2971, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2892, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2734, -2), (key2895, -2), (key2645, -2), (key2902, -2), (key2651, -2), (key2745, -2)]

def rawRow11744 : Integer.Sparse Key := [(key2971, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1), (key2892, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2895, -2), (key2734, -2), (key2902, -2), (key2645, -2), (key2745, -2), (key2651, -2)]

def rawRow11745 : Integer.Sparse Key := [(key2856, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2698, 1), (key2851, 1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, -2), (key2645, -2), (key2892, -2), (key2745, -2), (key2902, -2), (key2651, -2), (key2895, -2), (key2645, -2), (key2734, -2)]

def rawRow11746 : Integer.Sparse Key := [(key2974, 1), (key2856, 1), (key2971, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2895, -2), (key2892, -2), (key2734, -2), (key2902, -2), (key2892, -2), (key2645, -2), (key2902, -2), (key2745, -2), (key2895, -2), (key2651, -2), (key2734, -2), (key2645, -2)]

def rawRow11747 : Integer.Sparse Key := [(key2722, 1), (key2722, 1), (key2866, 1), (key2866, 1), (key2981, 1), (key2981, 1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2627, 1), (key2627, 1), (key2701, 1), (key2701, 1), (key2971, 1), (key2971, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1), (key2745, -2), (key2902, -2), (key2902, -2), (key2651, -2), (key2895, -2), (key2895, -2), (key2645, -2), (key2645, -2), (key2734, -2), (key2734, -2), (key2892, -2), (key2892, -2)]

def rawRow11748 : Integer.Sparse Key := [(key2866, 1), (key2981, 1), (key2722, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2902, -2), (key2745, -2), (key2902, -2), (key2895, -2), (key2651, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2645, -2), (key2892, -2), (key2645, -2), (key2734, -2)]

def rawRow11749 : Integer.Sparse Key := [(key2981, 1), (key2866, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2971, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2627, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1), (key2902, -2), (key2902, -2), (key2745, -2), (key2895, -2), (key2895, -2), (key2651, -2), (key2892, -2), (key2734, -2), (key2892, -2), (key2645, -2), (key2734, -2), (key2645, -2)]

def rawRow11750 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2801, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2804, -2), (key2825, -2), (key2947, -2), (key2947, -2), (key2958, -2), (key2624, 1), (key2627, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2636, 1), (key2698, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2722, 1), (key2851, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2866, 1), (key2971, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2974, 1), (key2981, 1)]

def rawRow11751 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2801, -2), (key2825, -2), (key2804, -2), (key2947, -2), (key2958, -2), (key2947, -2), (key2627, 1), (key2624, 1), (key2636, 1), (key2624, 1), (key2636, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2722, 1), (key2698, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2866, 1), (key2851, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2971, 1), (key2981, 1), (key2971, 1), (key2981, 1), (key2974, 1)]

def rawRow11752 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2825, -2), (key2825, -2), (key2804, -2), (key2804, -2), (key2801, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2947, -2), (key2636, 1), (key2636, 1), (key2627, 1), (key2627, 1), (key2624, 1), (key2624, 1), (key2722, 1), (key2722, 1), (key2701, 1), (key2701, 1), (key2698, 1), (key2698, 1), (key2866, 1), (key2866, 1), (key2856, 1), (key2856, 1), (key2851, 1), (key2851, 1), (key2981, 1), (key2981, 1), (key2974, 1), (key2974, 1), (key2971, 1), (key2971, 1)]

def rawRow11753 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2608, -2), (key2611, -2), (key2801, -2), (key2825, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2698, 1), (key2701, 1), (key2851, 1), (key2856, 1), (key2971, 1), (key2974, 1), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1)]

def rawRow11754 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2611, -2), (key2608, -2), (key2825, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2701, 1), (key2698, 1), (key2856, 1), (key2851, 1), (key2974, 1), (key2971, 1), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1)]

def rawRow11755 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2801, -2), (key2825, -2), (key2608, -2), (key2958, -2), (key2611, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2825, -2), (key2851, 1), (key2971, 1), (key2698, 1), (key2974, 1), (key2701, 1), (key2856, 1), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1)]

def rawRow11756 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2825, -2), (key2801, -2), (key2958, -2), (key2608, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2971, 1), (key2851, 1), (key2974, 1), (key2698, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1)]

def rawRow11757 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2825, -2), (key2608, -2), (key2801, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2856, 1), (key2974, 1), (key2701, 1), (key2971, 1), (key2698, 1), (key2851, 1), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1)]

def rawRow11758 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2958, -2), (key2947, -2), (key2825, -2), (key2611, -2), (key2801, -2), (key2608, -2), (key2825, -2), (key2804, -2), (key2611, -2), (key2974, 1), (key2856, 1), (key2971, 1), (key2701, 1), (key2851, 1), (key2698, 1), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

def rawRow11759 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2611, -2), (key2611, -2), (key2804, -2), (key2804, -2), (key2825, -2), (key2825, -2), (key2608, -2), (key2801, -2), (key2801, -2), (key2722, 1), (key2722, 1), (key2866, 1), (key2866, 1), (key2981, 1), (key2981, 1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2627, 1), (key2627, 1), (key2701, 1), (key2701, 1), (key2971, 1), (key2971, 1), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

def rawRow11760 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2801, -2), (key2608, -2), (key2801, -2), (key2866, 1), (key2981, 1), (key2722, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

def rawRow11761 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2825, -2), (key2804, -2), (key2825, -2), (key2611, -2), (key2804, -2), (key2611, -2), (key2801, -2), (key2801, -2), (key2608, -2), (key2981, 1), (key2866, 1), (key2981, 1), (key2722, 1), (key2866, 1), (key2722, 1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2971, 1), (key2701, 1), (key2971, 1), (key2627, 1), (key2701, 1), (key2627, 1), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

def rawRow11762 : Integer.Sparse Key := [(key2624, -2), (key2627, -2), (key2636, -2), (key2698, -2), (key2701, -2), (key2851, -2), (key2971, -2), (key2856, -2), (key2974, -2), (key2722, -2), (key2866, -2), (key2981, -2), (key2608, 1), (key2611, 1), (key2624, 1), (key2636, 1), (key2645, 1), (key2651, 1), (key2663, 1), (key2666, 1), (key2698, 1), (key2722, 1), (key2734, 1), (key2745, 1), (key2778, 1), (key2790, 1), (key2801, 1), (key2825, 1), (key2895, 1), (key2902, 1), (key2935, 1), (key2941, 1), (key2947, 1), (key2958, 1), (key2974, 1), (key2981, 1)]

def rawRow11763 : Integer.Sparse Key := [(key2627, -2), (key2624, -2), (key2636, -2), (key2701, -2), (key2698, -2), (key2971, -2), (key2851, -2), (key2974, -2), (key2856, -2), (key2722, -2), (key2981, -2), (key2866, -2), (key2611, 1), (key2608, 1), (key2636, 1), (key2624, 1), (key2651, 1), (key2645, 1), (key2666, 1), (key2663, 1), (key2722, 1), (key2698, 1), (key2745, 1), (key2734, 1), (key2790, 1), (key2778, 1), (key2825, 1), (key2801, 1), (key2902, 1), (key2895, 1), (key2941, 1), (key2935, 1), (key2958, 1), (key2947, 1), (key2981, 1), (key2974, 1)]

def rawRow11764 : Integer.Sparse Key := [(key2624, -2), (key2636, -2), (key2627, -2), (key2851, -2), (key2856, -2), (key2698, -2), (key2974, -2), (key2701, -2), (key2971, -2), (key2866, -2), (key2722, -2), (key2981, -2), (key2624, 1), (key2636, 1), (key2608, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2698, 1), (key2734, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2801, 1), (key2895, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2947, 1), (key2974, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2958, 1)]

def rawRow11765 : Integer.Sparse Key := [(key2636, -2), (key2624, -2), (key2627, -2), (key2856, -2), (key2851, -2), (key2974, -2), (key2698, -2), (key2971, -2), (key2701, -2), (key2866, -2), (key2981, -2), (key2722, -2), (key2636, 1), (key2624, 1), (key2651, 1), (key2608, 1), (key2636, 1), (key2611, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2722, 1), (key2666, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2825, 1), (key2790, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2958, 1), (key2941, 1)]

def rawRow11766 : Integer.Sparse Key := [(key2627, -2), (key2636, -2), (key2624, -2), (key2971, -2), (key2974, -2), (key2701, -2), (key2856, -2), (key2698, -2), (key2851, -2), (key2981, -2), (key2722, -2), (key2866, -2), (key2645, 1), (key2651, 1), (key2611, 1), (key2636, 1), (key2608, 1), (key2624, 1), (key2722, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2663, 1), (key2698, 1), (key2825, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2778, 1), (key2801, 1), (key2958, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2935, 1), (key2947, 1)]

def rawRow11767 : Integer.Sparse Key := [(key2636, -2), (key2627, -2), (key2624, -2), (key2974, -2), (key2971, -2), (key2856, -2), (key2701, -2), (key2851, -2), (key2698, -2), (key2981, -2), (key2866, -2), (key2722, -2), (key2651, 1), (key2645, 1), (key2636, 1), (key2611, 1), (key2624, 1), (key2608, 1), (key2745, 1), (key2722, 1), (key2734, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2902, 1), (key2825, 1), (key2895, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2958, 1), (key2974, 1), (key2941, 1), (key2947, 1), (key2935, 1)]

def rawRow11768 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2624, -2), (key2627, -2), (key2851, -2), (key2971, -2), (key2866, -2), (key2981, -2), (key2636, -2), (key2856, -2), (key2974, -2), (key2663, 1), (key2666, 1), (key2698, 1), (key2734, 1), (key2722, 1), (key2745, 1), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2722, 1), (key2974, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1)]

def rawRow11769 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2627, -2), (key2624, -2), (key2971, -2), (key2851, -2), (key2981, -2), (key2866, -2), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, 1), (key2663, 1), (key2734, 1), (key2698, 1), (key2745, 1), (key2722, 1), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2636, 1), (key2624, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2974, 1), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1)]

def rawRow11770 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2851, -2), (key2866, -2), (key2624, -2), (key2981, -2), (key2627, -2), (key2971, -2), (key2856, -2), (key2636, -2), (key2974, -2), (key2698, 1), (key2722, 1), (key2663, 1), (key2745, 1), (key2666, 1), (key2734, 1), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2698, 1), (key2974, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1)]

def rawRow11771 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2866, -2), (key2851, -2), (key2981, -2), (key2624, -2), (key2971, -2), (key2627, -2), (key2856, -2), (key2974, -2), (key2636, -2), (key2722, 1), (key2698, 1), (key2745, 1), (key2663, 1), (key2734, 1), (key2666, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2722, 1), (key2636, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1)]

def rawRow11772 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2971, -2), (key2981, -2), (key2627, -2), (key2866, -2), (key2624, -2), (key2851, -2), (key2974, -2), (key2636, -2), (key2856, -2), (key2734, 1), (key2745, 1), (key2666, 1), (key2722, 1), (key2663, 1), (key2698, 1), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2722, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2624, 1), (key2698, 1), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1)]

def rawRow11773 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2981, -2), (key2971, -2), (key2866, -2), (key2627, -2), (key2851, -2), (key2624, -2), (key2974, -2), (key2856, -2), (key2636, -2), (key2745, 1), (key2734, 1), (key2722, 1), (key2666, 1), (key2698, 1), (key2663, 1), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2981, 1), (key2722, 1), (key2974, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

def rawRow11774 : Integer.Sparse Key := [(key2851, -2), (key2856, -2), (key2866, -2), (key2624, -2), (key2636, -2), (key2698, -2), (key2974, -2), (key2722, -2), (key2981, -2), (key2627, -2), (key2701, -2), (key2971, -2), (key2778, 1), (key2790, 1), (key2801, 1), (key2895, 1), (key2825, 1), (key2902, 1), (key2624, 1), (key2636, 1), (key2698, 1), (key2974, 1), (key2722, 1), (key2981, 1), (key2608, 1), (key2651, 1), (key2663, 1), (key2745, 1), (key2941, 1), (key2958, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2722, 1), (key2790, 1), (key2825, 1)]

def rawRow11775 : Integer.Sparse Key := [(key2856, -2), (key2851, -2), (key2866, -2), (key2636, -2), (key2624, -2), (key2974, -2), (key2698, -2), (key2981, -2), (key2722, -2), (key2627, -2), (key2971, -2), (key2701, -2), (key2790, 1), (key2778, 1), (key2895, 1), (key2801, 1), (key2902, 1), (key2825, 1), (key2636, 1), (key2624, 1), (key2974, 1), (key2698, 1), (key2981, 1), (key2722, 1), (key2651, 1), (key2608, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2941, 1), (key2636, 1), (key2611, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2790, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11776 : Integer.Sparse Key := [(key2851, -2), (key2866, -2), (key2856, -2), (key2698, -2), (key2722, -2), (key2624, -2), (key2981, -2), (key2636, -2), (key2974, -2), (key2701, -2), (key2627, -2), (key2971, -2), (key2801, 1), (key2825, 1), (key2778, 1), (key2902, 1), (key2790, 1), (key2895, 1), (key2698, 1), (key2722, 1), (key2624, 1), (key2981, 1), (key2636, 1), (key2974, 1), (key2663, 1), (key2745, 1), (key2608, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2666, 1), (key2790, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2722, 1)]

def rawRow11777 : Integer.Sparse Key := [(key2866, -2), (key2851, -2), (key2856, -2), (key2722, -2), (key2698, -2), (key2981, -2), (key2624, -2), (key2974, -2), (key2636, -2), (key2701, -2), (key2971, -2), (key2627, -2), (key2825, 1), (key2801, 1), (key2902, 1), (key2778, 1), (key2895, 1), (key2790, 1), (key2722, 1), (key2698, 1), (key2981, 1), (key2624, 1), (key2974, 1), (key2636, 1), (key2745, 1), (key2663, 1), (key2958, 1), (key2608, 1), (key2745, 1), (key2651, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2722, 1), (key2636, 1)]

def rawRow11778 : Integer.Sparse Key := [(key2856, -2), (key2866, -2), (key2851, -2), (key2974, -2), (key2981, -2), (key2636, -2), (key2722, -2), (key2624, -2), (key2698, -2), (key2971, -2), (key2627, -2), (key2701, -2), (key2895, 1), (key2902, 1), (key2790, 1), (key2825, 1), (key2778, 1), (key2801, 1), (key2974, 1), (key2981, 1), (key2636, 1), (key2722, 1), (key2624, 1), (key2698, 1), (key2941, 1), (key2958, 1), (key2651, 1), (key2745, 1), (key2608, 1), (key2663, 1), (key2722, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2611, 1), (key2666, 1)]

def rawRow11779 : Integer.Sparse Key := [(key2866, -2), (key2856, -2), (key2851, -2), (key2981, -2), (key2974, -2), (key2722, -2), (key2636, -2), (key2698, -2), (key2624, -2), (key2971, -2), (key2701, -2), (key2627, -2), (key2902, 1), (key2895, 1), (key2825, 1), (key2790, 1), (key2801, 1), (key2778, 1), (key2981, 1), (key2974, 1), (key2722, 1), (key2636, 1), (key2698, 1), (key2624, 1), (key2958, 1), (key2941, 1), (key2745, 1), (key2651, 1), (key2663, 1), (key2608, 1), (key2825, 1), (key2722, 1), (key2790, 1), (key2636, 1), (key2666, 1), (key2611, 1)]

def rawRow11780 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2627, -2), (key2636, -2), (key2701, -2), (key2856, -2), (key2722, -2), (key2866, -2), (key2624, -2), (key2698, -2), (key2851, -2), (key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2611, 1), (key2636, 1), (key2666, 1), (key2790, 1), (key2722, 1), (key2825, 1), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

def rawRow11781 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2636, -2), (key2627, -2), (key2856, -2), (key2701, -2), (key2866, -2), (key2722, -2), (key2624, -2), (key2851, -2), (key2698, -2), (key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2636, 1), (key2611, 1), (key2790, 1), (key2666, 1), (key2825, 1), (key2722, 1), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

def rawRow11782 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2701, -2), (key2722, -2), (key2627, -2), (key2866, -2), (key2636, -2), (key2856, -2), (key2698, -2), (key2624, -2), (key2851, -2), (key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2666, 1), (key2722, 1), (key2611, 1), (key2825, 1), (key2636, 1), (key2790, 1), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

def rawRow11783 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2722, -2), (key2701, -2), (key2866, -2), (key2627, -2), (key2856, -2), (key2636, -2), (key2698, -2), (key2851, -2), (key2624, -2), (key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2722, 1), (key2666, 1), (key2825, 1), (key2611, 1), (key2790, 1), (key2636, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

def rawRow11784 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2856, -2), (key2866, -2), (key2636, -2), (key2722, -2), (key2627, -2), (key2701, -2), (key2851, -2), (key2624, -2), (key2698, -2), (key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2790, 1), (key2825, 1), (key2636, 1), (key2722, 1), (key2611, 1), (key2666, 1), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

def rawRow11785 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2866, -2), (key2856, -2), (key2722, -2), (key2636, -2), (key2701, -2), (key2627, -2), (key2851, -2), (key2698, -2), (key2624, -2), (key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2825, 1), (key2790, 1), (key2722, 1), (key2636, 1), (key2666, 1), (key2611, 1), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

def rawRow11786 : Integer.Sparse Key := [(key2457, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2525, 2), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2564, -2)]

def rawRow11787 : Integer.Sparse Key := [(key2460, 2), (key2457, 2), (key2460, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2564, -2), (key2533, -2), (key2564, -2)]

def rawRow11788 : Integer.Sparse Key := [(key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2521, 2), (key2457, 2), (key2525, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2460, 2), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2564, -2), (key2564, -2), (key2533, -2)]

def rawRow11789 : Integer.Sparse Key := [(key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2525, 2), (key2457, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2521, 2), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2564, -2), (key2532, -2), (key2532, -2), (key2562, -2)]

def rawRow11790 : Integer.Sparse Key := [(key2521, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2521, 2), (key2457, 2), (key2521, 2), (key2460, 2), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, -2), (key2532, -2), (key2564, -2), (key2532, -2), (key2564, -2), (key2533, -2), (key2532, -2), (key2562, -2), (key2532, -2)]

def rawRow11791 : Integer.Sparse Key := [(key2525, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2460, 2), (key2521, 2), (key2521, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2457, 2), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, -2), (key2564, -2), (key2533, -2), (key2533, -2), (key2532, -2), (key2532, -2), (key2562, -2), (key2532, -2), (key2532, -2)]

def rawRow11864 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2411, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2437, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2443, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2509, 1), (key2509, 1), (key2524, 1), (key2524, 1)]

def rawRow11865 : Integer.Sparse Key := [(key2406, -2), (key2411, -2), (key2406, -2), (key2437, -2), (key2443, -2), (key2406, -2), (key2443, -2), (key2406, -2), (key2437, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2480, 1), (key2484, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2484, 1), (key2509, 1)]

def rawRow11866 : Integer.Sparse Key := [(key2411, -2), (key2406, -2), (key2406, -2), (key2443, -2), (key2437, -2), (key2443, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2484, 1), (key2480, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2484, 1)]

def rawRow11867 : Integer.Sparse Key := [(key2437, -2), (key2443, -2), (key2443, -2), (key2406, -2), (key2411, -2), (key2406, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2503, 1), (key2509, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1)]

def rawRow11868 : Integer.Sparse Key := [(key2443, -2), (key2437, -2), (key2443, -2), (key2411, -2), (key2406, -2), (key2443, -2), (key2406, -2), (key2443, -2), (key2411, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2509, 1), (key2503, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1)]

def rawRow11869 : Integer.Sparse Key := [(key2443, -2), (key2443, -2), (key2437, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2411, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2406, -2), (key2524, 1), (key2524, 1), (key2509, 1), (key2509, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1), (key2509, 1), (key2509, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1)]

def rawRow11870 : Integer.Sparse Key := [(key2587, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2843, -2), (key2966, -2), (key2966, -2), (key2968, -2), (key2968, -2), (key2880, -2), (key2989, -2), (key2989, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2571, 1), (key2571, 1), (key2576, 1), (key2576, 1), (key2580, 1), (key2580, 1)]

def rawRow11871 : Integer.Sparse Key := [(key2587, -2), (key2593, -2), (key2587, -2), (key2966, -2), (key2968, -2), (key2843, -2), (key2968, -2), (key2843, -2), (key2966, -2), (key2989, -2), (key2880, -2), (key2989, -2), (key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2580, 1), (key2571, 1), (key2576, 1)]

def rawRow11872 : Integer.Sparse Key := [(key2593, -2), (key2587, -2), (key2587, -2), (key2968, -2), (key2966, -2), (key2968, -2), (key2843, -2), (key2966, -2), (key2843, -2), (key2989, -2), (key2989, -2), (key2880, -2), (key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2580, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2571, 1)]

def rawRow11873 : Integer.Sparse Key := [(key2843, -2), (key2843, -2), (key2880, -2), (key2587, -2), (key2587, -2), (key2966, -2), (key2966, -2), (key2989, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2968, -2), (key2766, 1), (key2766, 1), (key2887, 1), (key2887, 1), (key2910, 1), (key2910, 1), (key2587, 1), (key2587, 1), (key2966, 1), (key2966, 1), (key2989, 1), (key2989, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2580, 1), (key2580, 1), (key2394, 1), (key2394, 1), (key2443, 1), (key2443, 1), (key2524, 1), (key2524, 1)]

def rawRow11874 : Integer.Sparse Key := [(key2843, -2), (key2880, -2), (key2843, -2), (key2966, -2), (key2989, -2), (key2587, -2), (key2989, -2), (key2587, -2), (key2966, -2), (key2968, -2), (key2593, -2), (key2968, -2), (key2887, 1), (key2910, 1), (key2766, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key3002, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2524, 1), (key2394, 1), (key2443, 1)]

def rawRow11875 : Integer.Sparse Key := [(key2880, -2), (key2843, -2), (key2843, -2), (key2989, -2), (key2966, -2), (key2989, -2), (key2587, -2), (key2966, -2), (key2587, -2), (key2968, -2), (key2968, -2), (key2593, -2), (key2910, 1), (key2887, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2766, 1), (key2989, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2587, 1), (key3002, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key2437, 1), (key2390, 1), (key2524, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2394, 1)]

def rawRow11876 : Integer.Sparse Key := [(key2966, -2), (key2968, -2), (key2989, -2), (key2587, -2), (key2593, -2), (key2843, -2), (key2968, -2), (key2880, -2), (key2989, -2), (key2587, -2), (key2843, -2), (key2966, -2), (key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1), (key2587, 1), (key2600, 1), (key2766, 1), (key2931, 1), (key2910, 1), (key2989, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1)]

def rawRow11877 : Integer.Sparse Key := [(key2968, -2), (key2966, -2), (key2989, -2), (key2593, -2), (key2587, -2), (key2968, -2), (key2843, -2), (key2989, -2), (key2880, -2), (key2587, -2), (key2966, -2), (key2843, -2), (key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1), (key2600, 1), (key2587, 1), (key2931, 1), (key2766, 1), (key2989, 1), (key2910, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1)]

def rawRow11878 : Integer.Sparse Key := [(key2966, -2), (key2989, -2), (key2968, -2), (key2843, -2), (key2880, -2), (key2587, -2), (key2989, -2), (key2593, -2), (key2968, -2), (key2843, -2), (key2587, -2), (key2966, -2), (key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2766, 1), (key2910, 1), (key2587, 1), (key2989, 1), (key2600, 1), (key2931, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1)]

def rawRow11879 : Integer.Sparse Key := [(key2989, -2), (key2966, -2), (key2968, -2), (key2880, -2), (key2843, -2), (key2989, -2), (key2587, -2), (key2968, -2), (key2593, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1), (key2910, 1), (key2766, 1), (key2989, 1), (key2587, 1), (key2931, 1), (key2600, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1)]

def rawRow11880 : Integer.Sparse Key := [(key2968, -2), (key2989, -2), (key2966, -2), (key2968, -2), (key2989, -2), (key2593, -2), (key2880, -2), (key2587, -2), (key2843, -2), (key2966, -2), (key2587, -2), (key2843, -2), (key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1), (key2931, 1), (key2989, 1), (key2600, 1), (key2910, 1), (key2587, 1), (key2766, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1)]

def rawRow11881 : Integer.Sparse Key := [(key2989, -2), (key2968, -2), (key2966, -2), (key2989, -2), (key2968, -2), (key2880, -2), (key2593, -2), (key2843, -2), (key2587, -2), (key2966, -2), (key2843, -2), (key2587, -2), (key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1), (key2989, 1), (key2931, 1), (key2910, 1), (key2600, 1), (key2766, 1), (key2587, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

def rawRow11900 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2383, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2390, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2394, -2), (key2406, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2443, 2)]

def rawRow11901 : Integer.Sparse Key := [(key2378, -2), (key2383, -2), (key2378, -2), (key2390, -2), (key2394, -2), (key2378, -2), (key2394, -2), (key2378, -2), (key2390, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2406, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2443, 2)]

def rawRow11902 : Integer.Sparse Key := [(key2383, -2), (key2378, -2), (key2378, -2), (key2394, -2), (key2390, -2), (key2394, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2411, 2), (key2406, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2443, 2), (key2411, 2)]

def rawRow11903 : Integer.Sparse Key := [(key2390, -2), (key2394, -2), (key2394, -2), (key2378, -2), (key2383, -2), (key2378, -2), (key2394, -2), (key2383, -2), (key2394, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2437, 2), (key2443, 2), (key2443, 2), (key2406, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2406, 2), (key2406, 2), (key2437, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block117
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11904 : Integer.Sparse Key := [(key2394, -2), (key2390, -2), (key2394, -2), (key2383, -2), (key2378, -2), (key2394, -2), (key2378, -2), (key2394, -2), (key2383, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2443, 2), (key2437, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2443, 2), (key2406, 2), (key2443, 2), (key2411, 2), (key2406, 2), (key2437, 2), (key2406, 2)]

def rawRow11905 : Integer.Sparse Key := [(key2394, -2), (key2394, -2), (key2390, -2), (key2394, -2), (key2394, -2), (key2383, -2), (key2383, -2), (key2378, -2), (key2378, -2), (key2390, -2), (key2378, -2), (key2378, -2), (key2443, 2), (key2443, 2), (key2437, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2411, 2), (key2406, 2), (key2406, 2), (key2437, 2), (key2406, 2), (key2406, 2)]

def rawRow11906 : Integer.Sparse Key := [(key2766, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2843, -2), (key2887, -2), (key2887, -2), (key2889, -2), (key2889, -2), (key2880, -2), (key2910, -2), (key2910, -2), (key2587, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2843, 2), (key2966, 2), (key2966, 2), (key2968, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2989, 2)]

def rawRow11907 : Integer.Sparse Key := [(key2766, -2), (key2772, -2), (key2766, -2), (key2887, -2), (key2889, -2), (key2843, -2), (key2889, -2), (key2843, -2), (key2887, -2), (key2910, -2), (key2880, -2), (key2910, -2), (key2587, 2), (key2593, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2880, 2), (key2989, 2)]

def rawRow11908 : Integer.Sparse Key := [(key2772, -2), (key2766, -2), (key2766, -2), (key2889, -2), (key2887, -2), (key2889, -2), (key2843, -2), (key2887, -2), (key2843, -2), (key2910, -2), (key2910, -2), (key2880, -2), (key2593, 2), (key2587, 2), (key2587, 2), (key2968, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2843, 2), (key2989, 2), (key2989, 2), (key2880, 2)]

def rawRow11909 : Integer.Sparse Key := [(key2843, -2), (key2843, -2), (key2880, -2), (key2766, -2), (key2766, -2), (key2887, -2), (key2887, -2), (key2910, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2889, -2), (key2843, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2587, 2), (key2966, 2), (key2966, 2), (key2989, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2968, 2)]

def rawRow11910 : Integer.Sparse Key := [(key2843, -2), (key2880, -2), (key2843, -2), (key2887, -2), (key2910, -2), (key2766, -2), (key2910, -2), (key2766, -2), (key2887, -2), (key2889, -2), (key2772, -2), (key2889, -2), (key2843, 2), (key2880, 2), (key2843, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2968, 2), (key2593, 2), (key2968, 2)]

def rawRow11911 : Integer.Sparse Key := [(key2880, -2), (key2843, -2), (key2843, -2), (key2910, -2), (key2887, -2), (key2910, -2), (key2766, -2), (key2887, -2), (key2766, -2), (key2889, -2), (key2889, -2), (key2772, -2), (key2880, 2), (key2843, 2), (key2843, 2), (key2989, 2), (key2966, 2), (key2989, 2), (key2587, 2), (key2966, 2), (key2587, 2), (key2968, 2), (key2968, 2), (key2593, 2)]

def rawRow11912 : Integer.Sparse Key := [(key2887, -2), (key2889, -2), (key2910, -2), (key2766, -2), (key2772, -2), (key2843, -2), (key2889, -2), (key2880, -2), (key2910, -2), (key2766, -2), (key2843, -2), (key2887, -2), (key2966, 2), (key2968, 2), (key2989, 2), (key2587, 2), (key2593, 2), (key2843, 2), (key2968, 2), (key2880, 2), (key2989, 2), (key2587, 2), (key2843, 2), (key2966, 2)]

def rawRow11913 : Integer.Sparse Key := [(key2889, -2), (key2887, -2), (key2910, -2), (key2772, -2), (key2766, -2), (key2889, -2), (key2843, -2), (key2910, -2), (key2880, -2), (key2766, -2), (key2887, -2), (key2843, -2), (key2968, 2), (key2966, 2), (key2989, 2), (key2593, 2), (key2587, 2), (key2968, 2), (key2843, 2), (key2989, 2), (key2880, 2), (key2587, 2), (key2966, 2), (key2843, 2)]

def rawRow11914 : Integer.Sparse Key := [(key2887, -2), (key2910, -2), (key2889, -2), (key2843, -2), (key2880, -2), (key2766, -2), (key2910, -2), (key2772, -2), (key2889, -2), (key2843, -2), (key2766, -2), (key2887, -2), (key2966, 2), (key2989, 2), (key2968, 2), (key2843, 2), (key2880, 2), (key2587, 2), (key2989, 2), (key2593, 2), (key2968, 2), (key2843, 2), (key2587, 2), (key2966, 2)]

def rawRow11915 : Integer.Sparse Key := [(key2910, -2), (key2887, -2), (key2889, -2), (key2880, -2), (key2843, -2), (key2910, -2), (key2766, -2), (key2889, -2), (key2772, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2989, 2), (key2966, 2), (key2968, 2), (key2880, 2), (key2843, 2), (key2989, 2), (key2587, 2), (key2968, 2), (key2593, 2), (key2843, 2), (key2966, 2), (key2587, 2)]

def rawRow11916 : Integer.Sparse Key := [(key2889, -2), (key2910, -2), (key2887, -2), (key2889, -2), (key2910, -2), (key2772, -2), (key2880, -2), (key2766, -2), (key2843, -2), (key2887, -2), (key2766, -2), (key2843, -2), (key2968, 2), (key2989, 2), (key2966, 2), (key2968, 2), (key2989, 2), (key2593, 2), (key2880, 2), (key2587, 2), (key2843, 2), (key2966, 2), (key2587, 2), (key2843, 2)]

def rawRow11917 : Integer.Sparse Key := [(key2910, -2), (key2889, -2), (key2887, -2), (key2910, -2), (key2889, -2), (key2880, -2), (key2772, -2), (key2843, -2), (key2766, -2), (key2887, -2), (key2843, -2), (key2766, -2), (key2989, 2), (key2968, 2), (key2966, 2), (key2989, 2), (key2968, 2), (key2880, 2), (key2593, 2), (key2843, 2), (key2587, 2), (key2966, 2), (key2843, 2), (key2587, 2)]

def rawRow11918 : Integer.Sparse Key := [(key1531, -2), (key1531, -2), (key1536, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1765, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1768, -2), (key1609, 1), (key1609, 1), (key1648, 1), (key1648, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1809, 1), (key1809, 1), (key1648, 1), (key1648, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1809, 1), (key1809, 1), (key1837, 1), (key1837, 1)]

def rawRow11919 : Integer.Sparse Key := [(key1531, -2), (key1536, -2), (key1531, -2), (key1765, -2), (key1768, -2), (key1531, -2), (key1768, -2), (key1531, -2), (key1765, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1648, 1), (key1651, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1651, 1), (key1809, 1)]

def rawRow11920 : Integer.Sparse Key := [(key1536, -2), (key1531, -2), (key1531, -2), (key1768, -2), (key1765, -2), (key1768, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1651, 1), (key1648, 1), (key1651, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1809, 1), (key1806, 1), (key1809, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1648, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1651, 1), (key1809, 1), (key1651, 1)]

def rawRow11921 : Integer.Sparse Key := [(key1765, -2), (key1768, -2), (key1768, -2), (key1531, -2), (key1536, -2), (key1531, -2), (key1768, -2), (key1536, -2), (key1768, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1806, 1), (key1809, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1837, 1), (key1648, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1837, 1), (key1609, 1), (key1651, 1), (key1609, 1), (key1809, 1), (key1651, 1), (key1809, 1), (key1609, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1648, 1), (key1806, 1)]

def rawRow11922 : Integer.Sparse Key := [(key1768, -2), (key1765, -2), (key1768, -2), (key1536, -2), (key1531, -2), (key1768, -2), (key1531, -2), (key1768, -2), (key1536, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1809, 1), (key1806, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1809, 1), (key1651, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1809, 1), (key1609, 1), (key1809, 1), (key1651, 1), (key1648, 1), (key1609, 1), (key1806, 1), (key1609, 1), (key1806, 1), (key1648, 1)]

def rawRow11923 : Integer.Sparse Key := [(key1768, -2), (key1768, -2), (key1765, -2), (key1768, -2), (key1768, -2), (key1536, -2), (key1536, -2), (key1531, -2), (key1531, -2), (key1765, -2), (key1531, -2), (key1531, -2), (key1837, 1), (key1837, 1), (key1809, 1), (key1809, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1651, 1), (key1651, 1), (key1648, 1), (key1648, 1), (key1809, 1), (key1809, 1), (key1651, 1), (key1651, 1), (key1609, 1), (key1609, 1), (key1806, 1), (key1806, 1), (key1648, 1), (key1648, 1), (key1609, 1), (key1609, 1)]

def rawRow11924 : Integer.Sparse Key := [(key1256, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1609, -2), (key1806, -2), (key1806, -2), (key1809, -2), (key1809, -2), (key1642, -2), (key1832, -2), (key1832, -2), (key1256, 1), (key1256, 1), (key1265, 1), (key1265, 1), (key1268, 1), (key1268, 1), (key1531, 1), (key1531, 1), (key1765, 1), (key1765, 1), (key1768, 1), (key1768, 1), (key1648, 1), (key1648, 1), (key1806, 1), (key1806, 1), (key1837, 1), (key1837, 1), (key1674, 1), (key1674, 1), (key1832, 1), (key1832, 1), (key1848, 1), (key1848, 1)]

def rawRow11925 : Integer.Sparse Key := [(key1256, -2), (key1261, -2), (key1256, -2), (key1806, -2), (key1809, -2), (key1609, -2), (key1809, -2), (key1609, -2), (key1806, -2), (key1832, -2), (key1642, -2), (key1832, -2), (key1265, 1), (key1268, 1), (key1256, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1848, 1), (key1674, 1), (key1832, 1)]

def rawRow11926 : Integer.Sparse Key := [(key1261, -2), (key1256, -2), (key1256, -2), (key1809, -2), (key1806, -2), (key1809, -2), (key1609, -2), (key1806, -2), (key1609, -2), (key1832, -2), (key1832, -2), (key1642, -2), (key1268, 1), (key1265, 1), (key1268, 1), (key1256, 1), (key1265, 1), (key1256, 1), (key1768, 1), (key1765, 1), (key1768, 1), (key1531, 1), (key1765, 1), (key1531, 1), (key1837, 1), (key1806, 1), (key1837, 1), (key1648, 1), (key1806, 1), (key1648, 1), (key1848, 1), (key1832, 1), (key1848, 1), (key1674, 1), (key1832, 1), (key1674, 1)]

def rawRow11927 : Integer.Sparse Key := [(key1609, -2), (key1609, -2), (key1642, -2), (key1256, -2), (key1256, -2), (key1806, -2), (key1806, -2), (key1832, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1809, -2), (key1531, 1), (key1531, 1), (key1648, 1), (key1648, 1), (key1674, 1), (key1674, 1), (key1256, 1), (key1256, 1), (key1806, 1), (key1806, 1), (key1832, 1), (key1832, 1), (key1265, 1), (key1265, 1), (key1765, 1), (key1765, 1), (key1848, 1), (key1848, 1), (key1268, 1), (key1268, 1), (key1768, 1), (key1768, 1), (key1837, 1), (key1837, 1)]

def rawRow11928 : Integer.Sparse Key := [(key1609, -2), (key1642, -2), (key1609, -2), (key1806, -2), (key1832, -2), (key1256, -2), (key1832, -2), (key1256, -2), (key1806, -2), (key1809, -2), (key1261, -2), (key1809, -2), (key1648, 1), (key1674, 1), (key1531, 1), (key1674, 1), (key1531, 1), (key1648, 1), (key1806, 1), (key1832, 1), (key1256, 1), (key1832, 1), (key1256, 1), (key1806, 1), (key1765, 1), (key1848, 1), (key1265, 1), (key1848, 1), (key1265, 1), (key1765, 1), (key1768, 1), (key1837, 1), (key1268, 1), (key1837, 1), (key1268, 1), (key1768, 1)]

def rawRow11929 : Integer.Sparse Key := [(key1642, -2), (key1609, -2), (key1609, -2), (key1832, -2), (key1806, -2), (key1832, -2), (key1256, -2), (key1806, -2), (key1256, -2), (key1809, -2), (key1809, -2), (key1261, -2), (key1674, 1), (key1648, 1), (key1674, 1), (key1531, 1), (key1648, 1), (key1531, 1), (key1832, 1), (key1806, 1), (key1832, 1), (key1256, 1), (key1806, 1), (key1256, 1), (key1848, 1), (key1765, 1), (key1848, 1), (key1265, 1), (key1765, 1), (key1265, 1), (key1837, 1), (key1768, 1), (key1837, 1), (key1268, 1), (key1768, 1), (key1268, 1)]

def rawRow11930 : Integer.Sparse Key := [(key1806, -2), (key1809, -2), (key1832, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1809, -2), (key1642, -2), (key1832, -2), (key1256, -2), (key1609, -2), (key1806, -2), (key1765, 1), (key1768, 1), (key1806, 1), (key1837, 1), (key1832, 1), (key1848, 1), (key1265, 1), (key1268, 1), (key1648, 1), (key1837, 1), (key1674, 1), (key1848, 1), (key1256, 1), (key1268, 1), (key1531, 1), (key1768, 1), (key1674, 1), (key1832, 1), (key1256, 1), (key1265, 1), (key1531, 1), (key1765, 1), (key1648, 1), (key1806, 1)]

def rawRow11931 : Integer.Sparse Key := [(key1809, -2), (key1806, -2), (key1832, -2), (key1261, -2), (key1256, -2), (key1809, -2), (key1609, -2), (key1832, -2), (key1642, -2), (key1256, -2), (key1806, -2), (key1609, -2), (key1768, 1), (key1765, 1), (key1837, 1), (key1806, 1), (key1848, 1), (key1832, 1), (key1268, 1), (key1265, 1), (key1837, 1), (key1648, 1), (key1848, 1), (key1674, 1), (key1268, 1), (key1256, 1), (key1768, 1), (key1531, 1), (key1832, 1), (key1674, 1), (key1265, 1), (key1256, 1), (key1765, 1), (key1531, 1), (key1806, 1), (key1648, 1)]

def rawRow11932 : Integer.Sparse Key := [(key1806, -2), (key1832, -2), (key1809, -2), (key1609, -2), (key1642, -2), (key1256, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1609, -2), (key1256, -2), (key1806, -2), (key1806, 1), (key1832, 1), (key1765, 1), (key1848, 1), (key1768, 1), (key1837, 1), (key1648, 1), (key1674, 1), (key1265, 1), (key1848, 1), (key1268, 1), (key1837, 1), (key1531, 1), (key1674, 1), (key1256, 1), (key1832, 1), (key1268, 1), (key1768, 1), (key1531, 1), (key1648, 1), (key1256, 1), (key1806, 1), (key1265, 1), (key1765, 1)]

def rawRow11933 : Integer.Sparse Key := [(key1832, -2), (key1806, -2), (key1809, -2), (key1642, -2), (key1609, -2), (key1832, -2), (key1256, -2), (key1809, -2), (key1261, -2), (key1609, -2), (key1806, -2), (key1256, -2), (key1832, 1), (key1806, 1), (key1848, 1), (key1765, 1), (key1837, 1), (key1768, 1), (key1674, 1), (key1648, 1), (key1848, 1), (key1265, 1), (key1837, 1), (key1268, 1), (key1674, 1), (key1531, 1), (key1832, 1), (key1256, 1), (key1768, 1), (key1268, 1), (key1648, 1), (key1531, 1), (key1806, 1), (key1256, 1), (key1765, 1), (key1265, 1)]

def rawRow11934 : Integer.Sparse Key := [(key1809, -2), (key1832, -2), (key1806, -2), (key1809, -2), (key1832, -2), (key1261, -2), (key1642, -2), (key1256, -2), (key1609, -2), (key1806, -2), (key1256, -2), (key1609, -2), (key1837, 1), (key1848, 1), (key1768, 1), (key1832, 1), (key1765, 1), (key1806, 1), (key1837, 1), (key1848, 1), (key1268, 1), (key1674, 1), (key1265, 1), (key1648, 1), (key1768, 1), (key1832, 1), (key1268, 1), (key1674, 1), (key1256, 1), (key1531, 1), (key1765, 1), (key1806, 1), (key1265, 1), (key1648, 1), (key1256, 1), (key1531, 1)]

def rawRow11935 : Integer.Sparse Key := [(key1832, -2), (key1809, -2), (key1806, -2), (key1832, -2), (key1809, -2), (key1642, -2), (key1261, -2), (key1609, -2), (key1256, -2), (key1806, -2), (key1609, -2), (key1256, -2), (key1848, 1), (key1837, 1), (key1832, 1), (key1768, 1), (key1806, 1), (key1765, 1), (key1848, 1), (key1837, 1), (key1674, 1), (key1268, 1), (key1648, 1), (key1265, 1), (key1832, 1), (key1768, 1), (key1674, 1), (key1268, 1), (key1531, 1), (key1256, 1), (key1806, 1), (key1765, 1), (key1648, 1), (key1265, 1), (key1531, 1), (key1256, 1)]

def rawRow11936 : Integer.Sparse Key := [(key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2509, 1), (key2509, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2509, 1), (key2509, 1), (key2524, 1), (key2524, 1), (key2569, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2571, -2), (key2571, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2580, -2)]

def rawRow11937 : Integer.Sparse Key := [(key2480, 1), (key2484, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2571, -2), (key2569, -2), (key2571, -2), (key2576, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2580, -2), (key2571, -2), (key2576, -2)]

def rawRow11938 : Integer.Sparse Key := [(key2484, 1), (key2480, 1), (key2484, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2509, 1), (key2503, 1), (key2509, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2484, 1), (key2509, 1), (key2484, 1), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2576, -2), (key2569, -2), (key2580, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2576, -2), (key2571, -2)]

def rawRow11939 : Integer.Sparse Key := [(key2503, 1), (key2509, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2524, 1), (key2480, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2524, 1), (key2472, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2509, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2580, -2), (key2569, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2571, -2), (key2576, -2)]

def rawRow11940 : Integer.Sparse Key := [(key2509, 1), (key2503, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2509, 1), (key2472, 1), (key2509, 1), (key2484, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2576, -2), (key2580, -2), (key2576, -2), (key2571, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2576, -2), (key2569, -2), (key2576, -2), (key2571, -2)]

def rawRow11941 : Integer.Sparse Key := [(key2524, 1), (key2524, 1), (key2509, 1), (key2509, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2484, 1), (key2484, 1), (key2480, 1), (key2480, 1), (key2509, 1), (key2509, 1), (key2484, 1), (key2484, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1), (key2580, -2), (key2576, -2), (key2576, -2), (key2580, -2), (key2571, -2), (key2571, -2), (key2576, -2), (key2576, -2), (key2571, -2), (key2571, -2), (key2569, -2), (key2569, -2)]

def rawRow11942 : Integer.Sparse Key := [(key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2394, 1), (key2394, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2443, 1), (key2443, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2524, 1), (key2524, 1), (key2571, 1), (key2571, 1), (key2576, 1), (key2576, 1), (key2580, 1), (key2580, 1), (key2383, -2), (key2394, -2), (key2394, -2), (key2411, -2), (key2443, -2), (key2443, -2), (key2484, -2), (key2484, -2), (key2509, -2), (key2509, -2), (key2524, -2), (key2524, -2)]

def rawRow11943 : Integer.Sparse Key := [(key2390, 1), (key2394, 1), (key2378, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2394, -2), (key2383, -2), (key2394, -2), (key2443, -2), (key2411, -2), (key2443, -2), (key2509, -2), (key2524, -2), (key2484, -2), (key2524, -2), (key2484, -2), (key2509, -2)]

def rawRow11944 : Integer.Sparse Key := [(key2394, 1), (key2390, 1), (key2394, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2443, 1), (key2437, 1), (key2443, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2524, 1), (key2503, 1), (key2524, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2580, 1), (key2576, 1), (key2580, 1), (key2571, 1), (key2576, 1), (key2571, 1), (key2394, -2), (key2394, -2), (key2383, -2), (key2443, -2), (key2443, -2), (key2411, -2), (key2524, -2), (key2509, -2), (key2524, -2), (key2484, -2), (key2509, -2), (key2484, -2)]

def rawRow11945 : Integer.Sparse Key := [(key2766, 1), (key2766, 1), (key2887, 1), (key2887, 1), (key2910, 1), (key2910, 1), (key2587, 1), (key2587, 1), (key2966, 1), (key2966, 1), (key2989, 1), (key2989, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2580, 1), (key2580, 1), (key2394, 1), (key2394, 1), (key2443, 1), (key2443, 1), (key2524, 1), (key2524, 1), (key2411, -2), (key2484, -2), (key2484, -2), (key2383, -2), (key2509, -2), (key2509, -2), (key2394, -2), (key2394, -2), (key2443, -2), (key2443, -2), (key2524, -2), (key2524, -2)]

def rawRow11946 : Integer.Sparse Key := [(key2887, 1), (key2910, 1), (key2766, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key3002, 1), (key2390, 1), (key2437, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2484, -2), (key2411, -2), (key2484, -2), (key2509, -2), (key2383, -2), (key2509, -2), (key2443, -2), (key2524, -2), (key2394, -2), (key2524, -2), (key2394, -2), (key2443, -2)]

def rawRow11947 : Integer.Sparse Key := [(key2910, 1), (key2887, 1), (key2910, 1), (key2766, 1), (key2887, 1), (key2766, 1), (key2989, 1), (key2966, 1), (key2989, 1), (key2587, 1), (key2966, 1), (key2587, 1), (key3002, 1), (key2929, 1), (key3002, 1), (key2598, 1), (key2437, 1), (key2390, 1), (key2524, 1), (key2443, 1), (key2524, 1), (key2394, 1), (key2443, 1), (key2394, 1), (key2484, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2509, -2), (key2383, -2), (key2524, -2), (key2443, -2), (key2524, -2), (key2394, -2), (key2443, -2), (key2394, -2)]

def rawRow11948 : Integer.Sparse Key := [(key2929, 1), (key2931, 1), (key2966, 1), (key2995, 1), (key2989, 1), (key3002, 1), (key2598, 1), (key2600, 1), (key2887, 1), (key2995, 1), (key2910, 1), (key3002, 1), (key2587, 1), (key2600, 1), (key2766, 1), (key2931, 1), (key2910, 1), (key2989, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2443, -2), (key2509, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2524, -2), (key2383, -2), (key2394, -2), (key2411, -2), (key2443, -2), (key2484, -2), (key2509, -2)]

def rawRow11949 : Integer.Sparse Key := [(key2931, 1), (key2929, 1), (key2995, 1), (key2966, 1), (key3002, 1), (key2989, 1), (key2600, 1), (key2598, 1), (key2995, 1), (key2887, 1), (key3002, 1), (key2910, 1), (key2600, 1), (key2587, 1), (key2931, 1), (key2766, 1), (key2989, 1), (key2910, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1), (key2443, -2), (key2524, -2), (key2509, -2), (key2394, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2383, -2), (key2443, -2), (key2411, -2), (key2509, -2), (key2484, -2)]

def rawRow11950 : Integer.Sparse Key := [(key2966, 1), (key2989, 1), (key2929, 1), (key3002, 1), (key2931, 1), (key2995, 1), (key2887, 1), (key2910, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2766, 1), (key2910, 1), (key2587, 1), (key2989, 1), (key2600, 1), (key2931, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2509, -2), (key2443, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2524, -2), (key2411, -2), (key2484, -2), (key2383, -2), (key2509, -2), (key2394, -2), (key2443, -2)]

def rawRow11951 : Integer.Sparse Key := [(key2989, 1), (key2966, 1), (key3002, 1), (key2929, 1), (key2995, 1), (key2931, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2995, 1), (key2600, 1), (key2910, 1), (key2766, 1), (key2989, 1), (key2587, 1), (key2931, 1), (key2600, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1), (key2509, -2), (key2524, -2), (key2443, -2), (key2484, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2411, -2), (key2509, -2), (key2383, -2), (key2443, -2), (key2394, -2)]

def rawRow11952 : Integer.Sparse Key := [(key2995, 1), (key3002, 1), (key2931, 1), (key2989, 1), (key2929, 1), (key2966, 1), (key2995, 1), (key3002, 1), (key2600, 1), (key2910, 1), (key2598, 1), (key2887, 1), (key2931, 1), (key2989, 1), (key2600, 1), (key2910, 1), (key2587, 1), (key2766, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1), (key2524, -2), (key2443, -2), (key2509, -2), (key2524, -2), (key2394, -2), (key2484, -2), (key2443, -2), (key2509, -2), (key2394, -2), (key2484, -2), (key2383, -2), (key2411, -2)]

def rawRow11953 : Integer.Sparse Key := [(key3002, 1), (key2995, 1), (key2989, 1), (key2931, 1), (key2966, 1), (key2929, 1), (key3002, 1), (key2995, 1), (key2910, 1), (key2600, 1), (key2887, 1), (key2598, 1), (key2989, 1), (key2931, 1), (key2910, 1), (key2600, 1), (key2766, 1), (key2587, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1), (key2524, -2), (key2509, -2), (key2443, -2), (key2524, -2), (key2484, -2), (key2394, -2), (key2509, -2), (key2443, -2), (key2484, -2), (key2394, -2), (key2411, -2), (key2383, -2)]

def rawRow11972 : Integer.Sparse Key := [(key2361, 6), (key2361, 6), (key2364, 6), (key2364, 6), (key2531, -6), (key2531, -6), (key2561, -6), (key2561, -6)]

def rawRow11973 : Integer.Sparse Key := [(key2361, 6), (key2364, 6), (key2361, 6), (key2364, 6), (key2531, -6), (key2561, -6), (key2531, -6), (key2561, -6)]

def rawRow11974 : Integer.Sparse Key := [(key2364, 6), (key2361, 6), (key2361, 6), (key2364, 6), (key2531, -6), (key2561, -6), (key2561, -6), (key2531, -6)]

def rawRow11975 : Integer.Sparse Key := [(key2361, 6), (key2364, 6), (key2364, 6), (key2361, 6), (key2561, -6), (key2531, -6), (key2531, -6), (key2561, -6)]

def rawRow11976 : Integer.Sparse Key := [(key2364, 6), (key2361, 6), (key2364, 6), (key2361, 6), (key2561, -6), (key2531, -6), (key2561, -6), (key2531, -6)]

def rawRow11977 : Integer.Sparse Key := [(key2364, 6), (key2364, 6), (key2361, 6), (key2361, 6), (key2561, -6), (key2561, -6), (key2531, -6), (key2531, -6)]

def rawRow12026 : Integer.Sparse Key := [(key976, 6), (key976, 6), (key984, 6), (key984, 6), (key1169, -6), (key1169, -6), (key1220, -6), (key1220, -6)]

def rawRow12027 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key976, 6), (key984, 6), (key1169, -6), (key1220, -6), (key1169, -6), (key1220, -6)]

def rawRow12028 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key976, 6), (key984, 6), (key1169, -6), (key1220, -6), (key1220, -6), (key1169, -6)]

def rawRow12029 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key984, 6), (key976, 6), (key1220, -6), (key1169, -6), (key1169, -6), (key1220, -6)]

def rawRow12030 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key984, 6), (key976, 6), (key1220, -6), (key1169, -6), (key1220, -6), (key1169, -6)]

def rawRow12031 : Integer.Sparse Key := [(key984, 6), (key984, 6), (key976, 6), (key976, 6), (key1220, -6), (key1220, -6), (key1169, -6), (key1169, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12062 : Integer.Sparse Key := [(key2377, -6), (key2377, -6), (key2389, -6), (key2389, -6), (key2405, 6), (key2405, 6), (key2436, 6), (key2436, 6)]

def rawRow12063 : Integer.Sparse Key := [(key2377, -6), (key2389, -6), (key2377, -6), (key2389, -6), (key2405, 6), (key2436, 6), (key2405, 6), (key2436, 6)]

def rawRow12064 : Integer.Sparse Key := [(key2377, -6), (key2389, -6), (key2389, -6), (key2377, -6), (key2405, 6), (key2436, 6), (key2436, 6), (key2405, 6)]

def rawRow12065 : Integer.Sparse Key := [(key2389, -6), (key2377, -6), (key2377, -6), (key2389, -6), (key2436, 6), (key2405, 6), (key2405, 6), (key2436, 6)]

def rawRow12066 : Integer.Sparse Key := [(key2389, -6), (key2377, -6), (key2389, -6), (key2377, -6), (key2436, 6), (key2405, 6), (key2436, 6), (key2405, 6)]

def rawRow12067 : Integer.Sparse Key := [(key2389, -6), (key2389, -6), (key2377, -6), (key2377, -6), (key2436, 6), (key2436, 6), (key2405, 6), (key2405, 6)]

def rawRow12080 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2410, -2), (key2410, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2445, -2), (key2473, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2483, 2), (key2483, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2526, 2)]

def rawRow12081 : Integer.Sparse Key := [(key2410, -2), (key2407, -2), (key2410, -2), (key2441, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2445, -2), (key2410, -2), (key2441, -2), (key2483, 2), (key2473, 2), (key2483, 2), (key2507, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2526, 2), (key2483, 2), (key2507, 2)]

def rawRow12082 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2441, -2), (key2407, -2), (key2445, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2441, -2), (key2410, -2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2507, 2), (key2473, 2), (key2526, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2507, 2), (key2483, 2)]

def rawRow12083 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2445, -2), (key2407, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2410, -2), (key2441, -2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2526, 2), (key2473, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2483, 2), (key2507, 2)]

def rawRow12084 : Integer.Sparse Key := [(key2441, -2), (key2445, -2), (key2441, -2), (key2410, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2441, -2), (key2407, -2), (key2441, -2), (key2410, -2), (key2507, 2), (key2526, 2), (key2507, 2), (key2483, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2507, 2), (key2473, 2), (key2507, 2), (key2483, 2)]

def rawRow12085 : Integer.Sparse Key := [(key2445, -2), (key2441, -2), (key2441, -2), (key2445, -2), (key2410, -2), (key2410, -2), (key2441, -2), (key2441, -2), (key2410, -2), (key2410, -2), (key2407, -2), (key2407, -2), (key2526, 2), (key2507, 2), (key2507, 2), (key2526, 2), (key2483, 2), (key2483, 2), (key2507, 2), (key2507, 2), (key2483, 2), (key2483, 2), (key2473, 2), (key2473, 2)]

def rawRow12086 : Integer.Sparse Key := [(key2592, -2), (key2595, -2), (key2595, -2), (key2848, -2), (key2970, -2), (key2970, -2), (key2882, -2), (key2882, -2), (key2991, -2), (key2991, -2), (key2993, -2), (key2993, -2), (key2379, 2), (key2393, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2441, 2), (key2544, 2), (key2544, 2), (key2555, 2), (key2555, 2), (key2565, 2), (key2565, 2)]

def rawRow12087 : Integer.Sparse Key := [(key2595, -2), (key2592, -2), (key2595, -2), (key2970, -2), (key2848, -2), (key2970, -2), (key2991, -2), (key2993, -2), (key2882, -2), (key2993, -2), (key2882, -2), (key2991, -2), (key2393, 2), (key2379, 2), (key2393, 2), (key2441, 2), (key2407, 2), (key2441, 2), (key2555, 2), (key2565, 2), (key2544, 2), (key2565, 2), (key2544, 2), (key2555, 2)]

def rawRow12088 : Integer.Sparse Key := [(key2595, -2), (key2595, -2), (key2592, -2), (key2970, -2), (key2970, -2), (key2848, -2), (key2993, -2), (key2991, -2), (key2993, -2), (key2882, -2), (key2991, -2), (key2882, -2), (key2393, 2), (key2393, 2), (key2379, 2), (key2441, 2), (key2441, 2), (key2407, 2), (key2565, 2), (key2555, 2), (key2565, 2), (key2544, 2), (key2555, 2), (key2544, 2)]

def rawRow12089 : Integer.Sparse Key := [(key2848, -2), (key2882, -2), (key2882, -2), (key2592, -2), (key2991, -2), (key2991, -2), (key2595, -2), (key2595, -2), (key2970, -2), (key2970, -2), (key2993, -2), (key2993, -2), (key2771, 2), (key2912, 2), (key2912, 2), (key2592, 2), (key2991, 2), (key2991, 2), (key2393, 2), (key2393, 2), (key2441, 2), (key2441, 2), (key2565, 2), (key2565, 2)]

def rawRow12090 : Integer.Sparse Key := [(key2882, -2), (key2848, -2), (key2882, -2), (key2991, -2), (key2592, -2), (key2991, -2), (key2970, -2), (key2993, -2), (key2595, -2), (key2993, -2), (key2595, -2), (key2970, -2), (key2912, 2), (key2771, 2), (key2912, 2), (key2991, 2), (key2592, 2), (key2991, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2565, 2), (key2393, 2), (key2441, 2)]

def rawRow12091 : Integer.Sparse Key := [(key2882, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2991, -2), (key2592, -2), (key2993, -2), (key2970, -2), (key2993, -2), (key2595, -2), (key2970, -2), (key2595, -2), (key2912, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2991, 2), (key2592, 2), (key2565, 2), (key2441, 2), (key2565, 2), (key2393, 2), (key2441, 2), (key2393, 2)]

def rawRow12092 : Integer.Sparse Key := [(key2970, -2), (key2991, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2993, -2), (key2592, -2), (key2595, -2), (key2848, -2), (key2970, -2), (key2882, -2), (key2991, -2), (key2933, 2), (key2991, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key3003, 2), (key2379, 2), (key2393, 2), (key2407, 2), (key2441, 2), (key2544, 2), (key2555, 2)]

def rawRow12093 : Integer.Sparse Key := [(key2970, -2), (key2993, -2), (key2991, -2), (key2595, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2592, -2), (key2970, -2), (key2848, -2), (key2991, -2), (key2882, -2), (key2933, 2), (key3003, 2), (key2991, 2), (key2602, 2), (key3003, 2), (key2912, 2), (key2393, 2), (key2379, 2), (key2441, 2), (key2407, 2), (key2555, 2), (key2544, 2)]

def rawRow12094 : Integer.Sparse Key := [(key2991, -2), (key2970, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2993, -2), (key2848, -2), (key2882, -2), (key2592, -2), (key2991, -2), (key2595, -2), (key2970, -2), (key2991, 2), (key2933, 2), (key3003, 2), (key2912, 2), (key2602, 2), (key3003, 2), (key2771, 2), (key2912, 2), (key2592, 2), (key2991, 2), (key2393, 2), (key2441, 2)]

def rawRow12095 : Integer.Sparse Key := [(key2991, -2), (key2993, -2), (key2970, -2), (key2882, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2848, -2), (key2991, -2), (key2592, -2), (key2970, -2), (key2595, -2), (key2991, 2), (key3003, 2), (key2933, 2), (key2912, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2771, 2), (key2991, 2), (key2592, 2), (key2441, 2), (key2393, 2)]

def rawRow12096 : Integer.Sparse Key := [(key2993, -2), (key2970, -2), (key2991, -2), (key2993, -2), (key2595, -2), (key2882, -2), (key2970, -2), (key2991, -2), (key2595, -2), (key2882, -2), (key2592, -2), (key2848, -2), (key3003, 2), (key2933, 2), (key2991, 2), (key3003, 2), (key2602, 2), (key2912, 2), (key2933, 2), (key2991, 2), (key2602, 2), (key2912, 2), (key2379, 2), (key2407, 2)]

def rawRow12097 : Integer.Sparse Key := [(key2993, -2), (key2991, -2), (key2970, -2), (key2993, -2), (key2882, -2), (key2595, -2), (key2991, -2), (key2970, -2), (key2882, -2), (key2595, -2), (key2848, -2), (key2592, -2), (key3003, 2), (key2991, 2), (key2933, 2), (key3003, 2), (key2912, 2), (key2602, 2), (key2991, 2), (key2933, 2), (key2912, 2), (key2602, 2), (key2771, 2), (key2592, 2)]

def rawRow12152 : Integer.Sparse Key := [(key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1), (key2538, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2543, -2), (key2543, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2563, -2)]

def rawRow12153 : Integer.Sparse Key := [(key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2543, -2), (key2538, -2), (key2543, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2563, -2), (key2543, -2), (key2554, -2)]

def rawRow12154 : Integer.Sparse Key := [(key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2482, 1), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2538, -2), (key2563, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2554, -2), (key2543, -2)]

def rawRow12155 : Integer.Sparse Key := [(key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2563, -2), (key2538, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2543, -2), (key2554, -2)]

def rawRow12156 : Integer.Sparse Key := [(key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2554, -2), (key2563, -2), (key2554, -2), (key2543, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2543, -2)]

def rawRow12157 : Integer.Sparse Key := [(key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1), (key2506, 1), (key2506, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1), (key2563, -2), (key2554, -2), (key2554, -2), (key2563, -2), (key2543, -2), (key2543, -2), (key2554, -2), (key2554, -2), (key2543, -2), (key2543, -2), (key2538, -2), (key2538, -2)]

def rawRow12158 : Integer.Sparse Key := [(key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2543, 1), (key2543, 1), (key2554, 1), (key2554, 1), (key2563, 1), (key2563, 1), (key2381, -2), (key2392, -2), (key2392, -2), (key2409, -2), (key2440, -2), (key2440, -2), (key2482, -2), (key2482, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2)]

def rawRow12159 : Integer.Sparse Key := [(key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2392, -2), (key2381, -2), (key2392, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2506, -2), (key2522, -2), (key2482, -2), (key2522, -2), (key2482, -2), (key2506, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12160 : Integer.Sparse Key := [(key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2563, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2543, 1), (key2392, -2), (key2392, -2), (key2381, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2522, -2), (key2506, -2), (key2522, -2), (key2482, -2), (key2506, -2), (key2482, -2)]

def rawRow12161 : Integer.Sparse Key := [(key2406, 1), (key2406, 1), (key2480, 1), (key2480, 1), (key2543, 1), (key2543, 1), (key2378, 1), (key2378, 1), (key2503, 1), (key2503, 1), (key2554, 1), (key2554, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2563, 1), (key2563, 1), (key2392, 1), (key2392, 1), (key2440, 1), (key2440, 1), (key2522, 1), (key2522, 1), (key2409, -2), (key2482, -2), (key2482, -2), (key2381, -2), (key2506, -2), (key2506, -2), (key2392, -2), (key2392, -2), (key2440, -2), (key2440, -2), (key2522, -2), (key2522, -2)]

def rawRow12162 : Integer.Sparse Key := [(key2480, 1), (key2543, 1), (key2406, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2482, -2), (key2409, -2), (key2482, -2), (key2506, -2), (key2381, -2), (key2506, -2), (key2440, -2), (key2522, -2), (key2392, -2), (key2522, -2), (key2392, -2), (key2440, -2)]

def rawRow12163 : Integer.Sparse Key := [(key2543, 1), (key2480, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2563, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2390, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2440, 1), (key2392, 1), (key2482, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2506, -2), (key2381, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2392, -2), (key2440, -2), (key2392, -2)]

def rawRow12164 : Integer.Sparse Key := [(key2437, 1), (key2440, 1), (key2503, 1), (key2522, 1), (key2554, 1), (key2563, 1), (key2390, 1), (key2392, 1), (key2480, 1), (key2522, 1), (key2543, 1), (key2563, 1), (key2378, 1), (key2392, 1), (key2406, 1), (key2440, 1), (key2543, 1), (key2554, 1), (key2378, 1), (key2390, 1), (key2406, 1), (key2437, 1), (key2480, 1), (key2503, 1), (key2440, -2), (key2506, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2522, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2440, -2), (key2482, -2), (key2506, -2)]

def rawRow12165 : Integer.Sparse Key := [(key2440, 1), (key2437, 1), (key2522, 1), (key2503, 1), (key2563, 1), (key2554, 1), (key2392, 1), (key2390, 1), (key2522, 1), (key2480, 1), (key2563, 1), (key2543, 1), (key2392, 1), (key2378, 1), (key2440, 1), (key2406, 1), (key2554, 1), (key2543, 1), (key2390, 1), (key2378, 1), (key2437, 1), (key2406, 1), (key2503, 1), (key2480, 1), (key2440, -2), (key2522, -2), (key2506, -2), (key2392, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2381, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2482, -2)]

def rawRow12166 : Integer.Sparse Key := [(key2503, 1), (key2554, 1), (key2437, 1), (key2563, 1), (key2440, 1), (key2522, 1), (key2480, 1), (key2543, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2406, 1), (key2543, 1), (key2378, 1), (key2554, 1), (key2392, 1), (key2440, 1), (key2406, 1), (key2480, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2506, -2), (key2440, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2522, -2), (key2409, -2), (key2482, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2440, -2)]

def rawRow12167 : Integer.Sparse Key := [(key2554, 1), (key2503, 1), (key2563, 1), (key2437, 1), (key2522, 1), (key2440, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2522, 1), (key2392, 1), (key2543, 1), (key2406, 1), (key2554, 1), (key2378, 1), (key2440, 1), (key2392, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2437, 1), (key2390, 1), (key2506, -2), (key2522, -2), (key2440, -2), (key2482, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2440, -2), (key2392, -2)]

def rawRow12168 : Integer.Sparse Key := [(key2522, 1), (key2563, 1), (key2440, 1), (key2554, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2563, 1), (key2392, 1), (key2543, 1), (key2390, 1), (key2480, 1), (key2440, 1), (key2554, 1), (key2392, 1), (key2543, 1), (key2378, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2390, 1), (key2480, 1), (key2378, 1), (key2406, 1), (key2522, -2), (key2440, -2), (key2506, -2), (key2522, -2), (key2392, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2381, -2), (key2409, -2)]

def rawRow12169 : Integer.Sparse Key := [(key2563, 1), (key2522, 1), (key2554, 1), (key2440, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2522, 1), (key2543, 1), (key2392, 1), (key2480, 1), (key2390, 1), (key2554, 1), (key2440, 1), (key2543, 1), (key2392, 1), (key2406, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2480, 1), (key2390, 1), (key2406, 1), (key2378, 1), (key2522, -2), (key2506, -2), (key2440, -2), (key2522, -2), (key2482, -2), (key2392, -2), (key2506, -2), (key2440, -2), (key2482, -2), (key2392, -2), (key2409, -2), (key2381, -2)]

def rawRow12170 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2437, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2440, -2), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2506, 1), (key2506, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1)]

def rawRow12171 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2437, -2), (key2440, -2), (key2406, -2), (key2440, -2), (key2406, -2), (key2437, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2480, 1), (key2482, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2482, 1), (key2506, 1)]

def rawRow12172 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2440, -2), (key2437, -2), (key2440, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2482, 1), (key2480, 1), (key2482, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2506, 1), (key2503, 1), (key2506, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2482, 1), (key2506, 1), (key2482, 1)]

def rawRow12173 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2440, -2), (key2406, -2), (key2409, -2), (key2406, -2), (key2440, -2), (key2409, -2), (key2440, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2522, 1), (key2480, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2522, 1), (key2472, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2506, 1), (key2472, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2480, 1), (key2503, 1)]

def rawRow12174 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2440, -2), (key2409, -2), (key2406, -2), (key2440, -2), (key2406, -2), (key2440, -2), (key2409, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2506, 1), (key2503, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2506, 1), (key2472, 1), (key2506, 1), (key2482, 1), (key2480, 1), (key2472, 1), (key2503, 1), (key2472, 1), (key2503, 1), (key2480, 1)]

def rawRow12175 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2437, -2), (key2440, -2), (key2440, -2), (key2409, -2), (key2409, -2), (key2406, -2), (key2406, -2), (key2437, -2), (key2406, -2), (key2406, -2), (key2522, 1), (key2522, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1), (key2506, 1), (key2506, 1), (key2482, 1), (key2482, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1), (key2480, 1), (key2480, 1), (key2472, 1), (key2472, 1)]

def rawRow12176 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2506, -2), (key2506, -2), (key2538, -2), (key2554, -2), (key2554, -2), (key2378, 1), (key2378, 1), (key2390, 1), (key2390, 1), (key2392, 1), (key2392, 1), (key2406, 1), (key2406, 1), (key2437, 1), (key2437, 1), (key2440, 1), (key2440, 1), (key2480, 1), (key2480, 1), (key2503, 1), (key2503, 1), (key2522, 1), (key2522, 1), (key2543, 1), (key2543, 1), (key2554, 1), (key2554, 1), (key2563, 1), (key2563, 1)]

def rawRow12177 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2503, -2), (key2506, -2), (key2472, -2), (key2506, -2), (key2472, -2), (key2503, -2), (key2554, -2), (key2538, -2), (key2554, -2), (key2390, 1), (key2392, 1), (key2378, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2563, 1), (key2543, 1), (key2554, 1)]

def rawRow12178 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2506, -2), (key2503, -2), (key2506, -2), (key2472, -2), (key2503, -2), (key2472, -2), (key2554, -2), (key2554, -2), (key2538, -2), (key2392, 1), (key2390, 1), (key2392, 1), (key2378, 1), (key2390, 1), (key2378, 1), (key2440, 1), (key2437, 1), (key2440, 1), (key2406, 1), (key2437, 1), (key2406, 1), (key2522, 1), (key2503, 1), (key2522, 1), (key2480, 1), (key2503, 1), (key2480, 1), (key2563, 1), (key2554, 1), (key2563, 1), (key2543, 1), (key2554, 1), (key2543, 1)]

def rawRow12179 : Integer.Sparse Key := [(key2472, -2), (key2472, -2), (key2538, -2), (key2378, -2), (key2378, -2), (key2503, -2), (key2503, -2), (key2554, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2506, -2), (key2406, 1), (key2406, 1), (key2480, 1), (key2480, 1), (key2543, 1), (key2543, 1), (key2378, 1), (key2378, 1), (key2503, 1), (key2503, 1), (key2554, 1), (key2554, 1), (key2390, 1), (key2390, 1), (key2437, 1), (key2437, 1), (key2563, 1), (key2563, 1), (key2392, 1), (key2392, 1), (key2440, 1), (key2440, 1), (key2522, 1), (key2522, 1)]

def rawRow12180 : Integer.Sparse Key := [(key2472, -2), (key2538, -2), (key2472, -2), (key2503, -2), (key2554, -2), (key2378, -2), (key2554, -2), (key2378, -2), (key2503, -2), (key2506, -2), (key2381, -2), (key2506, -2), (key2480, 1), (key2543, 1), (key2406, 1), (key2543, 1), (key2406, 1), (key2480, 1), (key2503, 1), (key2554, 1), (key2378, 1), (key2554, 1), (key2378, 1), (key2503, 1), (key2437, 1), (key2563, 1), (key2390, 1), (key2563, 1), (key2390, 1), (key2437, 1), (key2440, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2440, 1)]

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

def rawRow13593 : Integer.Sparse Key := [(key2587, 4), (key2966, 4), (key2989, 4), (key2587, -2), (key2593, -2), (key2843, -2), (key2880, -2), (key2968, -2), (key2989, -2), (key2598, -2), (key2600, -2), (key2887, -2), (key2910, -2), (key2995, -2), (key3002, -2), (key2600, 4), (key2889, 4), (key2910, 4)]

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

def rawRow8749 : Integer.Sparse Key := [(key2353, 6), (key2356, 6), (key2356, 6), (key2356, 6), (key2527, -6), (key2527, -6), (key2527, -6), (key2558, -6)]

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

def nodeValue1187 : Sparse Master := [(Sum.inr 1187, (1 / 1))]

def nodeValue1188 : Sparse Master := [(Sum.inr 1188, (1 / 1))]

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

def nodeValue1222 : Sparse Master := [(Sum.inr 1222, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


