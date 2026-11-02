-- Prove2me | Definitions.Def_OAIQ106D166
-- name    : OAIQ106D166
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:29:18.893099+00:00
-- url     : https://prove2.me/theorems/ca5b81ec-2294-4b53-a5b1-84384a643a79
-- title:
--   Definitions bundle OAIQ106D166 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 666 declarations of OpenAI's Lean: 666 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow1829`, `OAI.MUB6.Certificate.GramRows.rawRow18290`, `OAI.MUB6.Certificate.GramRows.rawRow18291`, `OAI.MUB6.Certificate.GramRows.rawRow18292`, `OAI.MUB6.Certificate.GramRows.rawRow18293`, `OAI.MUB6.Certificate.GramRows.rawRow18294`, `OAI.MUB6.Certificate.GramRows.rawRow18295`, `OAI.MUB6.Certificate.GramRows.rawRow18296`, `OAI.MUB6.Certificate.GramRows.rawRow18297`, `OAI.MUB6.Certificate.GramRows.rawRow18298`, `OAI.MUB6.Certificate.GramRows.rawRow18299`, `OAI.MUB6.Certificate.GramRows.rawRow18300`, `OAI.MUB6.Certificate.GramRows.rawRow18301`, `OAI.MUB6.Certificate.GramRows.rawRow18302`, `OAI.MUB6.Certificate.GramRows.rawRow18303`, `OAI.MUB6.Certificate.GramRows.rawRow18304`, `OAI.MUB6.Certificate.GramRows.rawRow18305`, `OAI.MUB6.Certificate.GramRows.rawRow18306`, `OAI.MUB6.Certificate.GramRows.rawRow18307`, `OAI.MUB6.Certificate.GramRows.rawRow18308`, `OAI.MUB6.Certificate.GramRows.rawRow18309`, `OAI.MUB6.Certificate.GramRows.rawRow1831`, `OAI.MUB6.Certificate.GramRows.rawRow18310`, `OAI.MUB6.Certificate.GramRows.rawRow18311`, `OAI.MUB6.Certificate.GramRows.rawRow18312`, `OAI.MUB6.Certificate.GramRows.rawRow18313`, `OAI.MUB6.Certificate.GramRows.rawRow18314`, `OAI.MUB6.Certificate.GramRows.rawRow18315`, `OAI.MUB6.Certificate.GramRows.rawRow18316`, `OAI.MUB6.Certificate.GramRows.rawRow18317`, `OAI.MUB6.Certificate.GramRows.rawRow18318`, `OAI.MUB6.Certificate.GramRows.rawRow18319`, `OAI.MUB6.Certificate.GramRows.rawRow1832`, `OAI.MUB6.Certificate.GramRows.rawRow18320`, `OAI.MUB6.Certificate.GramRows.rawRow18321`, `OAI.MUB6.Certificate.GramRows.rawRow18322`, `OAI.MUB6.Certificate.GramRows.rawRow18323`, `OAI.MUB6.Certificate.GramRows.rawRow18324`, `OAI.MUB6.Certificate.GramRows.rawRow18325`, `OAI.MUB6.Certificate.GramRows.rawRow18326` and 626 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_GramRows_Block166`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block166.lean), [`MutuallyUnbiased_GramRows_Block167`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block167.lean), [`MutuallyUnbiased_GramRows_Block168`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block168.lean), [`MutuallyUnbiased_GramRows_Block169`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block169.lean), [`MutuallyUnbiased_GramRows_Block170`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block170.lean), [`MutuallyUnbiased_GramRows_Block171`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block171.lean), [`MutuallyUnbiased_GramRows_Block172`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block172.lean), [`MutuallyUnbiased_GramRows_Block174`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block174.lean), [`MutuallyUnbiased_GramRows_Block38`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block38.lean).
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_15`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_20`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEval21_21`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow16`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow17`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow18`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow19`, `OAI.MUB6.Certificate.GramEntries.Block4.entryEvalRow21`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow4`, `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow5` and `OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow6`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block166
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18290 : Integer.Sparse Key := [(key2682, -1), (key2679, -1), (key2740, -1), (key2710, -1), (key2742, -1), (key2715, -1), (key2689, 2), (key2742, 2), (key2715, 2), (key3050, 1), (key3047, 1), (key3103, 1), (key3096, 1), (key3110, 1), (key3106, 1), (key3054, -2), (key3110, -2), (key3106, -2), (key3050, -1), (key3047, -1), (key3066, -1), (key3061, -1), (key3072, -1), (key3069, -1), (key3050, 1), (key3047, 1), (key3103, 1), (key3096, 1), (key3110, 1), (key3106, 1), (key3054, 2), (key3072, 2), (key3069, 2), (key3054, -2), (key3110, -2), (key3106, -2)]

def rawRow18291 : Integer.Sparse Key := [(key2710, -1), (key2715, -1), (key2679, -1), (key2742, -1), (key2682, -1), (key2740, -1), (key2715, 2), (key2689, 2), (key2742, 2), (key3096, 1), (key3106, 1), (key3047, 1), (key3110, 1), (key3050, 1), (key3103, 1), (key3106, -2), (key3054, -2), (key3110, -2), (key3061, -1), (key3069, -1), (key3047, -1), (key3072, -1), (key3050, -1), (key3066, -1), (key3096, 1), (key3106, 1), (key3047, 1), (key3110, 1), (key3050, 1), (key3103, 1), (key3069, 2), (key3054, 2), (key3072, 2), (key3106, -2), (key3054, -2), (key3110, -2)]

def rawRow18292 : Integer.Sparse Key := [(key2715, -1), (key2710, -1), (key2742, -1), (key2679, -1), (key2740, -1), (key2682, -1), (key2715, 2), (key2742, 2), (key2689, 2), (key3106, 1), (key3096, 1), (key3110, 1), (key3047, 1), (key3103, 1), (key3050, 1), (key3106, -2), (key3110, -2), (key3054, -2), (key3069, -1), (key3061, -1), (key3072, -1), (key3047, -1), (key3066, -1), (key3050, -1), (key3106, 1), (key3096, 1), (key3110, 1), (key3047, 1), (key3103, 1), (key3050, 1), (key3069, 2), (key3072, 2), (key3054, 2), (key3106, -2), (key3110, -2), (key3054, -2)]

def rawRow18293 : Integer.Sparse Key := [(key2740, -1), (key2742, -1), (key2682, -1), (key2715, -1), (key2679, -1), (key2710, -1), (key2742, 2), (key2689, 2), (key2715, 2), (key3103, 1), (key3110, 1), (key3050, 1), (key3106, 1), (key3047, 1), (key3096, 1), (key3110, -2), (key3054, -2), (key3106, -2), (key3066, -1), (key3072, -1), (key3050, -1), (key3069, -1), (key3047, -1), (key3061, -1), (key3103, 1), (key3110, 1), (key3050, 1), (key3106, 1), (key3047, 1), (key3096, 1), (key3072, 2), (key3054, 2), (key3069, 2), (key3110, -2), (key3054, -2), (key3106, -2)]

def rawRow18294 : Integer.Sparse Key := [(key2742, -1), (key2740, -1), (key2715, -1), (key2682, -1), (key2710, -1), (key2679, -1), (key2742, 2), (key2715, 2), (key2689, 2), (key3110, 1), (key3103, 1), (key3106, 1), (key3050, 1), (key3096, 1), (key3047, 1), (key3110, -2), (key3106, -2), (key3054, -2), (key3072, -1), (key3066, -1), (key3069, -1), (key3050, -1), (key3061, -1), (key3047, -1), (key3110, 1), (key3103, 1), (key3106, 1), (key3050, 1), (key3096, 1), (key3047, 1), (key3072, 2), (key3069, 2), (key3054, 2), (key3110, -2), (key3106, -2), (key3054, -2)]

def rawRow18295 : Integer.Sparse Key := [(key2679, -1), (key2689, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2742, -1), (key2682, 2), (key2682, 2), (key2740, 2), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3050, -2), (key3050, -2), (key3103, -2), (key3096, -1), (key3106, -1), (key3096, -1), (key3134, -1), (key3106, -1), (key3134, -1), (key3061, 1), (key3069, 1), (key3061, 1), (key3136, 1), (key3069, 1), (key3136, 1), (key3106, 2), (key3106, 2), (key3134, 2), (key3069, -2), (key3069, -2), (key3136, -2)]

def rawRow18296 : Integer.Sparse Key := [(key2689, -1), (key2679, -1), (key2742, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2682, 2), (key2740, 2), (key2682, 2), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3050, -2), (key3103, -2), (key3050, -2), (key3106, -1), (key3096, -1), (key3134, -1), (key3096, -1), (key3134, -1), (key3106, -1), (key3069, 1), (key3061, 1), (key3136, 1), (key3061, 1), (key3136, 1), (key3069, 1), (key3106, 2), (key3134, 2), (key3106, 2), (key3069, -2), (key3136, -2), (key3069, -2)]

def rawRow18297 : Integer.Sparse Key := [(key2742, -1), (key2742, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key2679, -1), (key2740, 2), (key2682, 2), (key2682, 2), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3103, -2), (key3050, -2), (key3050, -2), (key3134, -1), (key3134, -1), (key3106, -1), (key3106, -1), (key3096, -1), (key3096, -1), (key3136, 1), (key3136, 1), (key3069, 1), (key3069, 1), (key3061, 1), (key3061, 1), (key3134, 2), (key3106, 2), (key3106, 2), (key3136, -2), (key3069, -2), (key3069, -2)]

def rawRow18298 : Integer.Sparse Key := [(key2682, -1), (key2689, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2715, -1), (key2679, 2), (key2679, 2), (key2710, 2), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2679, -2), (key3047, -2), (key3096, -2), (key3103, -1), (key3110, -1), (key3103, -1), (key3136, -1), (key3110, -1), (key3136, -1), (key3066, 1), (key3072, 1), (key3066, 1), (key3134, 1), (key3072, 1), (key3134, 1), (key3110, 2), (key3110, 2), (key3136, 2), (key3072, -2), (key3072, -2), (key3134, -2)]

def rawRow18299 : Integer.Sparse Key := [(key2689, -1), (key2682, -1), (key2715, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2679, 2), (key2710, 2), (key2679, 2), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2679, -2), (key3096, -2), (key3047, -2), (key3110, -1), (key3103, -1), (key3136, -1), (key3103, -1), (key3136, -1), (key3110, -1), (key3072, 1), (key3066, 1), (key3134, 1), (key3066, 1), (key3134, 1), (key3072, 1), (key3110, 2), (key3136, 2), (key3110, 2), (key3072, -2), (key3134, -2), (key3072, -2)]

def rawRow18300 : Integer.Sparse Key := [(key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2710, 2), (key2679, 2), (key2679, 2), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2813, -2), (key2679, -2), (key3047, -2), (key3136, -1), (key3136, -1), (key3110, -1), (key3110, -1), (key3103, -1), (key3103, -1), (key3134, 1), (key3134, 1), (key3072, 1), (key3072, 1), (key3066, 1), (key3066, 1), (key3136, 2), (key3110, 2), (key3110, 2), (key3134, -2), (key3072, -2), (key3072, -2)]

def rawRow18301 : Integer.Sparse Key := [(key2813, -1), (key2818, -1), (key2813, -1), (key2900, -1), (key2818, -1), (key2900, -1), (key2818, 2), (key2818, 2), (key2900, 2), (key2710, 1), (key2715, 1), (key2710, 1), (key2979, 1), (key2715, 1), (key2979, 1), (key2715, -2), (key2715, -2), (key2979, -2), (key2679, -1), (key2689, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2742, -1), (key2679, 1), (key2689, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3110, 1), (key3050, 2), (key3050, 2), (key3066, 2), (key3050, -2), (key3050, -2), (key3103, -2)]

def rawRow18302 : Integer.Sparse Key := [(key2818, -1), (key2813, -1), (key2900, -1), (key2813, -1), (key2900, -1), (key2818, -1), (key2818, 2), (key2900, 2), (key2818, 2), (key2715, 1), (key2710, 1), (key2979, 1), (key2710, 1), (key2979, 1), (key2715, 1), (key2715, -2), (key2979, -2), (key2715, -2), (key2689, -1), (key2679, -1), (key2742, -1), (key2679, -1), (key2742, -1), (key2689, -1), (key2689, 1), (key2679, 1), (key3110, 1), (key3047, 1), (key3110, 1), (key3054, 1), (key3050, 2), (key3066, 2), (key3050, 2), (key3050, -2), (key3103, -2), (key3050, -2)]

def rawRow18303 : Integer.Sparse Key := [(key2900, -1), (key2900, -1), (key2818, -1), (key2818, -1), (key2813, -1), (key2813, -1), (key2900, 2), (key2818, 2), (key2818, 2), (key2979, 1), (key2979, 1), (key2715, 1), (key2715, 1), (key2710, 1), (key2710, 1), (key2979, -2), (key2715, -2), (key2715, -2), (key2742, -1), (key2742, -1), (key2689, -1), (key2689, -1), (key2679, -1), (key2679, -1), (key2955, 1), (key2955, 1), (key2689, 1), (key2689, 1), (key2679, 1), (key3047, 1), (key3066, 2), (key3050, 2), (key3050, 2), (key3103, -2), (key3050, -2), (key3050, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block167
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18304 : Integer.Sparse Key := [(key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2813, 2), (key2813, 2), (key2813, 2), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2710, -2), (key2710, -2), (key2710, -2), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key3103, 2), (key3103, 2), (key3103, 2), (key3066, -2), (key3066, -2), (key3066, -2)]

def rawRow18305 : Integer.Sparse Key := [(key2953, -1), (key2955, -1), (key2953, -1), (key2979, -1), (key2955, -1), (key2979, -1), (key2955, 2), (key2955, 2), (key2979, 2), (key2740, 1), (key2742, 1), (key2740, 1), (key2900, 1), (key2742, 1), (key2900, 1), (key2742, -2), (key2742, -2), (key2900, -2), (key2682, -1), (key2689, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2715, -1), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2679, 2), (key2679, 2), (key2710, 2), (key2679, -2), (key3047, -2), (key3096, -2)]

def rawRow18306 : Integer.Sparse Key := [(key2955, -1), (key2953, -1), (key2979, -1), (key2953, -1), (key2979, -1), (key2955, -1), (key2955, 2), (key2979, 2), (key2955, 2), (key2742, 1), (key2740, 1), (key2900, 1), (key2740, 1), (key2900, 1), (key2742, 1), (key2742, -2), (key2900, -2), (key2742, -2), (key2689, -1), (key2682, -1), (key2715, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2679, 2), (key2710, 2), (key2679, 2), (key2679, -2), (key3096, -2), (key3047, -2)]

def rawRow18307 : Integer.Sparse Key := [(key2979, -1), (key2979, -1), (key2955, -1), (key2955, -1), (key2953, -1), (key2953, -1), (key2979, 2), (key2955, 2), (key2955, 2), (key2900, 1), (key2900, 1), (key2742, 1), (key2742, 1), (key2740, 1), (key2740, 1), (key2900, -2), (key2742, -2), (key2742, -2), (key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2710, 2), (key2679, 2), (key2679, 2), (key2813, -2), (key2679, -2), (key3047, -2)]

def rawRow18308 : Integer.Sparse Key := [(key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2953, 2), (key2953, 2), (key2953, 2), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2740, -2), (key2740, -2), (key2740, -2), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2813, 2), (key2813, 2), (key2813, 2), (key2710, -2), (key2710, -2), (key2710, -2)]

def rawRow18309 : Integer.Sparse Key := [(key2686, 2), (key2822, 2), (key2957, 2), (key2693, -1), (key2694, -1), (key2822, -1), (key2957, -1), (key2834, -1), (key2963, -1), (key2686, 2), (key2822, 2), (key2957, 2), (key2719, -1), (key2744, -1), (key2822, -1), (key2957, -1), (key2907, -1), (key2986, -1), (key2693, -1), (key2694, -1), (key2822, -1), (key2957, -1), (key2834, -1), (key2963, -1), (key2719, -1), (key2744, -1), (key2822, -1), (key2957, -1), (key2907, -1), (key2986, -1), (key2731, 2), (key2750, 2), (key2834, 2), (key2963, 2), (key2907, 2), (key2986, 2)]

def rawRow18310 : Integer.Sparse Key := [(key2686, 2), (key2957, 2), (key2822, 2), (key2694, -1), (key2693, -1), (key2957, -1), (key2822, -1), (key2963, -1), (key2834, -1), (key2686, 2), (key2957, 2), (key2822, 2), (key2744, -1), (key2719, -1), (key2957, -1), (key2822, -1), (key2986, -1), (key2907, -1), (key2694, -1), (key2693, -1), (key2957, -1), (key2822, -1), (key2963, -1), (key2834, -1), (key2744, -1), (key2719, -1), (key2957, -1), (key2822, -1), (key2986, -1), (key2907, -1), (key2750, 2), (key2731, 2), (key2963, 2), (key2834, 2), (key2986, 2), (key2907, 2)]

def rawRow18311 : Integer.Sparse Key := [(key2822, 2), (key2686, 2), (key2957, 2), (key2822, -1), (key2834, -1), (key2693, -1), (key2963, -1), (key2694, -1), (key2957, -1), (key2822, 2), (key2686, 2), (key2957, 2), (key2822, -1), (key2907, -1), (key2719, -1), (key2986, -1), (key2744, -1), (key2957, -1), (key2822, -1), (key2834, -1), (key2693, -1), (key2963, -1), (key2694, -1), (key2957, -1), (key2822, -1), (key2907, -1), (key2719, -1), (key2986, -1), (key2744, -1), (key2957, -1), (key2834, 2), (key2907, 2), (key2731, 2), (key2986, 2), (key2750, 2), (key2963, 2)]

def rawRow18312 : Integer.Sparse Key := [(key2822, 2), (key2957, 2), (key2686, 2), (key2834, -1), (key2822, -1), (key2963, -1), (key2693, -1), (key2957, -1), (key2694, -1), (key2822, 2), (key2957, 2), (key2686, 2), (key2907, -1), (key2822, -1), (key2986, -1), (key2719, -1), (key2957, -1), (key2744, -1), (key2834, -1), (key2822, -1), (key2963, -1), (key2693, -1), (key2957, -1), (key2694, -1), (key2907, -1), (key2822, -1), (key2986, -1), (key2719, -1), (key2957, -1), (key2744, -1), (key2907, 2), (key2834, 2), (key2986, 2), (key2731, 2), (key2963, 2), (key2750, 2)]

def rawRow18313 : Integer.Sparse Key := [(key2957, 2), (key2686, 2), (key2822, 2), (key2957, -1), (key2963, -1), (key2694, -1), (key2834, -1), (key2693, -1), (key2822, -1), (key2957, 2), (key2686, 2), (key2822, 2), (key2957, -1), (key2986, -1), (key2744, -1), (key2907, -1), (key2719, -1), (key2822, -1), (key2957, -1), (key2963, -1), (key2694, -1), (key2834, -1), (key2693, -1), (key2822, -1), (key2957, -1), (key2986, -1), (key2744, -1), (key2907, -1), (key2719, -1), (key2822, -1), (key2963, 2), (key2986, 2), (key2750, 2), (key2907, 2), (key2731, 2), (key2834, 2)]

def rawRow18314 : Integer.Sparse Key := [(key2957, 2), (key2822, 2), (key2686, 2), (key2963, -1), (key2957, -1), (key2834, -1), (key2694, -1), (key2822, -1), (key2693, -1), (key2957, 2), (key2822, 2), (key2686, 2), (key2986, -1), (key2957, -1), (key2907, -1), (key2744, -1), (key2822, -1), (key2719, -1), (key2963, -1), (key2957, -1), (key2834, -1), (key2694, -1), (key2822, -1), (key2693, -1), (key2986, -1), (key2957, -1), (key2907, -1), (key2744, -1), (key2822, -1), (key2719, -1), (key2986, 2), (key2963, 2), (key2907, 2), (key2750, 2), (key2834, 2), (key2731, 2)]

def rawRow18315 : Integer.Sparse Key := [(key2693, 2), (key2693, 2), (key2963, 2), (key2686, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2957, -1), (key2719, 2), (key2719, 2), (key2986, 2), (key2686, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2957, -1), (key2719, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2986, -1), (key2693, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2963, -1), (key2694, 2), (key2744, 2), (key2694, 2), (key2957, 2), (key2744, 2), (key2957, 2)]

def rawRow18316 : Integer.Sparse Key := [(key2693, 2), (key2963, 2), (key2693, 2), (key2694, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2719, 2), (key2986, 2), (key2719, 2), (key2744, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2744, 2), (key2694, 2), (key2957, 2), (key2694, 2), (key2957, 2), (key2744, 2)]

def rawRow18317 : Integer.Sparse Key := [(key2963, 2), (key2693, 2), (key2693, 2), (key2957, -1), (key2957, -1), (key2694, -1), (key2694, -1), (key2686, -1), (key2686, -1), (key2986, 2), (key2719, 2), (key2719, 2), (key2957, -1), (key2957, -1), (key2744, -1), (key2744, -1), (key2686, -1), (key2686, -1), (key2986, -1), (key2986, -1), (key2731, -1), (key2731, -1), (key2719, -1), (key2719, -1), (key2963, -1), (key2963, -1), (key2750, -1), (key2750, -1), (key2693, -1), (key2693, -1), (key2957, 2), (key2957, 2), (key2744, 2), (key2744, 2), (key2694, 2), (key2694, 2)]

def rawRow18318 : Integer.Sparse Key := [(key2694, 2), (key2694, 2), (key2834, 2), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2744, 2), (key2744, 2), (key2907, 2), (key2686, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2822, -1), (key2744, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2907, -1), (key2694, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2834, -1), (key2693, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2719, 2), (key2822, 2)]

def rawRow18319 : Integer.Sparse Key := [(key2694, 2), (key2834, 2), (key2694, 2), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2744, 2), (key2907, 2), (key2744, 2), (key2719, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2719, 2), (key2693, 2), (key2822, 2), (key2693, 2), (key2822, 2), (key2719, 2)]

def rawRow18320 : Integer.Sparse Key := [(key2834, 2), (key2694, 2), (key2694, 2), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2907, 2), (key2744, 2), (key2744, 2), (key2822, -1), (key2822, -1), (key2719, -1), (key2719, -1), (key2686, -1), (key2686, -1), (key2907, -1), (key2907, -1), (key2750, -1), (key2750, -1), (key2744, -1), (key2744, -1), (key2834, -1), (key2834, -1), (key2731, -1), (key2731, -1), (key2694, -1), (key2694, -1), (key2822, 2), (key2822, 2), (key2719, 2), (key2719, 2), (key2693, 2), (key2693, 2)]

def rawRow18321 : Integer.Sparse Key := [(key2719, 2), (key2719, 2), (key2986, 2), (key2719, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2986, -1), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2963, -1), (key2686, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2957, -1), (key2686, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2957, -1), (key2694, 2), (key2744, 2), (key2694, 2), (key2957, 2), (key2744, 2), (key2957, 2)]

def rawRow18322 : Integer.Sparse Key := [(key2719, 2), (key2986, 2), (key2719, 2), (key2731, -1), (key2719, -1), (key2986, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2693, 2), (key2963, 2), (key2693, 2), (key2750, -1), (key2693, -1), (key2963, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2744, 2), (key2694, 2), (key2957, 2), (key2694, 2), (key2957, 2), (key2744, 2)]

def rawRow18323 : Integer.Sparse Key := [(key2986, 2), (key2719, 2), (key2719, 2), (key2986, -1), (key2986, -1), (key2731, -1), (key2731, -1), (key2719, -1), (key2719, -1), (key2963, 2), (key2693, 2), (key2693, 2), (key2963, -1), (key2963, -1), (key2750, -1), (key2750, -1), (key2693, -1), (key2693, -1), (key2957, -1), (key2957, -1), (key2694, -1), (key2694, -1), (key2686, -1), (key2686, -1), (key2957, -1), (key2957, -1), (key2744, -1), (key2744, -1), (key2686, -1), (key2686, -1), (key2957, 2), (key2957, 2), (key2744, 2), (key2744, 2), (key2694, 2), (key2694, 2)]

def rawRow18324 : Integer.Sparse Key := [(key2731, 2), (key2731, 2), (key2731, 2), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2750, 2), (key2750, 2), (key2750, 2), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2)]

def rawRow18325 : Integer.Sparse Key := [(key2744, 2), (key2744, 2), (key2907, 2), (key2744, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2907, -1), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2834, -1), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2686, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2822, -1), (key2693, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2719, 2), (key2822, 2)]

def rawRow18326 : Integer.Sparse Key := [(key2744, 2), (key2907, 2), (key2744, 2), (key2750, -1), (key2744, -1), (key2907, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2694, 2), (key2834, 2), (key2694, 2), (key2731, -1), (key2694, -1), (key2834, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2719, 2), (key2693, 2), (key2822, 2), (key2693, 2), (key2822, 2), (key2719, 2)]

def rawRow18327 : Integer.Sparse Key := [(key2907, 2), (key2744, 2), (key2744, 2), (key2907, -1), (key2907, -1), (key2750, -1), (key2750, -1), (key2744, -1), (key2744, -1), (key2834, 2), (key2694, 2), (key2694, 2), (key2834, -1), (key2834, -1), (key2731, -1), (key2731, -1), (key2694, -1), (key2694, -1), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2822, -1), (key2822, -1), (key2719, -1), (key2719, -1), (key2686, -1), (key2686, -1), (key2822, 2), (key2822, 2), (key2719, 2), (key2719, 2), (key2693, 2), (key2693, 2)]

def rawRow18328 : Integer.Sparse Key := [(key2750, 2), (key2750, 2), (key2750, 2), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2731, 2), (key2731, 2), (key2731, 2), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2)]

def rawRow18329 : Integer.Sparse Key := [(key2114, 4), (key2118, 4), (key2122, 4), (key2114, -2), (key2118, -2), (key2156, -2), (key2183, -2), (key2162, -2), (key2185, -2), (key2114, -2), (key2118, -2), (key2156, -2), (key2183, -2), (key2162, -2), (key2185, -2), (key2156, 4), (key2183, 4), (key2285, 4)]

def rawRow18330 : Integer.Sparse Key := [(key2118, 4), (key2114, 4), (key2122, 4), (key2118, -2), (key2114, -2), (key2183, -2), (key2156, -2), (key2185, -2), (key2162, -2), (key2118, -2), (key2114, -2), (key2183, -2), (key2156, -2), (key2185, -2), (key2162, -2), (key2183, 4), (key2156, 4), (key2285, 4)]

def rawRow18331 : Integer.Sparse Key := [(key2114, 4), (key2122, 4), (key2118, 4), (key2156, -2), (key2162, -2), (key2114, -2), (key2185, -2), (key2118, -2), (key2183, -2), (key2156, -2), (key2162, -2), (key2114, -2), (key2185, -2), (key2118, -2), (key2183, -2), (key2156, 4), (key2285, 4), (key2183, 4)]

def rawRow18332 : Integer.Sparse Key := [(key2122, 4), (key2114, 4), (key2118, 4), (key2162, -2), (key2156, -2), (key2185, -2), (key2114, -2), (key2183, -2), (key2118, -2), (key2162, -2), (key2156, -2), (key2185, -2), (key2114, -2), (key2183, -2), (key2118, -2), (key2285, 4), (key2156, 4), (key2183, 4)]

def rawRow18333 : Integer.Sparse Key := [(key2118, 4), (key2122, 4), (key2114, 4), (key2183, -2), (key2185, -2), (key2118, -2), (key2162, -2), (key2114, -2), (key2156, -2), (key2183, -2), (key2185, -2), (key2118, -2), (key2162, -2), (key2114, -2), (key2156, -2), (key2183, 4), (key2285, 4), (key2156, 4)]

def rawRow18334 : Integer.Sparse Key := [(key2122, 4), (key2118, 4), (key2114, 4), (key2185, -2), (key2183, -2), (key2162, -2), (key2118, -2), (key2156, -2), (key2114, -2), (key2185, -2), (key2183, -2), (key2162, -2), (key2118, -2), (key2156, -2), (key2114, -2), (key2285, 4), (key2183, 4), (key2156, 4)]

def rawRow18335 : Integer.Sparse Key := [(key2156, 4), (key2162, 4), (key2162, 4), (key2114, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, -2), (key2156, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2285, -2), (key2114, 4), (key2185, 4), (key2185, 4)]

def rawRow18336 : Integer.Sparse Key := [(key2162, 4), (key2156, 4), (key2162, 4), (key2122, -2), (key2114, -2), (key2185, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2185, 4), (key2114, 4), (key2185, 4)]

def rawRow18337 : Integer.Sparse Key := [(key2162, 4), (key2162, 4), (key2156, 4), (key2185, -2), (key2185, -2), (key2122, -2), (key2122, -2), (key2114, -2), (key2114, -2), (key2285, -2), (key2285, -2), (key2162, -2), (key2162, -2), (key2156, -2), (key2156, -2), (key2185, 4), (key2185, 4), (key2114, 4)]

def rawRow18338 : Integer.Sparse Key := [(key2183, 4), (key2185, 4), (key2185, 4), (key2118, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, -2), (key2183, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2285, -2), (key2118, 4), (key2162, 4), (key2162, 4)]

def rawRow18339 : Integer.Sparse Key := [(key2185, 4), (key2183, 4), (key2185, 4), (key2122, -2), (key2118, -2), (key2162, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2162, 4), (key2118, 4), (key2162, 4)]

def rawRow18340 : Integer.Sparse Key := [(key2185, 4), (key2185, 4), (key2183, 4), (key2162, -2), (key2162, -2), (key2122, -2), (key2122, -2), (key2118, -2), (key2118, -2), (key2285, -2), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, -2), (key2183, -2), (key2162, 4), (key2162, 4), (key2118, 4)]

def rawRow18341 : Integer.Sparse Key := [(key2156, 4), (key2162, 4), (key2162, 4), (key2156, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2285, -2), (key2114, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, -2), (key2114, 4), (key2185, 4), (key2185, 4)]

def rawRow18342 : Integer.Sparse Key := [(key2162, 4), (key2156, 4), (key2162, 4), (key2162, -2), (key2156, -2), (key2285, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, 4), (key2114, 4), (key2185, 4)]

def rawRow18343 : Integer.Sparse Key := [(key2162, 4), (key2162, 4), (key2156, 4), (key2285, -2), (key2285, -2), (key2162, -2), (key2162, -2), (key2156, -2), (key2156, -2), (key2185, -2), (key2185, -2), (key2122, -2), (key2122, -2), (key2114, -2), (key2114, -2), (key2185, 4), (key2185, 4), (key2114, 4)]

def rawRow18344 : Integer.Sparse Key := [(key2285, 4), (key2285, 4), (key2285, 4), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2122, 4), (key2122, 4), (key2122, 4)]

def rawRow18345 : Integer.Sparse Key := [(key2183, 4), (key2185, 4), (key2185, 4), (key2183, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2285, -2), (key2118, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, -2), (key2118, 4), (key2162, 4), (key2162, 4)]

def rawRow18346 : Integer.Sparse Key := [(key2185, 4), (key2183, 4), (key2185, 4), (key2185, -2), (key2183, -2), (key2285, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, 4), (key2118, 4), (key2162, 4)]

def rawRow18347 : Integer.Sparse Key := [(key2185, 4), (key2185, 4), (key2183, 4), (key2285, -2), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, -2), (key2183, -2), (key2162, -2), (key2162, -2), (key2122, -2), (key2122, -2), (key2118, -2), (key2118, -2), (key2162, 4), (key2162, 4), (key2118, 4)]

def rawRow18348 : Integer.Sparse Key := [(key2285, 4), (key2285, 4), (key2285, 4), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2122, 4), (key2122, 4), (key2122, 4)]

def rawRow18349 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, -2), (key2112, -2), (key2110, -2), (key2113, -2), (key2107, 2), (key2112, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2140, -6), (key2110, 2), (key2113, 2), (key2140, 2), (key2140, -6)]

def rawRow18350 : Integer.Sparse Key := [(key2104, -2), (key2102, -2), (key2112, -2), (key2107, -2), (key2113, -2), (key2110, -2), (key2112, 2), (key2107, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2140, -6), (key2113, 2), (key2110, 2), (key2140, 2), (key2140, -6)]

def rawRow18351 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2102, -2), (key2113, -2), (key2104, -2), (key2112, -2), (key2107, 2), (key2140, 2), (key2112, 2), (key2110, 2), (key2140, 2), (key2113, 2), (key2107, 2), (key2140, 2), (key2112, 2), (key2140, -6), (key2110, 2), (key2140, 2), (key2113, 2), (key2140, -6)]

def rawRow18352 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2113, -2), (key2102, -2), (key2112, -2), (key2104, -2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, -6), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, -6)]

def rawRow18353 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2104, -2), (key2110, -2), (key2102, -2), (key2107, -2), (key2112, 2), (key2140, 2), (key2107, 2), (key2113, 2), (key2140, 2), (key2110, 2), (key2112, 2), (key2140, 2), (key2107, 2), (key2140, -6), (key2113, 2), (key2140, 2), (key2110, 2), (key2140, -6)]

def rawRow18354 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2110, -2), (key2104, -2), (key2107, -2), (key2102, -2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, -6), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, -6)]

def rawRow18355 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, -2), (key2102, 2), (key2113, 2), (key2113, 2), (key2104, 2), (key2112, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2112, -6), (key2110, 2), (key2140, 2), (key2140, 2), (key2113, -6)]

def rawRow18356 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2140, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2113, 2), (key2102, 2), (key2113, 2), (key2112, 2), (key2104, 2), (key2112, 2), (key2140, 2), (key2107, 2), (key2140, 2), (key2112, -6), (key2140, 2), (key2110, 2), (key2140, 2), (key2113, -6)]

def rawRow18357 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2110, -2), (key2110, -2), (key2107, -2), (key2107, -2), (key2113, 2), (key2113, 2), (key2102, 2), (key2112, 2), (key2112, 2), (key2104, 2), (key2140, 2), (key2140, 2), (key2107, 2), (key2112, -6), (key2140, 2), (key2140, 2), (key2110, 2), (key2113, -6)]

def rawRow18358 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, -2), (key2104, 2), (key2110, 2), (key2110, 2), (key2102, 2), (key2107, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2107, -6), (key2113, 2), (key2140, 2), (key2140, 2), (key2110, -6)]

def rawRow18359 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2140, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2110, 2), (key2104, 2), (key2110, 2), (key2107, 2), (key2102, 2), (key2107, 2), (key2140, 2), (key2112, 2), (key2140, 2), (key2107, -6), (key2140, 2), (key2113, 2), (key2140, 2), (key2110, -6)]

def rawRow18360 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2113, -2), (key2113, -2), (key2112, -2), (key2112, -2), (key2110, 2), (key2110, 2), (key2104, 2), (key2107, 2), (key2107, 2), (key2102, 2), (key2140, 2), (key2140, 2), (key2112, 2), (key2107, -6), (key2140, 2), (key2140, 2), (key2113, 2), (key2110, -6)]

def rawRow18361 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, -2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2140, 2), (key2140, 2), (key2102, 2), (key2113, 2), (key2113, 2), (key2113, -6), (key2104, 2), (key2112, 2), (key2112, 2), (key2112, -6)]

def rawRow18362 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2140, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2140, 2), (key2113, 2), (key2102, 2), (key2113, 2), (key2113, -6), (key2112, 2), (key2104, 2), (key2112, 2), (key2112, -6)]

def rawRow18363 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2110, -2), (key2110, -2), (key2107, -2), (key2107, -2), (key2140, 2), (key2140, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2113, 2), (key2102, 2), (key2113, -6), (key2112, 2), (key2112, 2), (key2104, 2), (key2112, -6)]

def rawRow18364 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2110, 2), (key2110, 2), (key2110, 2), (key2107, 2), (key2107, 2), (key2107, 2), (key2113, 2), (key2113, 2), (key2113, 2), (key2102, -6), (key2112, 2), (key2112, 2), (key2112, 2), (key2104, -6)]

def rawRow18365 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, -2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2140, 2), (key2140, 2), (key2104, 2), (key2110, 2), (key2110, 2), (key2110, -6), (key2102, 2), (key2107, 2), (key2107, 2), (key2107, -6)]

def rawRow18366 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2140, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2140, 2), (key2110, 2), (key2104, 2), (key2110, 2), (key2110, -6), (key2107, 2), (key2102, 2), (key2107, 2), (key2107, -6)]

def rawRow18367 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2113, -2), (key2113, -2), (key2112, -2), (key2112, -2), (key2140, 2), (key2140, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2110, 2), (key2104, 2), (key2110, -6), (key2107, 2), (key2107, 2), (key2102, 2), (key2107, -6)]

def rawRow18368 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2113, 2), (key2113, 2), (key2113, 2), (key2112, 2), (key2112, 2), (key2112, 2), (key2110, 2), (key2110, 2), (key2110, 2), (key2104, -6), (key2107, 2), (key2107, 2), (key2107, 2), (key2102, -6)]

def rawRow18369 : Integer.Sparse Key := [(key1945, 4), (key1947, 4), (key1948, 4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1952, 12)]

def rawRow18370 : Integer.Sparse Key := [(key1945, 4), (key1948, 4), (key1947, 4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1952, 12)]

def rawRow18371 : Integer.Sparse Key := [(key1947, 4), (key1945, 4), (key1948, 4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1952, 12)]

def rawRow18372 : Integer.Sparse Key := [(key1947, 4), (key1948, 4), (key1945, 4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, 12)]

def rawRow18373 : Integer.Sparse Key := [(key1948, 4), (key1945, 4), (key1947, 4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1952, 12)]

def rawRow18374 : Integer.Sparse Key := [(key1948, 4), (key1947, 4), (key1945, 4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, 12)]

def rawRow18375 : Integer.Sparse Key := [(key1947, 4), (key1947, 4), (key1952, 4), (key1945, -4), (key1948, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1952, -4), (key1948, 12)]

def rawRow18376 : Integer.Sparse Key := [(key1947, 4), (key1952, 4), (key1947, 4), (key1948, -4), (key1945, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1952, -4), (key1948, 12)]

def rawRow18377 : Integer.Sparse Key := [(key1952, 4), (key1947, 4), (key1947, 4), (key1948, -4), (key1948, -4), (key1945, -4), (key1952, -4), (key1952, -4), (key1947, -4), (key1948, 12)]

def rawRow18378 : Integer.Sparse Key := [(key1948, 4), (key1948, 4), (key1952, 4), (key1945, -4), (key1947, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1952, -4), (key1947, 12)]

def rawRow18379 : Integer.Sparse Key := [(key1948, 4), (key1952, 4), (key1948, 4), (key1947, -4), (key1945, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1952, -4), (key1947, 12)]

def rawRow18380 : Integer.Sparse Key := [(key1952, 4), (key1948, 4), (key1948, 4), (key1947, -4), (key1947, -4), (key1945, -4), (key1952, -4), (key1952, -4), (key1948, -4), (key1947, 12)]

def rawRow18381 : Integer.Sparse Key := [(key1947, 4), (key1947, 4), (key1952, 4), (key1947, -4), (key1952, -4), (key1952, -4), (key1945, -4), (key1948, -4), (key1948, -4), (key1948, 12)]

def rawRow18382 : Integer.Sparse Key := [(key1947, 4), (key1952, 4), (key1947, 4), (key1952, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1945, -4), (key1948, -4), (key1948, 12)]

def rawRow18383 : Integer.Sparse Key := [(key1952, 4), (key1947, 4), (key1947, 4), (key1952, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1948, -4), (key1945, -4), (key1948, 12)]

def rawRow18384 : Integer.Sparse Key := [(key1952, 4), (key1952, 4), (key1952, 4), (key1947, -4), (key1947, -4), (key1947, -4), (key1948, -4), (key1948, -4), (key1948, -4), (key1945, 12)]

def rawRow18385 : Integer.Sparse Key := [(key1948, 4), (key1948, 4), (key1952, 4), (key1948, -4), (key1952, -4), (key1952, -4), (key1945, -4), (key1947, -4), (key1947, -4), (key1947, 12)]

def rawRow18386 : Integer.Sparse Key := [(key1948, 4), (key1952, 4), (key1948, 4), (key1952, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1945, -4), (key1947, -4), (key1947, 12)]

def rawRow18387 : Integer.Sparse Key := [(key1952, 4), (key1948, 4), (key1948, 4), (key1952, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1947, -4), (key1945, -4), (key1947, 12)]

def rawRow18388 : Integer.Sparse Key := [(key1952, 4), (key1952, 4), (key1952, 4), (key1948, -4), (key1948, -4), (key1948, -4), (key1947, -4), (key1947, -4), (key1947, -4), (key1945, 12)]

def rawRow18389 : Integer.Sparse Key := [(key2117, 4), (key2119, 4), (key2123, 4), (key2117, -2), (key2119, -2), (key2159, -2), (key2184, -2), (key2163, -2), (key2186, -2), (key2117, -2), (key2119, -2), (key2159, -2), (key2184, -2), (key2163, -2), (key2186, -2), (key2159, 4), (key2184, 4), (key2286, 4)]

def rawRow18390 : Integer.Sparse Key := [(key2119, 4), (key2117, 4), (key2123, 4), (key2119, -2), (key2117, -2), (key2184, -2), (key2159, -2), (key2186, -2), (key2163, -2), (key2119, -2), (key2117, -2), (key2184, -2), (key2159, -2), (key2186, -2), (key2163, -2), (key2184, 4), (key2159, 4), (key2286, 4)]

def rawRow18391 : Integer.Sparse Key := [(key2117, 4), (key2123, 4), (key2119, 4), (key2159, -2), (key2163, -2), (key2117, -2), (key2186, -2), (key2119, -2), (key2184, -2), (key2159, -2), (key2163, -2), (key2117, -2), (key2186, -2), (key2119, -2), (key2184, -2), (key2159, 4), (key2286, 4), (key2184, 4)]

def rawRow18392 : Integer.Sparse Key := [(key2123, 4), (key2117, 4), (key2119, 4), (key2163, -2), (key2159, -2), (key2186, -2), (key2117, -2), (key2184, -2), (key2119, -2), (key2163, -2), (key2159, -2), (key2186, -2), (key2117, -2), (key2184, -2), (key2119, -2), (key2286, 4), (key2159, 4), (key2184, 4)]

def rawRow18393 : Integer.Sparse Key := [(key2119, 4), (key2123, 4), (key2117, 4), (key2184, -2), (key2186, -2), (key2119, -2), (key2163, -2), (key2117, -2), (key2159, -2), (key2184, -2), (key2186, -2), (key2119, -2), (key2163, -2), (key2117, -2), (key2159, -2), (key2184, 4), (key2286, 4), (key2159, 4)]

def rawRow18394 : Integer.Sparse Key := [(key2123, 4), (key2119, 4), (key2117, 4), (key2186, -2), (key2184, -2), (key2163, -2), (key2119, -2), (key2159, -2), (key2117, -2), (key2186, -2), (key2184, -2), (key2163, -2), (key2119, -2), (key2159, -2), (key2117, -2), (key2286, 4), (key2184, 4), (key2159, 4)]

def rawRow18395 : Integer.Sparse Key := [(key2159, 4), (key2163, 4), (key2163, 4), (key2117, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, -2), (key2159, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2286, -2), (key2117, 4), (key2186, 4), (key2186, 4)]

def rawRow18396 : Integer.Sparse Key := [(key2163, 4), (key2159, 4), (key2163, 4), (key2123, -2), (key2117, -2), (key2186, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2186, 4), (key2117, 4), (key2186, 4)]

def rawRow18397 : Integer.Sparse Key := [(key2163, 4), (key2163, 4), (key2159, 4), (key2186, -2), (key2186, -2), (key2123, -2), (key2123, -2), (key2117, -2), (key2117, -2), (key2286, -2), (key2286, -2), (key2163, -2), (key2163, -2), (key2159, -2), (key2159, -2), (key2186, 4), (key2186, 4), (key2117, 4)]

def rawRow18398 : Integer.Sparse Key := [(key2184, 4), (key2186, 4), (key2186, 4), (key2119, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, -2), (key2184, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2286, -2), (key2119, 4), (key2163, 4), (key2163, 4)]

def rawRow18399 : Integer.Sparse Key := [(key2186, 4), (key2184, 4), (key2186, 4), (key2123, -2), (key2119, -2), (key2163, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2163, 4), (key2119, 4), (key2163, 4)]

def rawRow18400 : Integer.Sparse Key := [(key2186, 4), (key2186, 4), (key2184, 4), (key2163, -2), (key2163, -2), (key2123, -2), (key2123, -2), (key2119, -2), (key2119, -2), (key2286, -2), (key2286, -2), (key2186, -2), (key2186, -2), (key2184, -2), (key2184, -2), (key2163, 4), (key2163, 4), (key2119, 4)]

def rawRow18401 : Integer.Sparse Key := [(key2159, 4), (key2163, 4), (key2163, 4), (key2159, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2286, -2), (key2117, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, -2), (key2117, 4), (key2186, 4), (key2186, 4)]

def rawRow18402 : Integer.Sparse Key := [(key2163, 4), (key2159, 4), (key2163, 4), (key2163, -2), (key2159, -2), (key2286, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, 4), (key2117, 4), (key2186, 4)]

def rawRow18403 : Integer.Sparse Key := [(key2163, 4), (key2163, 4), (key2159, 4), (key2286, -2), (key2286, -2), (key2163, -2), (key2163, -2), (key2159, -2), (key2159, -2), (key2186, -2), (key2186, -2), (key2123, -2), (key2123, -2), (key2117, -2), (key2117, -2), (key2186, 4), (key2186, 4), (key2117, 4)]

def rawRow18404 : Integer.Sparse Key := [(key2286, 4), (key2286, 4), (key2286, 4), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2123, 4), (key2123, 4), (key2123, 4)]

def rawRow18405 : Integer.Sparse Key := [(key2184, 4), (key2186, 4), (key2186, 4), (key2184, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2286, -2), (key2119, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, -2), (key2119, 4), (key2163, 4), (key2163, 4)]

def rawRow18406 : Integer.Sparse Key := [(key2186, 4), (key2184, 4), (key2186, 4), (key2186, -2), (key2184, -2), (key2286, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, 4), (key2119, 4), (key2163, 4)]

def rawRow18407 : Integer.Sparse Key := [(key2186, 4), (key2186, 4), (key2184, 4), (key2286, -2), (key2286, -2), (key2186, -2), (key2186, -2), (key2184, -2), (key2184, -2), (key2163, -2), (key2163, -2), (key2123, -2), (key2123, -2), (key2119, -2), (key2119, -2), (key2163, 4), (key2163, 4), (key2119, 4)]

def rawRow18408 : Integer.Sparse Key := [(key2286, 4), (key2286, 4), (key2286, 4), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2123, 4), (key2123, 4), (key2123, 4)]

def rawRow18409 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3086, 2), (key3088, 2), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3109, -6), (key3090, 2), (key3091, 2), (key3109, 2), (key3109, -6)]

def rawRow18410 : Integer.Sparse Key := [(key3082, -2), (key3081, -2), (key3088, -2), (key3086, -2), (key3091, -2), (key3090, -2), (key3088, 2), (key3086, 2), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3109, -6), (key3091, 2), (key3090, 2), (key3109, 2), (key3109, -6)]

def rawRow18411 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3081, -2), (key3091, -2), (key3082, -2), (key3088, -2), (key3086, 2), (key3109, 2), (key3088, 2), (key3090, 2), (key3109, 2), (key3091, 2), (key3086, 2), (key3109, 2), (key3088, 2), (key3109, -6), (key3090, 2), (key3109, 2), (key3091, 2), (key3109, -6)]

def rawRow18412 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3091, -2), (key3081, -2), (key3088, -2), (key3082, -2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, -6), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, -6)]

def rawRow18413 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3082, -2), (key3088, -2), (key3081, -2), (key3086, -2), (key3088, 2), (key3109, 2), (key3086, 2), (key3091, 2), (key3109, 2), (key3090, 2), (key3088, 2), (key3109, 2), (key3086, 2), (key3109, -6), (key3091, 2), (key3109, 2), (key3090, 2), (key3109, -6)]

def rawRow18414 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3088, -2), (key3082, -2), (key3086, -2), (key3081, -2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, -6), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, -6)]

def rawRow18415 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, -2), (key3081, 2), (key3091, 2), (key3091, 2), (key3082, 2), (key3088, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, -6), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, -6)]

def rawRow18416 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3109, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3091, 2), (key3081, 2), (key3091, 2), (key3088, 2), (key3082, 2), (key3088, 2), (key3109, 2), (key3086, 2), (key3109, 2), (key3088, -6), (key3109, 2), (key3090, 2), (key3109, 2), (key3091, -6)]

def rawRow18417 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3088, -2), (key3088, -2), (key3086, -2), (key3086, -2), (key3091, 2), (key3091, 2), (key3081, 2), (key3088, 2), (key3088, 2), (key3082, 2), (key3109, 2), (key3109, 2), (key3086, 2), (key3088, -6), (key3109, 2), (key3109, 2), (key3090, 2), (key3091, -6)]

def rawRow18418 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, -2), (key3082, 2), (key3088, 2), (key3088, 2), (key3081, 2), (key3086, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3109, 2), (key3086, -6), (key3091, 2), (key3109, 2), (key3109, 2), (key3090, -6)]

def rawRow18419 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3109, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3088, 2), (key3082, 2), (key3088, 2), (key3086, 2), (key3081, 2), (key3086, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3086, -6), (key3109, 2), (key3091, 2), (key3109, 2), (key3090, -6)]

def rawRow18420 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3091, -2), (key3091, -2), (key3090, -2), (key3090, -2), (key3088, 2), (key3088, 2), (key3082, 2), (key3086, 2), (key3086, 2), (key3081, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3086, -6), (key3109, 2), (key3109, 2), (key3091, 2), (key3090, -6)]

def rawRow18421 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, -2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3109, 2), (key3081, 2), (key3091, 2), (key3091, 2), (key3091, -6), (key3082, 2), (key3088, 2), (key3088, 2), (key3088, -6)]

def rawRow18422 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3109, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3091, 2), (key3081, 2), (key3091, 2), (key3091, -6), (key3088, 2), (key3082, 2), (key3088, 2), (key3088, -6)]

def rawRow18423 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3088, -2), (key3088, -2), (key3086, -2), (key3086, -2), (key3109, 2), (key3109, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3091, 2), (key3091, 2), (key3081, 2), (key3091, -6), (key3088, 2), (key3088, 2), (key3082, 2), (key3088, -6)]

def rawRow18424 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3088, 2), (key3088, 2), (key3088, 2), (key3086, 2), (key3086, 2), (key3086, 2), (key3091, 2), (key3091, 2), (key3091, 2), (key3081, -6), (key3088, 2), (key3088, 2), (key3088, 2), (key3082, -6)]

def rawRow18425 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, -2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3109, 2), (key3109, 2), (key3082, 2), (key3088, 2), (key3088, 2), (key3088, -6), (key3081, 2), (key3086, 2), (key3086, 2), (key3086, -6)]

def rawRow18426 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3109, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, 2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3109, 2), (key3088, 2), (key3082, 2), (key3088, 2), (key3088, -6), (key3086, 2), (key3081, 2), (key3086, 2), (key3086, -6)]

def rawRow18427 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3091, -2), (key3091, -2), (key3090, -2), (key3090, -2), (key3109, 2), (key3109, 2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3088, 2), (key3088, 2), (key3082, 2), (key3088, -6), (key3086, 2), (key3086, 2), (key3081, 2), (key3086, -6)]

def rawRow18428 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3091, 2), (key3091, 2), (key3091, 2), (key3090, 2), (key3090, 2), (key3090, 2), (key3088, 2), (key3088, 2), (key3088, 2), (key3082, -6), (key3086, 2), (key3086, 2), (key3086, 2), (key3081, -6)]

def rawRow18429 : Integer.Sparse Key := [(key2353, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6)]

def rawRow18430 : Integer.Sparse Key := [(key2359, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6)]

def rawRow18431 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block168
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18432 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6)]

def rawRow18433 : Integer.Sparse Key := [(key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2448, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6)]

def rawRow18434 : Integer.Sparse Key := [(key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6)]

def rawRow18435 : Integer.Sparse Key := [(key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6)]

def rawRow18436 : Integer.Sparse Key := [(key2448, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2353, 6), (key2359, 6), (key2448, 6), (key2515, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2515, 6)]

def rawRow18437 : Integer.Sparse Key := [(key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2353, 6), (key2515, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2515, 6), (key2454, 6)]

def rawRow18438 : Integer.Sparse Key := [(key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2353, 6), (key2578, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2515, 6)]

def rawRow18439 : Integer.Sparse Key := [(key2515, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2578, 6), (key2353, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6)]

def rawRow18440 : Integer.Sparse Key := [(key2454, 6), (key2515, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6)]

def rawRow18441 : Integer.Sparse Key := [(key2515, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2515, 6), (key2359, 6), (key2448, 6), (key2353, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2359, 6)]

def rawRow18442 : Integer.Sparse Key := [(key2454, 6), (key2454, 6), (key2515, 6), (key2448, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6)]

def rawRow18443 : Integer.Sparse Key := [(key2454, 6), (key2515, 6), (key2454, 6), (key2448, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2359, 6), (key2454, 6)]

def rawRow18444 : Integer.Sparse Key := [(key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2359, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2359, 6)]

def rawRow18445 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2515, 6), (key2353, 6), (key2448, 6), (key2448, 6), (key2448, 6)]

def rawRow18446 : Integer.Sparse Key := [(key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2353, 6), (key2448, 6), (key2448, 6)]

def rawRow18447 : Integer.Sparse Key := [(key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2353, 6), (key2448, 6)]

def rawRow18448 : Integer.Sparse Key := [(key2578, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2359, 6), (key2454, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2359, 6), (key2448, 6), (key2448, 6), (key2448, 6), (key2353, 6)]

def rawRow18449 : Integer.Sparse Key := [(key970, 6), (key970, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key1226, 6), (key1226, 6)]

def rawRow18450 : Integer.Sparse Key := [(key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6)]

def rawRow18451 : Integer.Sparse Key := [(key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6)]

def rawRow18452 : Integer.Sparse Key := [(key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key970, 6), (key1226, 6), (key970, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6)]

def rawRow18453 : Integer.Sparse Key := [(key1226, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1084, 6), (key1226, 6), (key1084, 6), (key1226, 6), (key970, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key970, 6), (key1084, 6), (key1084, 6), (key1084, 6), (key970, 6)]

def rawRow18457 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key83, 24), (key0, 24), (key83, 24)]

def rawRow18458 : Integer.Sparse Key := [(key83, 24), (key83, 24), (key83, 24), (key83, 24), (key0, 24)]

def rawRow18459 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2376, 6), (key2388, 6), (key2762, 6), (key2768, 6), (key2768, 6), (key2839, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2876, 6), (key2916, 6), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3019, 6), (key3028, 6)]

def rawRow18460 : Integer.Sparse Key := [(key2376, 6), (key2370, 6), (key2376, 6), (key2388, 6), (key2768, 6), (key2762, 6), (key2768, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2925, 6), (key2916, 6), (key3005, 6), (key3019, 6), (key3028, 6), (key3019, 6)]

def rawRow18461 : Integer.Sparse Key := [(key2376, 6), (key2376, 6), (key2370, 6), (key2388, 6), (key2768, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2876, 6), (key2845, 6), (key2845, 6), (key2839, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2916, 6), (key3005, 6), (key3028, 6), (key3019, 6), (key3019, 6)]

def rawRow18462 : Integer.Sparse Key := [(key2370, 6), (key2376, 6), (key2388, 6), (key2376, 6), (key2839, 6), (key2845, 6), (key2916, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2876, 6), (key2916, 6), (key2925, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key3019, 6), (key3005, 6), (key3019, 6), (key3028, 6)]

def rawRow18463 : Integer.Sparse Key := [(key2376, 6), (key2370, 6), (key2388, 6), (key2376, 6), (key2845, 6), (key2839, 6), (key2916, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key3005, 6), (key3028, 6), (key3019, 6)]

def rawRow18464 : Integer.Sparse Key := [(key2370, 6), (key2388, 6), (key2376, 6), (key2376, 6), (key2839, 6), (key2916, 6), (key2845, 6), (key2839, 6), (key2916, 6), (key2762, 6), (key2925, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2876, 6), (key3019, 6), (key3019, 6), (key3005, 6), (key3028, 6)]

def rawRow18465 : Integer.Sparse Key := [(key2388, 6), (key2370, 6), (key2376, 6), (key2376, 6), (key2916, 6), (key2839, 6), (key2845, 6), (key2916, 6), (key2839, 6), (key2925, 6), (key2762, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2768, 6), (key3019, 6), (key3019, 6), (key3028, 6), (key3005, 6)]

def rawRow18466 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2370, 6), (key2376, 6), (key2845, 6), (key2916, 6), (key2839, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key3019, 6), (key3028, 6), (key3005, 6), (key3019, 6)]

def rawRow18467 : Integer.Sparse Key := [(key2388, 6), (key2376, 6), (key2370, 6), (key2376, 6), (key2916, 6), (key2845, 6), (key2839, 6), (key2925, 6), (key2876, 6), (key2916, 6), (key2768, 6), (key2839, 6), (key2762, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key3019, 6), (key3028, 6), (key3019, 6), (key3005, 6)]

def rawRow18468 : Integer.Sparse Key := [(key2376, 6), (key2376, 6), (key2388, 6), (key2370, 6), (key2876, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2768, 6), (key2845, 6), (key2845, 6), (key2916, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key2839, 6), (key3028, 6), (key3005, 6), (key3019, 6), (key3019, 6)]

def rawRow18469 : Integer.Sparse Key := [(key2376, 6), (key2388, 6), (key2376, 6), (key2370, 6), (key2876, 6), (key2925, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2768, 6), (key2916, 6), (key2768, 6), (key2845, 6), (key2839, 6), (key2762, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key3005, 6), (key3019, 6)]

def rawRow18470 : Integer.Sparse Key := [(key2388, 6), (key2376, 6), (key2376, 6), (key2370, 6), (key2925, 6), (key2876, 6), (key2876, 6), (key2916, 6), (key2845, 6), (key2916, 6), (key2768, 6), (key2845, 6), (key2768, 6), (key2839, 6), (key2839, 6), (key2762, 6), (key3028, 6), (key3019, 6), (key3019, 6), (key3005, 6)]

def rawRow18471 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2404, 6), (key2435, 6), (key2583, 6), (key2589, 6), (key2589, 6), (key2839, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key2876, 6), (key3019, 6), (key3019, 6), (key3028, 6), (key2604, 6), (key2916, 6), (key2916, 6), (key2925, 6)]

def rawRow18472 : Integer.Sparse Key := [(key2404, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2589, 6), (key2583, 6), (key2589, 6), (key2845, 6), (key2839, 6), (key2876, 6), (key2839, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key3028, 6), (key3019, 6), (key2604, 6), (key2916, 6), (key2925, 6), (key2916, 6)]

def rawRow18473 : Integer.Sparse Key := [(key2404, 6), (key2404, 6), (key2398, 6), (key2435, 6), (key2589, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2876, 6), (key2845, 6), (key2845, 6), (key2839, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key3019, 6), (key2604, 6), (key2925, 6), (key2916, 6), (key2916, 6)]

def rawRow18474 : Integer.Sparse Key := [(key2398, 6), (key2404, 6), (key2435, 6), (key2404, 6), (key2839, 6), (key2845, 6), (key3019, 6), (key2583, 6), (key2589, 6), (key2839, 6), (key2876, 6), (key3019, 6), (key3028, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2916, 6), (key2604, 6), (key2916, 6), (key2925, 6)]

def rawRow18475 : Integer.Sparse Key := [(key2404, 6), (key2398, 6), (key2435, 6), (key2404, 6), (key2845, 6), (key2839, 6), (key3019, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2916, 6), (key2604, 6), (key2925, 6), (key2916, 6)]

def rawRow18476 : Integer.Sparse Key := [(key2398, 6), (key2435, 6), (key2404, 6), (key2404, 6), (key2839, 6), (key3019, 6), (key2845, 6), (key2839, 6), (key3019, 6), (key2583, 6), (key3028, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2876, 6), (key2916, 6), (key2916, 6), (key2604, 6), (key2925, 6)]

def rawRow18477 : Integer.Sparse Key := [(key2435, 6), (key2398, 6), (key2404, 6), (key2404, 6), (key3019, 6), (key2839, 6), (key2845, 6), (key3019, 6), (key2839, 6), (key3028, 6), (key2583, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2589, 6), (key2916, 6), (key2916, 6), (key2925, 6), (key2604, 6)]

def rawRow18478 : Integer.Sparse Key := [(key2404, 6), (key2435, 6), (key2398, 6), (key2404, 6), (key2845, 6), (key3019, 6), (key2839, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2916, 6), (key2925, 6), (key2604, 6), (key2916, 6)]

def rawRow18479 : Integer.Sparse Key := [(key2435, 6), (key2404, 6), (key2398, 6), (key2404, 6), (key3019, 6), (key2845, 6), (key2839, 6), (key3028, 6), (key2876, 6), (key3019, 6), (key2589, 6), (key2839, 6), (key2583, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2916, 6), (key2925, 6), (key2916, 6), (key2604, 6)]

def rawRow18480 : Integer.Sparse Key := [(key2404, 6), (key2404, 6), (key2435, 6), (key2398, 6), (key2876, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key2589, 6), (key2845, 6), (key2845, 6), (key3019, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2839, 6), (key2925, 6), (key2604, 6), (key2916, 6), (key2916, 6)]

def rawRow18481 : Integer.Sparse Key := [(key2404, 6), (key2435, 6), (key2404, 6), (key2398, 6), (key2876, 6), (key3028, 6), (key2876, 6), (key2845, 6), (key3019, 6), (key2589, 6), (key3019, 6), (key2589, 6), (key2845, 6), (key2839, 6), (key2583, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key2604, 6), (key2916, 6)]

def rawRow18482 : Integer.Sparse Key := [(key2435, 6), (key2404, 6), (key2404, 6), (key2398, 6), (key3028, 6), (key2876, 6), (key2876, 6), (key3019, 6), (key2845, 6), (key3019, 6), (key2589, 6), (key2845, 6), (key2589, 6), (key2839, 6), (key2839, 6), (key2583, 6), (key2925, 6), (key2916, 6), (key2916, 6), (key2604, 6)]

def rawRow18483 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2370, 6), (key2376, 6), (key2388, 6), (key2762, 6), (key2768, 6), (key2839, 6), (key2876, 6), (key2916, 6), (key2925, 6), (key3005, 6), (key3019, 6), (key3028, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6)]

def rawRow18484 : Integer.Sparse Key := [(key2470, 6), (key2464, 6), (key2478, 6), (key2501, 6), (key2376, 6), (key2370, 6), (key2388, 6), (key2768, 6), (key2762, 6), (key2876, 6), (key2839, 6), (key2925, 6), (key2916, 6), (key3005, 6), (key3028, 6), (key3019, 6), (key2589, 6), (key2768, 6), (key2876, 6), (key2845, 6)]

def rawRow18485 : Integer.Sparse Key := [(key2464, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2370, 6), (key2388, 6), (key2376, 6), (key2839, 6), (key2916, 6), (key2762, 6), (key2925, 6), (key2768, 6), (key2876, 6), (key3019, 6), (key3005, 6), (key3028, 6), (key2589, 6), (key2845, 6), (key2768, 6), (key2876, 6)]

def rawRow18486 : Integer.Sparse Key := [(key2478, 6), (key2464, 6), (key2470, 6), (key2501, 6), (key2388, 6), (key2370, 6), (key2376, 6), (key2916, 6), (key2839, 6), (key2925, 6), (key2762, 6), (key2876, 6), (key2768, 6), (key3019, 6), (key3028, 6), (key3005, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2768, 6)]

def rawRow18487 : Integer.Sparse Key := [(key2470, 6), (key2478, 6), (key2464, 6), (key2501, 6), (key2376, 6), (key2388, 6), (key2370, 6), (key2876, 6), (key2925, 6), (key2768, 6), (key2916, 6), (key2762, 6), (key2839, 6), (key3028, 6), (key3005, 6), (key3019, 6), (key2589, 6), (key2876, 6), (key2768, 6), (key2845, 6)]

def rawRow18488 : Integer.Sparse Key := [(key2478, 6), (key2470, 6), (key2464, 6), (key2501, 6), (key2388, 6), (key2376, 6), (key2370, 6), (key2925, 6), (key2876, 6), (key2916, 6), (key2768, 6), (key2839, 6), (key2762, 6), (key3028, 6), (key3019, 6), (key3005, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2768, 6)]

def rawRow18489 : Integer.Sparse Key := [(key2464, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2398, 6), (key2404, 6), (key2435, 6), (key2583, 6), (key2589, 6), (key2839, 6), (key2876, 6), (key3019, 6), (key3028, 6), (key2604, 6), (key2916, 6), (key2925, 6), (key2768, 6), (key2589, 6), (key2845, 6), (key2876, 6)]

def rawRow18490 : Integer.Sparse Key := [(key2470, 6), (key2464, 6), (key2501, 6), (key2478, 6), (key2404, 6), (key2398, 6), (key2435, 6), (key2589, 6), (key2583, 6), (key2876, 6), (key2839, 6), (key3028, 6), (key3019, 6), (key2604, 6), (key2925, 6), (key2916, 6), (key2768, 6), (key2589, 6), (key2876, 6), (key2845, 6)]

def rawRow18491 : Integer.Sparse Key := [(key2464, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2398, 6), (key2435, 6), (key2404, 6), (key2839, 6), (key3019, 6), (key2583, 6), (key3028, 6), (key2589, 6), (key2876, 6), (key2916, 6), (key2604, 6), (key2925, 6), (key2768, 6), (key2845, 6), (key2589, 6), (key2876, 6)]

def rawRow18492 : Integer.Sparse Key := [(key2501, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2435, 6), (key2398, 6), (key2404, 6), (key3019, 6), (key2839, 6), (key3028, 6), (key2583, 6), (key2876, 6), (key2589, 6), (key2916, 6), (key2925, 6), (key2604, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2589, 6)]

def rawRow18493 : Integer.Sparse Key := [(key2470, 6), (key2501, 6), (key2464, 6), (key2478, 6), (key2404, 6), (key2435, 6), (key2398, 6), (key2876, 6), (key3028, 6), (key2589, 6), (key3019, 6), (key2583, 6), (key2839, 6), (key2925, 6), (key2604, 6), (key2916, 6), (key2768, 6), (key2876, 6), (key2589, 6), (key2845, 6)]

def rawRow18494 : Integer.Sparse Key := [(key2501, 6), (key2470, 6), (key2464, 6), (key2478, 6), (key2435, 6), (key2404, 6), (key2398, 6), (key3028, 6), (key2876, 6), (key3019, 6), (key2589, 6), (key2839, 6), (key2583, 6), (key2925, 6), (key2916, 6), (key2604, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2589, 6)]

def rawRow18495 : Integer.Sparse Key := [(key2464, 6), (key2478, 6), (key2501, 6), (key2470, 6), (key2464, 6), (key2478, 6), (key2501, 6), (key2370, 6), (key2388, 6), (key2762, 6), (key2925, 6), (key3005, 6), (key3028, 6), (key2589, 6), (key2768, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2768, 6), (key2876, 6)]

def rawRow18496 : Integer.Sparse Key := [(key2478, 6), (key2464, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2464, 6), (key2501, 6), (key2388, 6), (key2370, 6), (key2925, 6), (key2762, 6), (key3028, 6), (key3005, 6), (key2589, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2589, 6), (key2876, 6), (key2768, 6)]

def rawRow18497 : Integer.Sparse Key := [(key2464, 6), (key2501, 6), (key2478, 6), (key2470, 6), (key2464, 6), (key2501, 6), (key2478, 6), (key2398, 6), (key2435, 6), (key2583, 6), (key3028, 6), (key2604, 6), (key2925, 6), (key2768, 6), (key2589, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2589, 6), (key2876, 6)]

def rawRow18498 : Integer.Sparse Key := [(key2501, 6), (key2464, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2464, 6), (key2478, 6), (key2435, 6), (key2398, 6), (key3028, 6), (key2583, 6), (key2925, 6), (key2604, 6), (key2768, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2768, 6), (key2876, 6), (key2589, 6)]

def rawRow18499 : Integer.Sparse Key := [(key2478, 6), (key2501, 6), (key2464, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2464, 6), (key2570, 6), (key2575, 6), (key2388, 6), (key2435, 6), (key2370, 6), (key2762, 6), (key2876, 6), (key2589, 6), (key2768, 6), (key2845, 6), (key2876, 6), (key2589, 6), (key2768, 6)]

def rawRow18500 : Integer.Sparse Key := [(key2501, 6), (key2478, 6), (key2464, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2464, 6), (key2575, 6), (key2570, 6), (key2435, 6), (key2388, 6), (key2398, 6), (key2583, 6), (key2876, 6), (key2768, 6), (key2589, 6), (key2845, 6), (key2876, 6), (key2768, 6), (key2589, 6)]

def rawRow18501 : Integer.Sparse Key := [(key2470, 6), (key2478, 6), (key2501, 6), (key2464, 6), (key2568, 6), (key2570, 6), (key2575, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2370, 6), (key2762, 6), (key2839, 6), (key2876, 6), (key2589, 6), (key2768, 6), (key2845, 6)]

def rawRow18502 : Integer.Sparse Key := [(key2478, 6), (key2470, 6), (key2501, 6), (key2464, 6), (key2570, 6), (key2568, 6), (key2575, 6), (key2388, 6), (key2376, 6), (key2478, 6), (key2404, 6), (key2501, 6), (key2435, 6), (key2370, 6), (key2839, 6), (key2762, 6), (key2876, 6), (key2589, 6), (key2845, 6), (key2768, 6)]

def rawRow18503 : Integer.Sparse Key := [(key2470, 6), (key2501, 6), (key2478, 6), (key2464, 6), (key2568, 6), (key2575, 6), (key2570, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2398, 6), (key2583, 6), (key2839, 6), (key2876, 6), (key2768, 6), (key2589, 6), (key2845, 6)]

def rawRow18504 : Integer.Sparse Key := [(key2501, 6), (key2470, 6), (key2478, 6), (key2464, 6), (key2575, 6), (key2568, 6), (key2570, 6), (key2435, 6), (key2404, 6), (key2501, 6), (key2376, 6), (key2478, 6), (key2388, 6), (key2398, 6), (key2839, 6), (key2583, 6), (key2876, 6), (key2768, 6), (key2845, 6), (key2589, 6)]

def rawRow18505 : Integer.Sparse Key := [(key2478, 6), (key2501, 6), (key2470, 6), (key2464, 6), (key2570, 6), (key2575, 6), (key2568, 6), (key2478, 6), (key2501, 6), (key2388, 6), (key2435, 6), (key2376, 6), (key2404, 6), (key2464, 6), (key2370, 6), (key2762, 6), (key2876, 6), (key2845, 6), (key2589, 6), (key2768, 6)]

def rawRow18506 : Integer.Sparse Key := [(key2501, 6), (key2478, 6), (key2470, 6), (key2464, 6), (key2575, 6), (key2570, 6), (key2568, 6), (key2501, 6), (key2478, 6), (key2435, 6), (key2388, 6), (key2404, 6), (key2376, 6), (key2464, 6), (key2398, 6), (key2583, 6), (key2876, 6), (key2845, 6), (key2768, 6), (key2589, 6)]

def rawRow18507 : Integer.Sparse Key := [(key2568, 6), (key2568, 6), (key2570, 6), (key2575, 6), (key2376, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2404, 6), (key2470, 6), (key2470, 6), (key2478, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2501, 6), (key2370, 6), (key2762, 6), (key2839, 6), (key2839, 6)]

def rawRow18508 : Integer.Sparse Key := [(key2568, 6), (key2570, 6), (key2568, 6), (key2575, 6), (key2376, 6), (key2388, 6), (key2376, 6), (key2470, 6), (key2478, 6), (key2404, 6), (key2478, 6), (key2404, 6), (key2470, 6), (key2501, 6), (key2435, 6), (key2501, 6), (key2370, 6), (key2839, 6), (key2762, 6), (key2839, 6)]

def rawRow18509 : Integer.Sparse Key := [(key2570, 6), (key2568, 6), (key2568, 6), (key2575, 6), (key2388, 6), (key2376, 6), (key2376, 6), (key2478, 6), (key2470, 6), (key2478, 6), (key2404, 6), (key2470, 6), (key2404, 6), (key2501, 6), (key2501, 6), (key2435, 6), (key2370, 6), (key2839, 6), (key2839, 6), (key2762, 6)]

def rawRow18510 : Integer.Sparse Key := [(key2568, 6), (key2568, 6), (key2575, 6), (key2570, 6), (key2404, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2376, 6), (key2470, 6), (key2470, 6), (key2501, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2478, 6), (key2398, 6), (key2583, 6), (key2839, 6), (key2839, 6)]

def rawRow18511 : Integer.Sparse Key := [(key2568, 6), (key2575, 6), (key2568, 6), (key2570, 6), (key2404, 6), (key2435, 6), (key2404, 6), (key2470, 6), (key2501, 6), (key2376, 6), (key2501, 6), (key2376, 6), (key2470, 6), (key2478, 6), (key2388, 6), (key2478, 6), (key2398, 6), (key2839, 6), (key2583, 6), (key2839, 6)]

def rawRow18512 : Integer.Sparse Key := [(key2575, 6), (key2568, 6), (key2568, 6), (key2570, 6), (key2435, 6), (key2404, 6), (key2404, 6), (key2501, 6), (key2470, 6), (key2501, 6), (key2376, 6), (key2470, 6), (key2376, 6), (key2478, 6), (key2478, 6), (key2388, 6), (key2398, 6), (key2839, 6), (key2839, 6), (key2583, 6)]

def rawRow18513 : Integer.Sparse Key := [(key2568, 6), (key2570, 6), (key2575, 6), (key2568, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2376, 6), (key2388, 6), (key2404, 6), (key2478, 6), (key2435, 6), (key2501, 6), (key2376, 6), (key2404, 6), (key2470, 6), (key2464, 6), (key2370, 6), (key2762, 6), (key2839, 6)]

def rawRow18514 : Integer.Sparse Key := [(key2570, 6), (key2568, 6), (key2575, 6), (key2568, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2388, 6), (key2376, 6), (key2478, 6), (key2404, 6), (key2501, 6), (key2435, 6), (key2376, 6), (key2470, 6), (key2404, 6), (key2464, 6), (key2370, 6), (key2839, 6), (key2762, 6)]

def rawRow18515 : Integer.Sparse Key := [(key2568, 6), (key2575, 6), (key2570, 6), (key2568, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2404, 6), (key2435, 6), (key2376, 6), (key2501, 6), (key2388, 6), (key2478, 6), (key2404, 6), (key2376, 6), (key2470, 6), (key2464, 6), (key2398, 6), (key2583, 6), (key2839, 6)]

def rawRow18516 : Integer.Sparse Key := [(key2575, 6), (key2568, 6), (key2570, 6), (key2568, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2435, 6), (key2404, 6), (key2501, 6), (key2376, 6), (key2478, 6), (key2388, 6), (key2404, 6), (key2470, 6), (key2376, 6), (key2464, 6), (key2398, 6), (key2839, 6), (key2583, 6)]

def rawRow18517 : Integer.Sparse Key := [(key2570, 6), (key2575, 6), (key2568, 6), (key2568, 6), (key2478, 6), (key2501, 6), (key2470, 6), (key2478, 6), (key2501, 6), (key2388, 6), (key2435, 6), (key2376, 6), (key2404, 6), (key2470, 6), (key2376, 6), (key2404, 6), (key2464, 6), (key2464, 6), (key2370, 6), (key2762, 6)]

def rawRow18518 : Integer.Sparse Key := [(key2575, 6), (key2570, 6), (key2568, 6), (key2568, 6), (key2501, 6), (key2478, 6), (key2470, 6), (key2501, 6), (key2478, 6), (key2435, 6), (key2388, 6), (key2404, 6), (key2376, 6), (key2470, 6), (key2404, 6), (key2376, 6), (key2464, 6), (key2464, 6), (key2398, 6), (key2583, 6)]

def rawRow18519 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 24), (key1104, 24), (key1230, 24)]

def rawRow18520 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1104, 24), (key1230, 24), (key1104, 24)]

def rawRow18521 : Integer.Sparse Key := [(key991, 24), (key1026, 24), (key1230, 24), (key1104, 24), (key1104, 24)]

def rawRow18522 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1026, 24), (key1104, 24), (key1230, 24)]

def rawRow18523 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1026, 24), (key1230, 24), (key1104, 24)]

def rawRow18524 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1104, 24), (key1026, 24), (key1230, 24)]

def rawRow18525 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1104, 24), (key1230, 24), (key1026, 24)]

def rawRow18526 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1230, 24), (key1026, 24), (key1104, 24)]

def rawRow18527 : Integer.Sparse Key := [(key991, 24), (key1104, 24), (key1230, 24), (key1104, 24), (key1026, 24)]

def rawRow18528 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1026, 24), (key1104, 24), (key1104, 24)]

def rawRow18529 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1104, 24), (key1026, 24), (key1104, 24)]

def rawRow18530 : Integer.Sparse Key := [(key991, 24), (key1230, 24), (key1104, 24), (key1104, 24), (key1026, 24)]

def rawRow18531 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1104, 24), (key1104, 24), (key1230, 24)]

def rawRow18532 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1104, 24), (key1230, 24), (key1104, 24)]

def rawRow18533 : Integer.Sparse Key := [(key1026, 24), (key991, 24), (key1230, 24), (key1104, 24), (key1104, 24)]

def rawRow18534 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key991, 24), (key1104, 24), (key1230, 24)]

def rawRow18535 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key991, 24), (key1230, 24), (key1104, 24)]

def rawRow18536 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1104, 24), (key991, 24), (key1230, 24)]

def rawRow18537 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1104, 24), (key1230, 24), (key991, 24)]

def rawRow18538 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1230, 24), (key991, 24), (key1104, 24)]

def rawRow18539 : Integer.Sparse Key := [(key1026, 24), (key1104, 24), (key1230, 24), (key1104, 24), (key991, 24)]

def rawRow18540 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key991, 24), (key1104, 24), (key1104, 24)]

def rawRow18541 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key1104, 24), (key991, 24), (key1104, 24)]

def rawRow18542 : Integer.Sparse Key := [(key1026, 24), (key1230, 24), (key1104, 24), (key1104, 24), (key991, 24)]

def rawRow18543 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1026, 24), (key1104, 24), (key1230, 24)]

def rawRow18544 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1026, 24), (key1230, 24), (key1104, 24)]

def rawRow18545 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1104, 24), (key1026, 24), (key1230, 24)]

def rawRow18546 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1104, 24), (key1230, 24), (key1026, 24)]

def rawRow18547 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1230, 24), (key1026, 24), (key1104, 24)]

def rawRow18548 : Integer.Sparse Key := [(key1104, 24), (key991, 24), (key1230, 24), (key1104, 24), (key1026, 24)]

def rawRow18549 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key991, 24), (key1104, 24), (key1230, 24)]

def rawRow18550 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key991, 24), (key1230, 24), (key1104, 24)]

def rawRow18551 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1104, 24), (key991, 24), (key1230, 24)]

def rawRow18552 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1104, 24), (key1230, 24), (key991, 24)]

def rawRow18553 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1230, 24), (key991, 24), (key1104, 24)]

def rawRow18554 : Integer.Sparse Key := [(key1104, 24), (key1026, 24), (key1230, 24), (key1104, 24), (key991, 24)]

def rawRow18555 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key991, 24), (key1026, 24), (key1230, 24)]

def rawRow18556 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key991, 24), (key1230, 24), (key1026, 24)]

def rawRow18557 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1026, 24), (key991, 24), (key1230, 24)]

def rawRow18558 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1026, 24), (key1230, 24), (key991, 24)]

def rawRow18559 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1230, 24), (key991, 24), (key1026, 24)]

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

def rawRow18560 : Integer.Sparse Key := [(key1104, 24), (key1104, 24), (key1230, 24), (key1026, 24), (key991, 24)]

def rawRow18561 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key991, 24), (key1026, 24), (key1104, 24)]

def rawRow18562 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key991, 24), (key1104, 24), (key1026, 24)]

def rawRow18563 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1026, 24), (key991, 24), (key1104, 24)]

def rawRow18564 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1026, 24), (key1104, 24), (key991, 24)]

def rawRow18565 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1104, 24), (key991, 24), (key1026, 24)]

def rawRow18566 : Integer.Sparse Key := [(key1104, 24), (key1230, 24), (key1104, 24), (key1026, 24), (key991, 24)]

def rawRow18567 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1026, 24), (key1104, 24), (key1104, 24)]

def rawRow18568 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1104, 24), (key1026, 24), (key1104, 24)]

def rawRow18569 : Integer.Sparse Key := [(key1230, 24), (key991, 24), (key1104, 24), (key1104, 24), (key1026, 24)]

def rawRow18570 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key991, 24), (key1104, 24), (key1104, 24)]

def rawRow18571 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key1104, 24), (key991, 24), (key1104, 24)]

def rawRow18572 : Integer.Sparse Key := [(key1230, 24), (key1026, 24), (key1104, 24), (key1104, 24), (key991, 24)]

def rawRow18573 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key991, 24), (key1026, 24), (key1104, 24)]

def rawRow18574 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key991, 24), (key1104, 24), (key1026, 24)]

def rawRow18575 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1026, 24), (key991, 24), (key1104, 24)]

def rawRow18576 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1026, 24), (key1104, 24), (key991, 24)]

def rawRow18577 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1104, 24), (key991, 24), (key1026, 24)]

def rawRow18578 : Integer.Sparse Key := [(key1230, 24), (key1104, 24), (key1104, 24), (key1026, 24), (key991, 24)]

def rawRow18639 : Integer.Sparse Key := [(key2355, 6), (key2355, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2512, 6), (key2512, 6)]

def rawRow18640 : Integer.Sparse Key := [(key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6)]

def rawRow18641 : Integer.Sparse Key := [(key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6)]

def rawRow18642 : Integer.Sparse Key := [(key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6)]

def rawRow18643 : Integer.Sparse Key := [(key2512, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2450, 6), (key2512, 6), (key2450, 6), (key2512, 6), (key2355, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2355, 6), (key2450, 6), (key2450, 6), (key2450, 6), (key2355, 6)]

def rawRow18644 : Integer.Sparse Key := [(key968, 24), (key1082, 24), (key1082, 24), (key1082, 24), (key1082, 24)]

def rawRow18645 : Integer.Sparse Key := [(key1082, 24), (key968, 24), (key1082, 24), (key1082, 24), (key1082, 24)]

def rawRow18646 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key968, 24), (key1082, 24), (key1082, 24)]

def rawRow18647 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key1082, 24), (key968, 24), (key1082, 24)]

def rawRow18648 : Integer.Sparse Key := [(key1082, 24), (key1082, 24), (key1082, 24), (key1082, 24), (key968, 24)]

def rawRow18649 : Integer.Sparse Key := [(key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2)]

def rawRow18650 : Integer.Sparse Key := [(key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2)]

def rawRow18651 : Integer.Sparse Key := [(key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2873, 2), (key2873, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2841, 2)]

def rawRow18652 : Integer.Sparse Key := [(key2841, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2585, 2), (key2873, 2), (key2585, 2), (key2764, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2764, 2)]

def rawRow18653 : Integer.Sparse Key := [(key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2841, 2), (key2841, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2764, 2), (key2841, 2), (key2764, 2), (key2873, 2), (key2841, 2), (key2873, 2), (key2585, 2), (key2841, 2), (key2585, 2), (key2873, 2), (key2764, 2), (key2873, 2), (key2585, 2), (key2764, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2585, 2), (key2841, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2841, 2), (key2585, 2), (key2841, 2), (key2764, 2), (key2841, 2), (key2585, 2), (key2764, 2), (key2585, 2)]

def rawRow18654 : Integer.Sparse Key := [(key2351, 24), (key2446, 24), (key2446, 24), (key2446, 24), (key2446, 24)]

def rawRow18655 : Integer.Sparse Key := [(key2446, 24), (key2351, 24), (key2446, 24), (key2446, 24), (key2446, 24)]

def rawRow18656 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2351, 24), (key2446, 24), (key2446, 24)]

def rawRow18657 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2446, 24), (key2351, 24), (key2446, 24)]

def rawRow18658 : Integer.Sparse Key := [(key2446, 24), (key2446, 24), (key2446, 24), (key2446, 24), (key2351, 24)]

def rawRow18659 : Integer.Sparse Key := [(key971, 6), (key979, 6), (key979, 6), (key979, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key1228, 6), (key1228, 6), (key1228, 6), (key1245, 6)]

def rawRow18660 : Integer.Sparse Key := [(key979, 6), (key971, 6), (key979, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key1245, 6), (key1228, 6)]

def rawRow18661 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key971, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1245, 6), (key1228, 6), (key1228, 6)]

def rawRow18662 : Integer.Sparse Key := [(key979, 6), (key979, 6), (key979, 6), (key971, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key1228, 6), (key1228, 6)]

def rawRow18663 : Integer.Sparse Key := [(key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key971, 6), (key979, 6), (key979, 6), (key1085, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1164, 6), (key1228, 6), (key1228, 6), (key1245, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6)]

def rawRow18664 : Integer.Sparse Key := [(key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key979, 6), (key971, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1245, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6)]

def rawRow18665 : Integer.Sparse Key := [(key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key979, 6), (key979, 6), (key971, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key1228, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6)]

def rawRow18666 : Integer.Sparse Key := [(key1085, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key971, 6), (key979, 6), (key1085, 6), (key1164, 6), (key1228, 6), (key1245, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1164, 6)]

def rawRow18667 : Integer.Sparse Key := [(key1093, 6), (key1085, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key979, 6), (key971, 6), (key1164, 6), (key1085, 6), (key1245, 6), (key1228, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1164, 6), (key1093, 6)]

def rawRow18668 : Integer.Sparse Key := [(key1085, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1228, 6), (key971, 6), (key1245, 6), (key979, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1164, 6)]

def rawRow18669 : Integer.Sparse Key := [(key1228, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1245, 6), (key971, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key979, 6)]

def rawRow18670 : Integer.Sparse Key := [(key1093, 6), (key1228, 6), (key1085, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1164, 6), (key1245, 6), (key979, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1164, 6), (key979, 6), (key1093, 6)]

def rawRow18671 : Integer.Sparse Key := [(key1228, 6), (key1093, 6), (key1085, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1245, 6), (key1164, 6), (key1228, 6), (key979, 6), (key1085, 6), (key971, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1164, 6), (key1093, 6), (key979, 6)]

def rawRow18672 : Integer.Sparse Key := [(key1093, 6), (key1093, 6), (key1228, 6), (key1085, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1085, 6), (key1164, 6), (key979, 6), (key1093, 6), (key1093, 6)]

def rawRow18673 : Integer.Sparse Key := [(key1093, 6), (key1228, 6), (key1093, 6), (key1085, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1085, 6), (key971, 6), (key1085, 6), (key1164, 6), (key1093, 6), (key979, 6), (key1093, 6)]

def rawRow18674 : Integer.Sparse Key := [(key1228, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1228, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1093, 6), (key979, 6), (key1085, 6), (key1085, 6), (key971, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key979, 6)]

def rawRow18675 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1164, 6), (key1245, 6), (key979, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key1228, 6), (key971, 6), (key1085, 6), (key1085, 6), (key1085, 6)]

def rawRow18676 : Integer.Sparse Key := [(key1164, 6), (key1164, 6), (key1245, 6), (key1164, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key979, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1093, 6), (key1085, 6), (key971, 6), (key1085, 6), (key1085, 6)]

def rawRow18677 : Integer.Sparse Key := [(key1164, 6), (key1245, 6), (key1164, 6), (key1164, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1228, 6), (key979, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1085, 6), (key1085, 6), (key971, 6), (key1085, 6)]

def rawRow18678 : Integer.Sparse Key := [(key1245, 6), (key1164, 6), (key1164, 6), (key1164, 6), (key1228, 6), (key1093, 6), (key1093, 6), (key1228, 6), (key1093, 6), (key1228, 6), (key979, 6), (key1093, 6), (key979, 6), (key1093, 6), (key1093, 6), (key979, 6), (key1085, 6), (key1085, 6), (key1085, 6), (key971, 6)]

def rawRow18679 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key86, 24), (key86, 24), (key147, 24)]

def rawRow18680 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key86, 24), (key147, 24), (key86, 24)]

def rawRow18681 : Integer.Sparse Key := [(key3, 24), (key86, 24), (key147, 24), (key86, 24), (key86, 24)]

def rawRow18682 : Integer.Sparse Key := [(key3, 24), (key147, 24), (key86, 24), (key86, 24), (key86, 24)]

def rawRow18683 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key86, 24), (key86, 24), (key147, 24)]

def rawRow18684 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key86, 24), (key147, 24), (key86, 24)]

def rawRow18685 : Integer.Sparse Key := [(key86, 24), (key3, 24), (key147, 24), (key86, 24), (key86, 24)]

def rawRow18686 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key3, 24), (key86, 24), (key147, 24)]

def rawRow18687 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key3, 24), (key147, 24), (key86, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block170
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18688 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key86, 24), (key3, 24), (key147, 24)]

def rawRow18689 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key86, 24), (key147, 24), (key3, 24)]

def rawRow18690 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key147, 24), (key3, 24), (key86, 24)]

def rawRow18691 : Integer.Sparse Key := [(key86, 24), (key86, 24), (key147, 24), (key86, 24), (key3, 24)]

def rawRow18692 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key3, 24), (key86, 24), (key86, 24)]

def rawRow18693 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key86, 24), (key3, 24), (key86, 24)]

def rawRow18694 : Integer.Sparse Key := [(key86, 24), (key147, 24), (key86, 24), (key86, 24), (key3, 24)]

def rawRow18695 : Integer.Sparse Key := [(key147, 24), (key3, 24), (key86, 24), (key86, 24), (key86, 24)]

def rawRow18696 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key3, 24), (key86, 24), (key86, 24)]

def rawRow18697 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key86, 24), (key3, 24), (key86, 24)]

def rawRow18698 : Integer.Sparse Key := [(key147, 24), (key86, 24), (key86, 24), (key86, 24), (key3, 24)]

def rawRow18699 : Integer.Sparse Key := [(key993, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1232, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1242, 2)]

def rawRow18700 : Integer.Sparse Key := [(key1001, 2), (key993, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1015, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1242, 2), (key1235, 2)]

def rawRow18701 : Integer.Sparse Key := [(key1001, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2)]

def rawRow18702 : Integer.Sparse Key := [(key1015, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key993, 2), (key1071, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1028, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2)]

def rawRow18703 : Integer.Sparse Key := [(key1028, 2), (key1036, 2), (key1036, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1123, 2), (key1232, 2), (key1232, 2), (key1235, 2), (key993, 2), (key1001, 2), (key1001, 2), (key1106, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1232, 2), (key1232, 2), (key1242, 2), (key993, 2), (key1001, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1015, 2), (key1028, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1071, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1150, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1036, 2), (key1071, 2), (key1114, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1123, 2), (key1150, 2)]

def rawRow18704 : Integer.Sparse Key := [(key1036, 2), (key1028, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1123, 2), (key1106, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1235, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1114, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1015, 2), (key993, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1071, 2), (key1028, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1150, 2), (key1106, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1232, 2), (key1242, 2), (key1232, 2), (key1242, 2), (key1235, 2), (key1001, 2), (key1015, 2), (key1001, 2), (key1036, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1150, 2), (key1114, 2), (key1150, 2), (key1123, 2)]

def rawRow18705 : Integer.Sparse Key := [(key1036, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1150, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1232, 2), (key1015, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key993, 2), (key993, 2), (key1071, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1028, 2), (key1028, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1106, 2), (key1106, 2), (key1242, 2), (key1242, 2), (key1235, 2), (key1235, 2), (key1232, 2), (key1232, 2), (key1015, 2), (key1001, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1036, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1114, 2), (key1114, 2)]

def rawRow18706 : Integer.Sparse Key := [(key1106, 2), (key1114, 2), (key1232, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1150, 2), (key1232, 2), (key1242, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1028, 2), (key1036, 2), (key1106, 2), (key1123, 2), (key1232, 2), (key1235, 2), (key993, 2), (key1001, 2), (key1106, 2), (key1150, 2), (key1232, 2), (key1242, 2), (key993, 2), (key1015, 2), (key1028, 2), (key1071, 2), (key1235, 2), (key1242, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1071, 2), (key1123, 2), (key1150, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1015, 2), (key1036, 2), (key1071, 2), (key1123, 2), (key1150, 2)]

def rawRow18707 : Integer.Sparse Key := [(key1114, 2), (key1106, 2), (key1232, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1036, 2), (key1028, 2), (key1123, 2), (key1106, 2), (key1235, 2), (key1232, 2), (key1001, 2), (key993, 2), (key1150, 2), (key1106, 2), (key1242, 2), (key1232, 2), (key1015, 2), (key993, 2), (key1071, 2), (key1028, 2), (key1242, 2), (key1235, 2), (key1015, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1123, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1015, 2), (key1001, 2), (key1071, 2), (key1036, 2), (key1150, 2), (key1123, 2)]

def rawRow18708 : Integer.Sparse Key := [(key1106, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1232, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1106, 2), (key1232, 2), (key1028, 2), (key1235, 2), (key1036, 2), (key1123, 2), (key1106, 2), (key1232, 2), (key993, 2), (key1242, 2), (key1001, 2), (key1150, 2), (key1028, 2), (key1235, 2), (key993, 2), (key1242, 2), (key1015, 2), (key1071, 2), (key1036, 2), (key1123, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1071, 2), (key1114, 2), (key1036, 2), (key1123, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1036, 2), (key1123, 2), (key1001, 2), (key1150, 2), (key1015, 2), (key1071, 2)]

def rawRow18709 : Integer.Sparse Key := [(key1232, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1106, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1232, 2), (key1106, 2), (key1235, 2), (key1028, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1106, 2), (key1242, 2), (key993, 2), (key1150, 2), (key1001, 2), (key1235, 2), (key1028, 2), (key1242, 2), (key993, 2), (key1071, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1071, 2), (key1015, 2), (key1114, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1123, 2), (key1036, 2), (key1150, 2), (key1001, 2), (key1071, 2), (key1015, 2)]

def rawRow18710 : Integer.Sparse Key := [(key1114, 2), (key1232, 2), (key1106, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1071, 2), (key1242, 2), (key1015, 2), (key1235, 2), (key993, 2), (key1028, 2), (key1071, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1001, 2), (key1036, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1150, 2), (key1001, 2), (key1114, 2), (key1071, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1001, 2), (key1036, 2)]

def rawRow18711 : Integer.Sparse Key := [(key1232, 2), (key1114, 2), (key1106, 2), (key1235, 2), (key1123, 2), (key1232, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1106, 2), (key1242, 2), (key1150, 2), (key1232, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1235, 2), (key1123, 2), (key1232, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1232, 2), (key1001, 2), (key1106, 2), (key993, 2), (key1242, 2), (key1071, 2), (key1235, 2), (key1015, 2), (key1028, 2), (key993, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1001, 2), (key1123, 2), (key1114, 2), (key1036, 2), (key1150, 2), (key1114, 2), (key1001, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1015, 2), (key1036, 2), (key1001, 2)]

def rawRow18712 : Integer.Sparse Key := [(key1123, 2), (key1123, 2), (key1235, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key993, 2), (key1106, 2), (key1106, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1232, 2), (key1232, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2)]

def rawRow18713 : Integer.Sparse Key := [(key1123, 2), (key1235, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1150, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1106, 2), (key993, 2), (key1028, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1036, 2)]

def rawRow18714 : Integer.Sparse Key := [(key1235, 2), (key1123, 2), (key1123, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1106, 2), (key1106, 2), (key1028, 2), (key1242, 2), (key1150, 2), (key1150, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1242, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1071, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1028, 2), (key993, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1114, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1001, 2)]

def rawRow18715 : Integer.Sparse Key := [(key1071, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1242, 2), (key1015, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1235, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key1232, 2), (key993, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2), (key1106, 2)]

def rawRow18716 : Integer.Sparse Key := [(key1150, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1232, 2), (key1232, 2), (key1001, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1106, 2), (key993, 2), (key993, 2), (key1028, 2), (key1028, 2), (key1106, 2), (key1106, 2)]

def rawRow18717 : Integer.Sparse Key := [(key1150, 2), (key1242, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1106, 2), (key993, 2), (key1028, 2)]

def rawRow18718 : Integer.Sparse Key := [(key1242, 2), (key1150, 2), (key1150, 2), (key1242, 2), (key1150, 2), (key1242, 2), (key1071, 2), (key1150, 2), (key1071, 2), (key1150, 2), (key1150, 2), (key1071, 2), (key1235, 2), (key1123, 2), (key1123, 2), (key1235, 2), (key1123, 2), (key1235, 2), (key1015, 2), (key1123, 2), (key1015, 2), (key1123, 2), (key1123, 2), (key1015, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1036, 2), (key1114, 2), (key1036, 2), (key1232, 2), (key1114, 2), (key1232, 2), (key1001, 2), (key1114, 2), (key1001, 2), (key1232, 2), (key1036, 2), (key1232, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1114, 2), (key1036, 2), (key1114, 2), (key1001, 2), (key1036, 2), (key1001, 2), (key1106, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key1106, 2), (key993, 2), (key1106, 2), (key1028, 2), (key1106, 2), (key993, 2), (key1028, 2), (key993, 2)]

def rawRow18719 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1087, 24), (key1087, 24), (key1160, 24)]

def rawRow18720 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1087, 24), (key1160, 24), (key1087, 24)]

def rawRow18721 : Integer.Sparse Key := [(key973, 24), (key1087, 24), (key1160, 24), (key1087, 24), (key1087, 24)]

def rawRow18722 : Integer.Sparse Key := [(key973, 24), (key1160, 24), (key1087, 24), (key1087, 24), (key1087, 24)]

def rawRow18723 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1087, 24), (key1087, 24), (key1160, 24)]

def rawRow18724 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1087, 24), (key1160, 24), (key1087, 24)]

def rawRow18725 : Integer.Sparse Key := [(key1087, 24), (key973, 24), (key1160, 24), (key1087, 24), (key1087, 24)]

def rawRow18726 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key973, 24), (key1087, 24), (key1160, 24)]

def rawRow18727 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key973, 24), (key1160, 24), (key1087, 24)]

def rawRow18728 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1087, 24), (key973, 24), (key1160, 24)]

def rawRow18729 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1087, 24), (key1160, 24), (key973, 24)]

def rawRow18730 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1160, 24), (key973, 24), (key1087, 24)]

def rawRow18731 : Integer.Sparse Key := [(key1087, 24), (key1087, 24), (key1160, 24), (key1087, 24), (key973, 24)]

def rawRow18732 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key973, 24), (key1087, 24), (key1087, 24)]

def rawRow18733 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key1087, 24), (key973, 24), (key1087, 24)]

def rawRow18734 : Integer.Sparse Key := [(key1087, 24), (key1160, 24), (key1087, 24), (key1087, 24), (key973, 24)]

def rawRow18735 : Integer.Sparse Key := [(key1160, 24), (key973, 24), (key1087, 24), (key1087, 24), (key1087, 24)]

def rawRow18736 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key973, 24), (key1087, 24), (key1087, 24)]

def rawRow18737 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key1087, 24), (key973, 24), (key1087, 24)]

def rawRow18738 : Integer.Sparse Key := [(key1160, 24), (key1087, 24), (key1087, 24), (key1087, 24), (key973, 24)]

def rawRow18739 : Integer.Sparse Key := [(key1, 6), (key7, 6), (key7, 6), (key7, 6), (key84, 6), (key90, 6), (key90, 6), (key84, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key193, 6), (key193, 6), (key193, 6), (key202, 6)]

def rawRow18740 : Integer.Sparse Key := [(key7, 6), (key1, 6), (key7, 6), (key7, 6), (key90, 6), (key84, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key90, 6), (key193, 6), (key193, 6), (key202, 6), (key193, 6)]

def rawRow18741 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key1, 6), (key7, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key193, 6), (key202, 6), (key193, 6), (key193, 6)]

def rawRow18742 : Integer.Sparse Key := [(key7, 6), (key7, 6), (key7, 6), (key1, 6), (key151, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key193, 6)]

def rawRow18743 : Integer.Sparse Key := [(key84, 6), (key90, 6), (key90, 6), (key151, 6), (key1, 6), (key7, 6), (key7, 6), (key84, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key151, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6)]

def rawRow18744 : Integer.Sparse Key := [(key90, 6), (key84, 6), (key90, 6), (key151, 6), (key7, 6), (key1, 6), (key7, 6), (key90, 6), (key84, 6), (key151, 6), (key84, 6), (key151, 6), (key90, 6), (key193, 6), (key202, 6), (key193, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6)]

def rawRow18745 : Integer.Sparse Key := [(key90, 6), (key90, 6), (key84, 6), (key151, 6), (key7, 6), (key7, 6), (key1, 6), (key151, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6)]

def rawRow18746 : Integer.Sparse Key := [(key84, 6), (key90, 6), (key151, 6), (key90, 6), (key84, 6), (key90, 6), (key151, 6), (key1, 6), (key7, 6), (key84, 6), (key151, 6), (key193, 6), (key202, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6), (key151, 6)]

def rawRow18747 : Integer.Sparse Key := [(key90, 6), (key84, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key7, 6), (key1, 6), (key151, 6), (key84, 6), (key202, 6), (key193, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6), (key151, 6), (key90, 6)]

def rawRow18748 : Integer.Sparse Key := [(key84, 6), (key151, 6), (key90, 6), (key90, 6), (key84, 6), (key151, 6), (key90, 6), (key84, 6), (key151, 6), (key1, 6), (key202, 6), (key7, 6), (key151, 6), (key90, 6), (key7, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6), (key151, 6)]

def rawRow18749 : Integer.Sparse Key := [(key151, 6), (key84, 6), (key90, 6), (key90, 6), (key151, 6), (key84, 6), (key90, 6), (key151, 6), (key84, 6), (key202, 6), (key1, 6), (key151, 6), (key7, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6)]

def rawRow18750 : Integer.Sparse Key := [(key90, 6), (key151, 6), (key84, 6), (key90, 6), (key90, 6), (key151, 6), (key84, 6), (key193, 6), (key202, 6), (key7, 6), (key151, 6), (key1, 6), (key84, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6)]

def rawRow18751 : Integer.Sparse Key := [(key151, 6), (key90, 6), (key84, 6), (key90, 6), (key151, 6), (key90, 6), (key84, 6), (key202, 6), (key193, 6), (key151, 6), (key7, 6), (key84, 6), (key1, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6), (key151, 6), (key90, 6), (key7, 6)]

def rawRow18752 : Integer.Sparse Key := [(key90, 6), (key90, 6), (key151, 6), (key84, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key1, 6), (key84, 6), (key84, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6)]

def rawRow18753 : Integer.Sparse Key := [(key90, 6), (key151, 6), (key90, 6), (key84, 6), (key193, 6), (key202, 6), (key193, 6), (key90, 6), (key151, 6), (key7, 6), (key151, 6), (key7, 6), (key90, 6), (key84, 6), (key1, 6), (key84, 6), (key151, 6), (key90, 6), (key7, 6), (key90, 6)]

def rawRow18754 : Integer.Sparse Key := [(key151, 6), (key90, 6), (key90, 6), (key84, 6), (key202, 6), (key193, 6), (key193, 6), (key151, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key7, 6), (key84, 6), (key84, 6), (key1, 6), (key151, 6), (key90, 6), (key90, 6), (key7, 6)]

def rawRow18755 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key193, 6), (key202, 6), (key7, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key151, 6), (key1, 6), (key84, 6), (key84, 6), (key84, 6)]

def rawRow18756 : Integer.Sparse Key := [(key193, 6), (key193, 6), (key202, 6), (key193, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key7, 6), (key90, 6), (key90, 6), (key151, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key84, 6), (key1, 6), (key84, 6), (key84, 6)]

def rawRow18757 : Integer.Sparse Key := [(key193, 6), (key202, 6), (key193, 6), (key193, 6), (key90, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key7, 6), (key151, 6), (key7, 6), (key90, 6), (key90, 6), (key7, 6), (key90, 6), (key84, 6), (key84, 6), (key1, 6), (key84, 6)]

def rawRow18758 : Integer.Sparse Key := [(key202, 6), (key193, 6), (key193, 6), (key193, 6), (key151, 6), (key90, 6), (key90, 6), (key151, 6), (key90, 6), (key151, 6), (key7, 6), (key90, 6), (key7, 6), (key90, 6), (key90, 6), (key7, 6), (key84, 6), (key84, 6), (key84, 6), (key1, 6)]

def rawRow18759 : Integer.Sparse Key := [(key2357, 6), (key2361, 6), (key2366, 6), (key2366, 6), (key2456, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2523, 6), (key2567, 6), (key2567, 6), (key2579, 6), (key2579, 6)]

def rawRow18760 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2361, 6), (key2366, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2567, 6), (key2579, 6), (key2567, 6), (key2579, 6)]

def rawRow18761 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2567, 6), (key2579, 6), (key2579, 6), (key2567, 6)]

def rawRow18762 : Integer.Sparse Key := [(key2357, 6), (key2363, 6), (key2363, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2456, 6), (key2461, 6), (key2456, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2579, 6), (key2567, 6), (key2567, 6), (key2579, 6)]

def rawRow18763 : Integer.Sparse Key := [(key2363, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2461, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2579, 6), (key2567, 6), (key2579, 6), (key2567, 6)]

def rawRow18764 : Integer.Sparse Key := [(key2363, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2461, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2456, 6), (key2579, 6), (key2579, 6), (key2567, 6), (key2567, 6)]

def rawRow18765 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2357, 6), (key2361, 6), (key2366, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2517, 6), (key2523, 6), (key2523, 6), (key2567, 6), (key2579, 6), (key2579, 6), (key2366, 6), (key2461, 6), (key2523, 6), (key2523, 6)]

def rawRow18766 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2363, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2579, 6), (key2567, 6), (key2579, 6), (key2366, 6), (key2523, 6), (key2461, 6), (key2523, 6)]

def rawRow18767 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2363, 6), (key2357, 6), (key2361, 6), (key2523, 6), (key2517, 6), (key2523, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2579, 6), (key2579, 6), (key2567, 6), (key2366, 6), (key2523, 6), (key2523, 6), (key2461, 6)]

def rawRow18768 : Integer.Sparse Key := [(key2452, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2361, 6), (key2517, 6), (key2517, 6), (key2579, 6), (key2579, 6), (key2366, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2366, 6), (key2523, 6), (key2523, 6)]

def rawRow18769 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2528, 6), (key2560, 6), (key2357, 6), (key2560, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2366, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2366, 6), (key2523, 6)]

def rawRow18770 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2528, 6), (key2560, 6), (key2357, 6), (key2517, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2366, 6), (key2461, 6), (key2523, 6), (key2523, 6), (key2366, 6)]

def rawRow18771 : Integer.Sparse Key := [(key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2357, 6), (key2363, 6), (key2452, 6), (key2530, 6), (key2519, 6), (key2560, 6), (key2361, 6), (key2456, 6), (key2517, 6), (key2523, 6), (key2366, 6), (key2461, 6), (key2523, 6)]

def rawRow18772 : Integer.Sparse Key := [(key2458, 6), (key2452, 6), (key2519, 6), (key2452, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2361, 6), (key2517, 6), (key2456, 6), (key2523, 6), (key2366, 6), (key2523, 6), (key2461, 6)]

def rawRow18773 : Integer.Sparse Key := [(key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2560, 6), (key2363, 6), (key2530, 6), (key2456, 6), (key2361, 6), (key2517, 6), (key2523, 6), (key2461, 6), (key2366, 6), (key2523, 6)]

def rawRow18774 : Integer.Sparse Key := [(key2519, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2519, 6), (key2452, 6), (key2560, 6), (key2357, 6), (key2530, 6), (key2363, 6), (key2456, 6), (key2517, 6), (key2361, 6), (key2523, 6), (key2461, 6), (key2523, 6), (key2366, 6)]

def rawRow18775 : Integer.Sparse Key := [(key2458, 6), (key2519, 6), (key2452, 6), (key2452, 6), (key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2517, 6), (key2361, 6), (key2456, 6), (key2523, 6), (key2523, 6), (key2366, 6), (key2461, 6)]

def rawRow18776 : Integer.Sparse Key := [(key2519, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2519, 6), (key2363, 6), (key2452, 6), (key2357, 6), (key2517, 6), (key2456, 6), (key2361, 6), (key2523, 6), (key2523, 6), (key2461, 6), (key2366, 6)]

def rawRow18777 : Integer.Sparse Key := [(key2528, 6), (key2530, 6), (key2530, 6), (key2560, 6), (key2357, 6), (key2363, 6), (key2363, 6), (key2452, 6), (key2458, 6), (key2452, 6), (key2530, 6), (key2458, 6), (key2530, 6), (key2519, 6), (key2519, 6), (key2560, 6), (key2361, 6), (key2456, 6), (key2456, 6), (key2517, 6)]

def rawRow18778 : Integer.Sparse Key := [(key2530, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2357, 6), (key2363, 6), (key2458, 6), (key2452, 6), (key2530, 6), (key2452, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2560, 6), (key2519, 6), (key2361, 6), (key2456, 6), (key2517, 6), (key2456, 6)]

def rawRow18779 : Integer.Sparse Key := [(key2530, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2363, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2530, 6), (key2458, 6), (key2458, 6), (key2452, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2519, 6), (key2361, 6), (key2517, 6), (key2456, 6), (key2456, 6)]

def rawRow18780 : Integer.Sparse Key := [(key2528, 6), (key2530, 6), (key2560, 6), (key2530, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2357, 6), (key2363, 6), (key2452, 6), (key2530, 6), (key2519, 6), (key2560, 6), (key2363, 6), (key2458, 6), (key2530, 6), (key2456, 6), (key2361, 6), (key2456, 6), (key2517, 6)]

def rawRow18781 : Integer.Sparse Key := [(key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2363, 6), (key2357, 6), (key2530, 6), (key2452, 6), (key2560, 6), (key2519, 6), (key2363, 6), (key2530, 6), (key2458, 6), (key2456, 6), (key2361, 6), (key2517, 6), (key2456, 6)]

def rawRow18782 : Integer.Sparse Key := [(key2528, 6), (key2560, 6), (key2530, 6), (key2530, 6), (key2452, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2519, 6), (key2357, 6), (key2560, 6), (key2363, 6), (key2530, 6), (key2458, 6), (key2363, 6), (key2530, 6), (key2456, 6), (key2456, 6), (key2361, 6), (key2517, 6)]

def rawRow18783 : Integer.Sparse Key := [(key2560, 6), (key2528, 6), (key2530, 6), (key2530, 6), (key2519, 6), (key2452, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2560, 6), (key2357, 6), (key2530, 6), (key2363, 6), (key2458, 6), (key2530, 6), (key2363, 6), (key2456, 6), (key2456, 6), (key2517, 6), (key2361, 6)]

def rawRow18784 : Integer.Sparse Key := [(key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2452, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2530, 6), (key2363, 6), (key2458, 6), (key2456, 6), (key2517, 6), (key2361, 6), (key2456, 6)]

def rawRow18785 : Integer.Sparse Key := [(key2560, 6), (key2530, 6), (key2528, 6), (key2530, 6), (key2519, 6), (key2458, 6), (key2452, 6), (key2560, 6), (key2530, 6), (key2519, 6), (key2363, 6), (key2452, 6), (key2357, 6), (key2530, 6), (key2458, 6), (key2363, 6), (key2456, 6), (key2517, 6), (key2456, 6), (key2361, 6)]

def rawRow18786 : Integer.Sparse Key := [(key2530, 6), (key2530, 6), (key2560, 6), (key2528, 6), (key2530, 6), (key2530, 6), (key2560, 6), (key2363, 6), (key2363, 6), (key2458, 6), (key2458, 6), (key2519, 6), (key2519, 6), (key2357, 6), (key2452, 6), (key2452, 6), (key2517, 6), (key2361, 6), (key2456, 6), (key2456, 6)]

def rawRow18787 : Integer.Sparse Key := [(key2530, 6), (key2560, 6), (key2530, 6), (key2528, 6), (key2530, 6), (key2560, 6), (key2530, 6), (key2458, 6), (key2519, 6), (key2363, 6), (key2519, 6), (key2363, 6), (key2458, 6), (key2452, 6), (key2357, 6), (key2452, 6), (key2517, 6), (key2456, 6), (key2361, 6), (key2456, 6)]

def rawRow18788 : Integer.Sparse Key := [(key2560, 6), (key2530, 6), (key2530, 6), (key2528, 6), (key2560, 6), (key2530, 6), (key2530, 6), (key2519, 6), (key2458, 6), (key2519, 6), (key2363, 6), (key2458, 6), (key2363, 6), (key2452, 6), (key2452, 6), (key2357, 6), (key2517, 6), (key2456, 6), (key2456, 6), (key2361, 6)]

def rawRow18789 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1088, 24), (key1178, 24), (key1178, 24)]

def rawRow18790 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1178, 24), (key1088, 24), (key1178, 24)]

def rawRow18791 : Integer.Sparse Key := [(key974, 24), (key1088, 24), (key1178, 24), (key1178, 24), (key1088, 24)]

def rawRow18792 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1088, 24), (key1088, 24), (key1178, 24)]

def rawRow18793 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1088, 24), (key1178, 24), (key1088, 24)]

def rawRow18794 : Integer.Sparse Key := [(key974, 24), (key1178, 24), (key1178, 24), (key1088, 24), (key1088, 24)]

def rawRow18795 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1088, 24), (key1178, 24), (key1178, 24)]

def rawRow18796 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1178, 24), (key1088, 24), (key1178, 24)]

def rawRow18797 : Integer.Sparse Key := [(key1088, 24), (key974, 24), (key1178, 24), (key1178, 24), (key1088, 24)]

def rawRow18798 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key974, 24), (key1178, 24), (key1178, 24)]

def rawRow18799 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key1178, 24), (key974, 24), (key1178, 24)]

def rawRow18800 : Integer.Sparse Key := [(key1088, 24), (key1088, 24), (key1178, 24), (key1178, 24), (key974, 24)]

def rawRow18801 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key974, 24), (key1088, 24), (key1178, 24)]

def rawRow18802 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key974, 24), (key1178, 24), (key1088, 24)]

def rawRow18803 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1088, 24), (key974, 24), (key1178, 24)]

def rawRow18804 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1088, 24), (key1178, 24), (key974, 24)]

def rawRow18805 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1178, 24), (key974, 24), (key1088, 24)]

def rawRow18806 : Integer.Sparse Key := [(key1088, 24), (key1178, 24), (key1178, 24), (key1088, 24), (key974, 24)]

def rawRow18807 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1088, 24), (key1088, 24), (key1178, 24)]

def rawRow18808 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1088, 24), (key1178, 24), (key1088, 24)]

def rawRow18809 : Integer.Sparse Key := [(key1178, 24), (key974, 24), (key1178, 24), (key1088, 24), (key1088, 24)]

def rawRow18810 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key974, 24), (key1088, 24), (key1178, 24)]

def rawRow18811 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key974, 24), (key1178, 24), (key1088, 24)]

def rawRow18812 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1088, 24), (key974, 24), (key1178, 24)]

def rawRow18813 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1088, 24), (key1178, 24), (key974, 24)]

def rawRow18814 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1178, 24), (key974, 24), (key1088, 24)]

def rawRow18815 : Integer.Sparse Key := [(key1178, 24), (key1088, 24), (key1178, 24), (key1088, 24), (key974, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18816 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key974, 24), (key1088, 24), (key1088, 24)]

def rawRow18817 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key1088, 24), (key974, 24), (key1088, 24)]

def rawRow18818 : Integer.Sparse Key := [(key1178, 24), (key1178, 24), (key1088, 24), (key1088, 24), (key974, 24)]

def rawRow18849 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2455, 24), (key2516, 24), (key2516, 24)]

def rawRow18850 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2516, 24), (key2455, 24), (key2516, 24)]

def rawRow18851 : Integer.Sparse Key := [(key2360, 24), (key2455, 24), (key2516, 24), (key2516, 24), (key2455, 24)]

def rawRow18852 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2455, 24), (key2455, 24), (key2516, 24)]

def rawRow18853 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2455, 24), (key2516, 24), (key2455, 24)]

def rawRow18854 : Integer.Sparse Key := [(key2360, 24), (key2516, 24), (key2516, 24), (key2455, 24), (key2455, 24)]

def rawRow18855 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2455, 24), (key2516, 24), (key2516, 24)]

def rawRow18856 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2516, 24), (key2455, 24), (key2516, 24)]

def rawRow18857 : Integer.Sparse Key := [(key2455, 24), (key2360, 24), (key2516, 24), (key2516, 24), (key2455, 24)]

def rawRow18858 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2360, 24), (key2516, 24), (key2516, 24)]

def rawRow18859 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2516, 24), (key2360, 24), (key2516, 24)]

def rawRow18860 : Integer.Sparse Key := [(key2455, 24), (key2455, 24), (key2516, 24), (key2516, 24), (key2360, 24)]

def rawRow18861 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2360, 24), (key2455, 24), (key2516, 24)]

def rawRow18862 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2360, 24), (key2516, 24), (key2455, 24)]

def rawRow18863 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2455, 24), (key2360, 24), (key2516, 24)]

def rawRow18864 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2455, 24), (key2516, 24), (key2360, 24)]

def rawRow18865 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2516, 24), (key2360, 24), (key2455, 24)]

def rawRow18866 : Integer.Sparse Key := [(key2455, 24), (key2516, 24), (key2516, 24), (key2455, 24), (key2360, 24)]

def rawRow18867 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2455, 24), (key2455, 24), (key2516, 24)]

def rawRow18868 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2455, 24), (key2516, 24), (key2455, 24)]

def rawRow18869 : Integer.Sparse Key := [(key2516, 24), (key2360, 24), (key2516, 24), (key2455, 24), (key2455, 24)]

def rawRow18870 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2360, 24), (key2455, 24), (key2516, 24)]

def rawRow18871 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2360, 24), (key2516, 24), (key2455, 24)]

def rawRow18872 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2455, 24), (key2360, 24), (key2516, 24)]

def rawRow18873 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2455, 24), (key2516, 24), (key2360, 24)]

def rawRow18874 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2516, 24), (key2360, 24), (key2455, 24)]

def rawRow18875 : Integer.Sparse Key := [(key2516, 24), (key2455, 24), (key2516, 24), (key2455, 24), (key2360, 24)]

def rawRow18876 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2360, 24), (key2455, 24), (key2455, 24)]

def rawRow18877 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2455, 24), (key2360, 24), (key2455, 24)]

def rawRow18878 : Integer.Sparse Key := [(key2516, 24), (key2516, 24), (key2455, 24), (key2455, 24), (key2360, 24)]

def rawRow18879 : Integer.Sparse Key := [(key976, 6), (key976, 6), (key984, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1169, 6), (key1220, 6), (key1220, 6)]

def rawRow18880 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key976, 6), (key984, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key1169, 6), (key1220, 6)]

def rawRow18881 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key976, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1220, 6), (key1220, 6), (key1169, 6)]

def rawRow18882 : Integer.Sparse Key := [(key976, 6), (key984, 6), (key984, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1169, 6), (key1169, 6), (key1220, 6)]

def rawRow18883 : Integer.Sparse Key := [(key984, 6), (key976, 6), (key984, 6), (key976, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key1220, 6), (key1169, 6)]

def rawRow18884 : Integer.Sparse Key := [(key984, 6), (key984, 6), (key976, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1220, 6), (key1169, 6), (key1169, 6)]

def rawRow18885 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key976, 6), (key976, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key1220, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1183, 6)]

def rawRow18886 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key976, 6), (key984, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1169, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1183, 6)]

def rawRow18887 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key984, 6), (key976, 6), (key976, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key1220, 6), (key1220, 6), (key1169, 6), (key984, 6), (key1183, 6), (key1183, 6), (key1098, 6)]

def rawRow18888 : Integer.Sparse Key := [(key1090, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1169, 6), (key976, 6), (key976, 6), (key1180, 6), (key1180, 6), (key1220, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6), (key1183, 6)]

def rawRow18889 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key976, 6), (key1220, 6), (key976, 6), (key1180, 6), (key1183, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key984, 6), (key1183, 6)]

def rawRow18890 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1180, 6), (key1220, 6), (key976, 6), (key1180, 6), (key976, 6), (key1183, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1183, 6), (key984, 6)]

def rawRow18891 : Integer.Sparse Key := [(key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key976, 6), (key984, 6), (key1090, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6)]

def rawRow18892 : Integer.Sparse Key := [(key1098, 6), (key1090, 6), (key1169, 6), (key1090, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key984, 6), (key976, 6), (key1183, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1183, 6), (key984, 6), (key1183, 6), (key1098, 6)]

def rawRow18893 : Integer.Sparse Key := [(key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1090, 6), (key1169, 6), (key976, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6)]

def rawRow18894 : Integer.Sparse Key := [(key1169, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1169, 6), (key1090, 6), (key1220, 6), (key976, 6), (key1183, 6), (key984, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key984, 6)]

def rawRow18895 : Integer.Sparse Key := [(key1098, 6), (key1169, 6), (key1090, 6), (key1090, 6), (key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key984, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6), (key1183, 6), (key1183, 6), (key984, 6), (key1098, 6)]

def rawRow18896 : Integer.Sparse Key := [(key1169, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1169, 6), (key984, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key984, 6)]

def rawRow18897 : Integer.Sparse Key := [(key1180, 6), (key1183, 6), (key1183, 6), (key1220, 6), (key976, 6), (key984, 6), (key984, 6), (key1090, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1183, 6), (key1169, 6), (key1169, 6), (key1220, 6), (key976, 6), (key1090, 6), (key1090, 6), (key1180, 6)]

def rawRow18898 : Integer.Sparse Key := [(key1183, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key984, 6), (key976, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1183, 6), (key1090, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1220, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1090, 6)]

def rawRow18899 : Integer.Sparse Key := [(key1183, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key984, 6), (key984, 6), (key976, 6), (key1183, 6), (key1183, 6), (key1098, 6), (key1098, 6), (key1090, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key1169, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1090, 6)]

def rawRow18900 : Integer.Sparse Key := [(key1180, 6), (key1183, 6), (key1220, 6), (key1183, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key976, 6), (key984, 6), (key1090, 6), (key1183, 6), (key1169, 6), (key1220, 6), (key984, 6), (key1098, 6), (key1183, 6), (key1090, 6), (key976, 6), (key1090, 6), (key1180, 6)]

def rawRow18901 : Integer.Sparse Key := [(key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key984, 6), (key976, 6), (key1183, 6), (key1090, 6), (key1220, 6), (key1169, 6), (key984, 6), (key1183, 6), (key1098, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6)]

def rawRow18902 : Integer.Sparse Key := [(key1180, 6), (key1220, 6), (key1183, 6), (key1183, 6), (key1090, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1169, 6), (key976, 6), (key1220, 6), (key984, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1183, 6), (key1090, 6), (key1090, 6), (key976, 6), (key1180, 6)]

def rawRow18903 : Integer.Sparse Key := [(key1220, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1090, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1220, 6), (key976, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1183, 6), (key984, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key976, 6)]

def rawRow18904 : Integer.Sparse Key := [(key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key1090, 6), (key1183, 6), (key1220, 6), (key984, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1183, 6), (key984, 6), (key1098, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6)]

def rawRow18905 : Integer.Sparse Key := [(key1220, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1169, 6), (key1098, 6), (key1090, 6), (key1220, 6), (key1183, 6), (key1169, 6), (key984, 6), (key1090, 6), (key976, 6), (key1183, 6), (key1098, 6), (key984, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key976, 6)]

def rawRow18906 : Integer.Sparse Key := [(key1183, 6), (key1183, 6), (key1220, 6), (key1180, 6), (key1183, 6), (key1183, 6), (key1220, 6), (key984, 6), (key984, 6), (key1098, 6), (key1098, 6), (key1169, 6), (key1169, 6), (key976, 6), (key1090, 6), (key1090, 6), (key1180, 6), (key976, 6), (key1090, 6), (key1090, 6)]

def rawRow18907 : Integer.Sparse Key := [(key1183, 6), (key1220, 6), (key1183, 6), (key1180, 6), (key1183, 6), (key1220, 6), (key1183, 6), (key1098, 6), (key1169, 6), (key984, 6), (key1169, 6), (key984, 6), (key1098, 6), (key1090, 6), (key976, 6), (key1090, 6), (key1180, 6), (key1090, 6), (key976, 6), (key1090, 6)]

def rawRow18908 : Integer.Sparse Key := [(key1220, 6), (key1183, 6), (key1183, 6), (key1180, 6), (key1220, 6), (key1183, 6), (key1183, 6), (key1169, 6), (key1098, 6), (key1169, 6), (key984, 6), (key1098, 6), (key984, 6), (key1090, 6), (key1090, 6), (key976, 6), (key1180, 6), (key1090, 6), (key1090, 6), (key976, 6)]

def rawRow18909 : Integer.Sparse Key := [(key2362, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2457, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2525, 4), (key2532, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow18910 : Integer.Sparse Key := [(key2365, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow18911 : Integer.Sparse Key := [(key2365, 4), (key2365, 4), (key2362, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2525, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow18912 : Integer.Sparse Key := [(key2365, 4), (key2365, 4), (key2367, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow18913 : Integer.Sparse Key := [(key2365, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow18914 : Integer.Sparse Key := [(key2367, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2457, 4), (key2564, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2533, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow18915 : Integer.Sparse Key := [(key2457, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2525, 4), (key2525, 4), (key2533, 4), (key2564, 4), (key2564, 4)]

def rawRow18916 : Integer.Sparse Key := [(key2460, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2533, 4), (key2564, 4)]

def rawRow18917 : Integer.Sparse Key := [(key2460, 4), (key2460, 4), (key2457, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2525, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2564, 4), (key2533, 4)]

def rawRow18918 : Integer.Sparse Key := [(key2457, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2521, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2562, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2564, 4), (key2460, 4), (key2460, 4), (key2533, 4), (key2365, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2525, 4)]

def rawRow18919 : Integer.Sparse Key := [(key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2562, 4), (key2362, 4), (key2562, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2533, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2525, 4), (key2367, 4), (key2525, 4)]

def rawRow18920 : Integer.Sparse Key := [(key2521, 4), (key2521, 4), (key2457, 4), (key2525, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2562, 4), (key2362, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2460, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2525, 4), (key2525, 4), (key2367, 4)]

def rawRow18921 : Integer.Sparse Key := [(key2460, 4), (key2521, 4), (key2525, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2564, 4), (key2362, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2521, 4), (key2525, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2525, 4), (key2533, 4), (key2564, 4), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow18922 : Integer.Sparse Key := [(key2460, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2367, 4), (key2365, 4), (key2525, 4), (key2460, 4), (key2564, 4), (key2533, 4), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow18923 : Integer.Sparse Key := [(key2521, 4), (key2460, 4), (key2525, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2457, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2460, 4), (key2533, 4), (key2365, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow18924 : Integer.Sparse Key := [(key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2460, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2362, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2525, 4), (key2533, 4), (key2460, 4), (key2564, 4), (key2365, 4), (key2525, 4), (key2367, 4), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow18925 : Integer.Sparse Key := [(key2525, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2525, 4), (key2564, 4), (key2521, 4), (key2525, 4), (key2564, 4), (key2367, 4), (key2533, 4), (key2365, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow18926 : Integer.Sparse Key := [(key2525, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2564, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2562, 4), (key2532, 4), (key2521, 4), (key2365, 4), (key2457, 4), (key2362, 4), (key2564, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2533, 4), (key2367, 4), (key2460, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow18927 : Integer.Sparse Key := [(key2532, 4), (key2532, 4), (key2533, 4), (key2562, 4), (key2564, 4), (key2564, 4), (key2365, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2460, 4), (key2533, 4), (key2521, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2564, 4), (key2362, 4), (key2365, 4), (key2365, 4), (key2457, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4)]

def rawRow18928 : Integer.Sparse Key := [(key2532, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2562, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2365, 4), (key2460, 4), (key2533, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2564, 4), (key2521, 4), (key2564, 4), (key2525, 4), (key2365, 4), (key2362, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2532, 4), (key2562, 4), (key2532, 4)]

def rawRow18929 : Integer.Sparse Key := [(key2533, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2562, 4), (key2367, 4), (key2365, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2460, 4), (key2564, 4), (key2564, 4), (key2525, 4), (key2525, 4), (key2521, 4), (key2521, 4), (key2365, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2521, 4), (key2460, 4), (key2460, 4), (key2457, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2532, 4)]

def rawRow18930 : Integer.Sparse Key := [(key2532, 4), (key2562, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2564, 4), (key2460, 4), (key2521, 4), (key2525, 4), (key2365, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2367, 4), (key2460, 4), (key2533, 4), (key2525, 4), (key2564, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2362, 4), (key2365, 4), (key2457, 4), (key2521, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2460, 4), (key2521, 4)]

def rawRow18931 : Integer.Sparse Key := [(key2532, 4), (key2564, 4), (key2562, 4), (key2533, 4), (key2532, 4), (key2564, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2521, 4), (key2367, 4), (key2365, 4), (key2533, 4), (key2460, 4), (key2564, 4), (key2525, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2365, 4), (key2362, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2365, 4), (key2521, 4), (key2460, 4)]

def rawRow18932 : Integer.Sparse Key := [(key2562, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2521, 4), (key2460, 4), (key2525, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2460, 4), (key2525, 4), (key2365, 4), (key2564, 4), (key2367, 4), (key2533, 4), (key2457, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2521, 4), (key2362, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2365, 4), (key2521, 4)]

def rawRow18933 : Integer.Sparse Key := [(key2562, 4), (key2564, 4), (key2532, 4), (key2564, 4), (key2532, 4), (key2533, 4), (key2521, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2525, 4), (key2460, 4), (key2564, 4), (key2365, 4), (key2533, 4), (key2367, 4), (key2521, 4), (key2457, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2562, 4), (key2362, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2521, 4), (key2365, 4)]

def rawRow18934 : Integer.Sparse Key := [(key2564, 4), (key2532, 4), (key2562, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2564, 4), (key2365, 4), (key2521, 4), (key2533, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2457, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2521, 4), (key2365, 4), (key2460, 4)]

def rawRow18935 : Integer.Sparse Key := [(key2564, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2532, 4), (key2525, 4), (key2521, 4), (key2460, 4), (key2564, 4), (key2521, 4), (key2365, 4), (key2564, 4), (key2533, 4), (key2525, 4), (key2367, 4), (key2460, 4), (key2365, 4), (key2521, 4), (key2460, 4), (key2457, 4), (key2562, 4), (key2532, 4), (key2521, 4), (key2365, 4), (key2457, 4), (key2362, 4), (key2521, 4), (key2460, 4), (key2365, 4)]

def rawRow18936 : Integer.Sparse Key := [(key2533, 4), (key2564, 4), (key2564, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2533, 4), (key2564, 4), (key2564, 4), (key2367, 4), (key2525, 4), (key2525, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2532, 4), (key2532, 4), (key2562, 4), (key2365, 4), (key2365, 4), (key2460, 4), (key2460, 4), (key2521, 4), (key2521, 4), (key2362, 4), (key2457, 4), (key2457, 4)]

def rawRow18937 : Integer.Sparse Key := [(key2564, 4), (key2533, 4), (key2564, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2564, 4), (key2533, 4), (key2564, 4), (key2525, 4), (key2367, 4), (key2525, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2532, 4), (key2562, 4), (key2532, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2457, 4), (key2362, 4), (key2457, 4)]

def rawRow18938 : Integer.Sparse Key := [(key2564, 4), (key2564, 4), (key2533, 4), (key2562, 4), (key2532, 4), (key2532, 4), (key2564, 4), (key2564, 4), (key2533, 4), (key2525, 4), (key2525, 4), (key2367, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2365, 4), (key2562, 4), (key2532, 4), (key2532, 4), (key2521, 4), (key2460, 4), (key2521, 4), (key2365, 4), (key2460, 4), (key2365, 4), (key2457, 4), (key2457, 4), (key2362, 4)]

def rawRow18939 : Integer.Sparse Key := [(key2354, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2559, 6)]

def rawRow18940 : Integer.Sparse Key := [(key2358, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2514, 6)]

def rawRow18941 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2514, 6)]

def rawRow18942 : Integer.Sparse Key := [(key2358, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2514, 6)]

def rawRow18943 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2354, 6), (key2358, 6), (key2358, 6), (key2449, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2529, 6), (key2514, 6), (key2514, 6), (key2559, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block172
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18944 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2354, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2559, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6)]

def rawRow18945 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2514, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6)]

def rawRow18946 : Integer.Sparse Key := [(key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2354, 6), (key2358, 6), (key2449, 6), (key2529, 6), (key2514, 6), (key2559, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2529, 6)]

def rawRow18947 : Integer.Sparse Key := [(key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2358, 6), (key2354, 6), (key2529, 6), (key2449, 6), (key2559, 6), (key2514, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2529, 6), (key2453, 6)]

def rawRow18948 : Integer.Sparse Key := [(key2449, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2514, 6), (key2354, 6), (key2559, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2529, 6)]

def rawRow18949 : Integer.Sparse Key := [(key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2559, 6), (key2354, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2358, 6)]

def rawRow18950 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2449, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2529, 6), (key2358, 6), (key2453, 6)]

def rawRow18951 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2449, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2559, 6), (key2529, 6), (key2514, 6), (key2358, 6), (key2449, 6), (key2354, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2529, 6), (key2453, 6), (key2358, 6)]

def rawRow18952 : Integer.Sparse Key := [(key2453, 6), (key2453, 6), (key2514, 6), (key2449, 6), (key2529, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2449, 6), (key2529, 6), (key2358, 6), (key2453, 6), (key2453, 6)]

def rawRow18953 : Integer.Sparse Key := [(key2453, 6), (key2514, 6), (key2453, 6), (key2449, 6), (key2529, 6), (key2559, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2354, 6), (key2449, 6), (key2529, 6), (key2453, 6), (key2358, 6), (key2453, 6)]

def rawRow18954 : Integer.Sparse Key := [(key2514, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2559, 6), (key2529, 6), (key2529, 6), (key2514, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2358, 6), (key2449, 6), (key2449, 6), (key2354, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2358, 6)]

def rawRow18955 : Integer.Sparse Key := [(key2529, 6), (key2529, 6), (key2529, 6), (key2559, 6), (key2358, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2514, 6), (key2354, 6), (key2449, 6), (key2449, 6), (key2449, 6)]

def rawRow18956 : Integer.Sparse Key := [(key2529, 6), (key2529, 6), (key2559, 6), (key2529, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2449, 6), (key2354, 6), (key2449, 6), (key2449, 6)]

def rawRow18957 : Integer.Sparse Key := [(key2529, 6), (key2559, 6), (key2529, 6), (key2529, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2449, 6), (key2449, 6), (key2354, 6), (key2449, 6)]

def rawRow18958 : Integer.Sparse Key := [(key2559, 6), (key2529, 6), (key2529, 6), (key2529, 6), (key2514, 6), (key2453, 6), (key2453, 6), (key2514, 6), (key2453, 6), (key2514, 6), (key2358, 6), (key2453, 6), (key2358, 6), (key2453, 6), (key2453, 6), (key2358, 6), (key2449, 6), (key2449, 6), (key2449, 6), (key2354, 6)]

def rawRow18959 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1083, 24), (key1083, 24), (key1177, 24)]

def rawRow18960 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1083, 24), (key1177, 24), (key1083, 24)]

def rawRow18961 : Integer.Sparse Key := [(key969, 24), (key1083, 24), (key1177, 24), (key1083, 24), (key1083, 24)]

def rawRow18962 : Integer.Sparse Key := [(key969, 24), (key1177, 24), (key1083, 24), (key1083, 24), (key1083, 24)]

def rawRow18963 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1083, 24), (key1083, 24), (key1177, 24)]

def rawRow18964 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1083, 24), (key1177, 24), (key1083, 24)]

def rawRow18965 : Integer.Sparse Key := [(key1083, 24), (key969, 24), (key1177, 24), (key1083, 24), (key1083, 24)]

def rawRow18966 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key969, 24), (key1083, 24), (key1177, 24)]

def rawRow18967 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key969, 24), (key1177, 24), (key1083, 24)]

def rawRow18968 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1083, 24), (key969, 24), (key1177, 24)]

def rawRow18969 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1083, 24), (key1177, 24), (key969, 24)]

def rawRow18970 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1177, 24), (key969, 24), (key1083, 24)]

def rawRow18971 : Integer.Sparse Key := [(key1083, 24), (key1083, 24), (key1177, 24), (key1083, 24), (key969, 24)]

def rawRow18972 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key969, 24), (key1083, 24), (key1083, 24)]

def rawRow18973 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key1083, 24), (key969, 24), (key1083, 24)]

def rawRow18974 : Integer.Sparse Key := [(key1083, 24), (key1177, 24), (key1083, 24), (key1083, 24), (key969, 24)]

def rawRow18975 : Integer.Sparse Key := [(key1177, 24), (key969, 24), (key1083, 24), (key1083, 24), (key1083, 24)]

def rawRow18976 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key969, 24), (key1083, 24), (key1083, 24)]

def rawRow18977 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key1083, 24), (key969, 24), (key1083, 24)]

def rawRow18978 : Integer.Sparse Key := [(key1177, 24), (key1083, 24), (key1083, 24), (key1083, 24), (key969, 24)]

def rawRow18979 : Integer.Sparse Key := [(key2584, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2844, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2988, 2)]

def rawRow18980 : Integer.Sparse Key := [(key2588, 2), (key2584, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2988, 2), (key2909, 2)]

def rawRow18981 : Integer.Sparse Key := [(key2588, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2)]

def rawRow18982 : Integer.Sparse Key := [(key2599, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2584, 2), (key2930, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2763, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2)]

def rawRow18983 : Integer.Sparse Key := [(key2763, 2), (key2767, 2), (key2767, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2888, 2), (key2875, 2), (key2875, 2), (key2909, 2), (key2584, 2), (key2588, 2), (key2588, 2), (key2840, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2875, 2), (key2875, 2), (key2988, 2), (key2584, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2599, 2), (key2763, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2930, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2967, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2767, 2), (key2930, 2), (key2844, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2888, 2), (key2967, 2)]

def rawRow18984 : Integer.Sparse Key := [(key2767, 2), (key2763, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2888, 2), (key2840, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2909, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2599, 2), (key2584, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2930, 2), (key2763, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2967, 2), (key2840, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2875, 2), (key2988, 2), (key2875, 2), (key2988, 2), (key2909, 2), (key2588, 2), (key2599, 2), (key2588, 2), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2967, 2), (key2844, 2), (key2967, 2), (key2888, 2)]

def rawRow18985 : Integer.Sparse Key := [(key2767, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2875, 2), (key2599, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2584, 2), (key2584, 2), (key2930, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2763, 2), (key2763, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2840, 2), (key2840, 2), (key2988, 2), (key2988, 2), (key2909, 2), (key2909, 2), (key2875, 2), (key2875, 2), (key2599, 2), (key2588, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2767, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2844, 2), (key2844, 2)]

def rawRow18986 : Integer.Sparse Key := [(key2840, 2), (key2844, 2), (key2875, 2), (key2763, 2), (key2767, 2), (key2840, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2763, 2), (key2767, 2), (key2840, 2), (key2888, 2), (key2875, 2), (key2909, 2), (key2584, 2), (key2588, 2), (key2840, 2), (key2967, 2), (key2875, 2), (key2988, 2), (key2584, 2), (key2599, 2), (key2763, 2), (key2930, 2), (key2909, 2), (key2988, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2930, 2), (key2888, 2), (key2967, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2599, 2), (key2767, 2), (key2930, 2), (key2888, 2), (key2967, 2)]

def rawRow18987 : Integer.Sparse Key := [(key2844, 2), (key2840, 2), (key2875, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2767, 2), (key2763, 2), (key2888, 2), (key2840, 2), (key2909, 2), (key2875, 2), (key2588, 2), (key2584, 2), (key2967, 2), (key2840, 2), (key2988, 2), (key2875, 2), (key2599, 2), (key2584, 2), (key2930, 2), (key2763, 2), (key2988, 2), (key2909, 2), (key2599, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2967, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2599, 2), (key2588, 2), (key2930, 2), (key2767, 2), (key2967, 2), (key2888, 2)]

def rawRow18988 : Integer.Sparse Key := [(key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2840, 2), (key2875, 2), (key2763, 2), (key2909, 2), (key2767, 2), (key2888, 2), (key2840, 2), (key2875, 2), (key2584, 2), (key2988, 2), (key2588, 2), (key2967, 2), (key2763, 2), (key2909, 2), (key2584, 2), (key2988, 2), (key2599, 2), (key2930, 2), (key2767, 2), (key2888, 2), (key2588, 2), (key2967, 2), (key2599, 2), (key2930, 2), (key2844, 2), (key2767, 2), (key2888, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2767, 2), (key2888, 2), (key2588, 2), (key2967, 2), (key2599, 2), (key2930, 2)]

def rawRow18989 : Integer.Sparse Key := [(key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2840, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2875, 2), (key2840, 2), (key2909, 2), (key2763, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2840, 2), (key2988, 2), (key2584, 2), (key2967, 2), (key2588, 2), (key2909, 2), (key2763, 2), (key2988, 2), (key2584, 2), (key2930, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2967, 2), (key2588, 2), (key2930, 2), (key2599, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2888, 2), (key2767, 2), (key2967, 2), (key2588, 2), (key2930, 2), (key2599, 2)]

def rawRow18990 : Integer.Sparse Key := [(key2844, 2), (key2875, 2), (key2840, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2930, 2), (key2988, 2), (key2599, 2), (key2909, 2), (key2584, 2), (key2763, 2), (key2930, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2588, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2930, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2588, 2), (key2767, 2)]

def rawRow18991 : Integer.Sparse Key := [(key2875, 2), (key2844, 2), (key2840, 2), (key2909, 2), (key2888, 2), (key2875, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2844, 2), (key2840, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2909, 2), (key2888, 2), (key2875, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2988, 2), (key2967, 2), (key2875, 2), (key2588, 2), (key2840, 2), (key2584, 2), (key2988, 2), (key2930, 2), (key2909, 2), (key2599, 2), (key2763, 2), (key2584, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2599, 2), (key2767, 2), (key2588, 2), (key2888, 2), (key2844, 2), (key2767, 2), (key2967, 2), (key2844, 2), (key2588, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2599, 2), (key2767, 2), (key2588, 2)]

def rawRow18992 : Integer.Sparse Key := [(key2888, 2), (key2888, 2), (key2909, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2840, 2), (key2840, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2)]

def rawRow18993 : Integer.Sparse Key := [(key2888, 2), (key2909, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2967, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2767, 2)]

def rawRow18994 : Integer.Sparse Key := [(key2909, 2), (key2888, 2), (key2888, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2840, 2), (key2840, 2), (key2763, 2), (key2988, 2), (key2967, 2), (key2967, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2988, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2930, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2584, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2844, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2588, 2)]

def rawRow18995 : Integer.Sparse Key := [(key2930, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2988, 2), (key2599, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2909, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2875, 2), (key2584, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2), (key2840, 2)]

def rawRow18996 : Integer.Sparse Key := [(key2967, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2875, 2), (key2875, 2), (key2588, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2584, 2), (key2763, 2), (key2763, 2), (key2840, 2), (key2840, 2)]

def rawRow18997 : Integer.Sparse Key := [(key2967, 2), (key2988, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2584, 2), (key2763, 2)]

def rawRow18998 : Integer.Sparse Key := [(key2988, 2), (key2967, 2), (key2967, 2), (key2988, 2), (key2967, 2), (key2988, 2), (key2930, 2), (key2967, 2), (key2930, 2), (key2967, 2), (key2967, 2), (key2930, 2), (key2909, 2), (key2888, 2), (key2888, 2), (key2909, 2), (key2888, 2), (key2909, 2), (key2599, 2), (key2888, 2), (key2599, 2), (key2888, 2), (key2888, 2), (key2599, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2875, 2), (key2844, 2), (key2875, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2875, 2), (key2767, 2), (key2875, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2844, 2), (key2767, 2), (key2844, 2), (key2588, 2), (key2767, 2), (key2588, 2), (key2840, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2840, 2), (key2584, 2), (key2840, 2), (key2763, 2), (key2840, 2), (key2584, 2), (key2763, 2), (key2584, 2)]

def rawRow18999 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2447, 24), (key2447, 24), (key2511, 24)]

def rawRow19000 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2447, 24), (key2511, 24), (key2447, 24)]

def rawRow19001 : Integer.Sparse Key := [(key2352, 24), (key2447, 24), (key2511, 24), (key2447, 24), (key2447, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow19244 : Integer.Sparse Key := [(key685, 24), (key685, 24), (key685, 24), (key685, 24), (key692, 24)]

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

def rawRow1829 : Integer.Sparse Key := [(key2475, -6), (key2466, 2), (key2466, 2), (key2400, 2), (key2498, 6), (key2466, -2), (key2466, -2), (key2372, -2), (key2498, -2), (key2498, -2), (key2432, -2), (key2475, 2), (key2475, 2), (key2385, 2)]

def rawRow1831 : Integer.Sparse Key := [(key2498, -6), (key2432, 2), (key2498, 2), (key2498, 2), (key2475, 6), (key2385, -2), (key2475, -2), (key2475, -2), (key2400, -2), (key2466, -2), (key2466, -2), (key2372, 2), (key2466, 2), (key2466, 2)]

def rawRow1832 : Integer.Sparse Key := [(key2498, -6), (key2498, 2), (key2432, 2), (key2498, 2), (key2475, 6), (key2475, -2), (key2385, -2), (key2475, -2), (key2466, -2), (key2400, -2), (key2466, -2), (key2466, 2), (key2372, 2), (key2466, 2)]

def rawRow1833 : Integer.Sparse Key := [(key2498, -6), (key2498, 2), (key2498, 2), (key2432, 2), (key2475, 6), (key2475, -2), (key2475, -2), (key2385, -2), (key2466, -2), (key2466, -2), (key2400, -2), (key2466, 2), (key2466, 2), (key2372, 2)]

def rawRow1834 : Integer.Sparse Key := [(key1526, -1), (key1534, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1894, -1), (key1534, 2), (key1534, 2), (key1894, 2), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1612, -1), (key1679, -1), (key1612, -1), (key1916, -1), (key1679, -1), (key1916, -1), (key1640, -2), (key1640, -2), (key1930, -2), (key1640, 1), (key1693, 1), (key1640, 1), (key1930, 1), (key1693, 1), (key1930, 1)]

def rawRow1835 : Integer.Sparse Key := [(key1534, -1), (key1526, -1), (key1894, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1534, 2), (key1894, 2), (key1534, 2), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1679, -1), (key1612, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1679, -1), (key1640, -2), (key1930, -2), (key1640, -2), (key1693, 1), (key1640, 1), (key1930, 1), (key1640, 1), (key1930, 1), (key1693, 1)]

def rawRow1836 : Integer.Sparse Key := [(key1894, -1), (key1894, -1), (key1534, -1), (key1534, -1), (key1526, -1), (key1526, -1), (key1894, 2), (key1534, 2), (key1534, 2), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1916, -1), (key1916, -1), (key1679, -1), (key1679, -1), (key1612, -1), (key1612, -1), (key1930, -2), (key1640, -2), (key1640, -2), (key1930, 1), (key1930, 1), (key1693, 1), (key1693, 1), (key1640, 1), (key1640, 1)]

def rawRow1838 : Integer.Sparse Key := [(key1604, -1), (key1612, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1640, 2), (key1640, 2), (key1930, 2), (key1526, 1), (key1534, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1894, 1), (key1640, -1), (key1693, -1), (key1640, -1), (key1930, -1), (key1693, -1), (key1930, -1), (key1534, -2), (key1534, -2), (key1894, -2), (key1612, 1), (key1679, 1), (key1612, 1), (key1916, 1), (key1679, 1), (key1916, 1)]

def rawRow1839 : Integer.Sparse Key := [(key1612, -1), (key1604, -1), (key1916, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1640, 2), (key1930, 2), (key1640, 2), (key1534, 1), (key1526, 1), (key1894, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1693, -1), (key1640, -1), (key1930, -1), (key1640, -1), (key1930, -1), (key1693, -1), (key1534, -2), (key1894, -2), (key1534, -2), (key1679, 1), (key1612, 1), (key1916, 1), (key1612, 1), (key1916, 1), (key1679, 1)]

def rawRow1840 : Integer.Sparse Key := [(key1916, -1), (key1916, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1930, 2), (key1640, 2), (key1640, 2), (key1894, 1), (key1894, 1), (key1534, 1), (key1534, 1), (key1526, 1), (key1526, 1), (key1930, -1), (key1930, -1), (key1693, -1), (key1693, -1), (key1640, -1), (key1640, -1), (key1894, -2), (key1534, -2), (key1534, -2), (key1916, 1), (key1916, 1), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1)]

def rawRow1841 : Integer.Sparse Key := [(key1259, -1), (key1259, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1251, 2), (key1604, 2), (key1604, 2), (key1271, 1), (key1271, 1), (key1679, 1), (key1679, 1), (key1693, 1), (key1693, 1), (key1251, -1), (key1251, -1), (key1526, -1), (key1526, -1), (key1604, -1), (key1604, -1), (key1271, -2), (key1679, -2), (key1679, -2), (key1259, 1), (key1259, 1), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1)]

def rawRow1842 : Integer.Sparse Key := [(key1612, -1), (key1640, -1), (key1259, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1604, 2), (key1251, 2), (key1604, 2), (key1679, 1), (key1693, 1), (key1271, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1526, -1), (key1604, -1), (key1251, -1), (key1604, -1), (key1251, -1), (key1526, -1), (key1679, -2), (key1271, -2), (key1679, -2), (key1534, 1), (key1612, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1534, 1)]

def rawRow1843 : Integer.Sparse Key := [(key1640, -1), (key1612, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1604, 2), (key1604, 2), (key1251, 2), (key1693, 1), (key1679, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1271, 1), (key1604, -1), (key1526, -1), (key1604, -1), (key1251, -1), (key1526, -1), (key1251, -1), (key1679, -2), (key1679, -2), (key1271, -2), (key1612, 1), (key1534, 1), (key1612, 1), (key1259, 1), (key1534, 1), (key1259, 1)]

def rawRow1845 : Integer.Sparse Key := [(key1271, -1), (key1271, -1), (key1679, -1), (key1679, -1), (key1693, -1), (key1693, -1), (key1271, 2), (key1679, 2), (key1679, 2), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1259, -1), (key1259, -1), (key1534, -1), (key1534, -1), (key1612, -1), (key1612, -1), (key1251, -2), (key1604, -2), (key1604, -2), (key1251, 1), (key1251, 1), (key1526, 1), (key1526, 1), (key1604, 1), (key1604, 1)]

def rawRow1846 : Integer.Sparse Key := [(key1679, -1), (key1693, -1), (key1271, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1679, 2), (key1271, 2), (key1679, 2), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1534, -1), (key1612, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1534, -1), (key1604, -2), (key1251, -2), (key1604, -2), (key1526, 1), (key1604, 1), (key1251, 1), (key1604, 1), (key1251, 1), (key1526, 1)]

def rawRow1847 : Integer.Sparse Key := [(key1693, -1), (key1679, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1271, -1), (key1679, 2), (key1679, 2), (key1271, 2), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1), (key1612, -1), (key1534, -1), (key1612, -1), (key1259, -1), (key1534, -1), (key1259, -1), (key1604, -2), (key1604, -2), (key1251, -2), (key1604, 1), (key1526, 1), (key1604, 1), (key1251, 1), (key1526, 1), (key1251, 1)]

def rawRow1855 : Integer.Sparse Key := [(key3038, -2), (key3038, -2), (key3130, -2), (key3033, 2), (key3033, 2), (key3120, 2), (key3043, 2), (key3043, 2), (key3144, 2), (key2414, -6), (key2426, -2), (key2426, -2), (key2494, -2), (key2419, 6)]

def rawRow1856 : Integer.Sparse Key := [(key3038, -2), (key3130, -2), (key3038, -2), (key3033, 2), (key3120, 2), (key3033, 2), (key3043, 2), (key3144, 2), (key3043, 2), (key3033, -6), (key2426, -2), (key2494, -2), (key2426, -2), (key2419, 6)]

def rawRow1857 : Integer.Sparse Key := [(key3130, -2), (key3038, -2), (key3038, -2), (key3120, 2), (key3033, 2), (key3033, 2), (key3144, 2), (key3043, 2), (key3043, 2), (key3033, -6), (key2494, -2), (key2426, -2), (key2426, -2), (key2419, 6)]

def rawRow1859 : Integer.Sparse Key := [(key3043, -2), (key3043, -2), (key3144, -2), (key3043, 2), (key3043, 2), (key3141, 2), (key3038, 2), (key3038, 2), (key3130, 2), (key3038, -6), (key3033, -2), (key3033, -2), (key3120, -2), (key2414, 6)]

def rawRow1860 : Integer.Sparse Key := [(key3043, -2), (key3144, -2), (key3043, -2), (key3043, 2), (key3141, 2), (key3043, 2), (key3038, 2), (key3130, 2), (key3038, 2), (key3038, -6), (key3033, -2), (key3120, -2), (key3033, -2), (key3033, 6)]

def rawRow1861 : Integer.Sparse Key := [(key3144, -2), (key3043, -2), (key3043, -2), (key3141, 2), (key3043, 2), (key3043, 2), (key3130, 2), (key3038, 2), (key3038, 2), (key3038, -6), (key3120, -2), (key3033, -2), (key3033, -2), (key3033, 6)]

def rawRow1862 : Integer.Sparse Key := [(key1251, -2), (key1259, -2), (key1259, -2), (key1251, 1), (key1259, 1), (key1251, 1), (key1271, 1), (key1259, 1), (key1271, 1), (key1526, 2), (key1534, 2), (key1534, 2), (key1526, -1), (key1534, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1894, -1), (key1604, -1), (key1612, -1), (key1604, -1), (key1679, -1), (key1612, -1), (key1679, -1), (key1604, 1), (key1612, 1), (key1604, 1), (key1916, 1), (key1612, 1), (key1916, 1)]

def rawRow1863 : Integer.Sparse Key := [(key1259, -2), (key1251, -2), (key1259, -2), (key1259, 1), (key1251, 1), (key1271, 1), (key1251, 1), (key1271, 1), (key1259, 1), (key1534, 2), (key1526, 2), (key1534, 2), (key1534, -1), (key1526, -1), (key1894, -1), (key1526, -1), (key1894, -1), (key1534, -1), (key1612, -1), (key1604, -1), (key1679, -1), (key1604, -1), (key1679, -1), (key1612, -1), (key1612, 1), (key1604, 1), (key1916, 1), (key1604, 1), (key1916, 1), (key1612, 1)]

def rawRow1864 : Integer.Sparse Key := [(key1259, -2), (key1259, -2), (key1251, -2), (key1271, 1), (key1271, 1), (key1259, 1), (key1259, 1), (key1251, 1), (key1251, 1), (key1534, 2), (key1534, 2), (key1526, 2), (key1894, -1), (key1894, -1), (key1534, -1), (key1534, -1), (key1526, -1), (key1526, -1), (key1679, -1), (key1679, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1916, 1), (key1916, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1)]

def rawRow1866 : Integer.Sparse Key := [(key1526, -2), (key1534, -2), (key1534, -2), (key1604, 1), (key1612, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1679, 1), (key1251, 2), (key1259, 2), (key1259, 2), (key1604, -1), (key1612, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1916, -1), (key1251, -1), (key1259, -1), (key1251, -1), (key1271, -1), (key1259, -1), (key1271, -1), (key1526, 1), (key1534, 1), (key1526, 1), (key1894, 1), (key1534, 1), (key1894, 1)]

def rawRow1867 : Integer.Sparse Key := [(key1534, -2), (key1526, -2), (key1534, -2), (key1612, 1), (key1604, 1), (key1679, 1), (key1604, 1), (key1679, 1), (key1612, 1), (key1259, 2), (key1251, 2), (key1259, 2), (key1612, -1), (key1604, -1), (key1916, -1), (key1604, -1), (key1916, -1), (key1612, -1), (key1259, -1), (key1251, -1), (key1271, -1), (key1251, -1), (key1271, -1), (key1259, -1), (key1534, 1), (key1526, 1), (key1894, 1), (key1526, 1), (key1894, 1), (key1534, 1)]

def rawRow1868 : Integer.Sparse Key := [(key1534, -2), (key1534, -2), (key1526, -2), (key1679, 1), (key1679, 1), (key1612, 1), (key1612, 1), (key1604, 1), (key1604, 1), (key1259, 2), (key1259, 2), (key1251, 2), (key1916, -1), (key1916, -1), (key1612, -1), (key1612, -1), (key1604, -1), (key1604, -1), (key1271, -1), (key1271, -1), (key1259, -1), (key1259, -1), (key1251, -1), (key1251, -1), (key1894, 1), (key1894, 1), (key1534, 1), (key1534, 1), (key1526, 1), (key1526, 1)]

def rawRow1869 : Integer.Sparse Key := [(key1679, -2), (key1679, -2), (key1693, -2), (key1534, 1), (key1534, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1), (key1916, 2), (key1916, 2), (key1930, 2), (key1259, -1), (key1259, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1894, -1), (key1894, -1), (key1916, -1), (key1916, -1), (key1930, -1), (key1930, -1), (key1271, 1), (key1271, 1), (key1679, 1), (key1679, 1), (key1693, 1), (key1693, 1)]

def rawRow1870 : Integer.Sparse Key := [(key1679, -2), (key1693, -2), (key1679, -2), (key1612, 1), (key1640, 1), (key1534, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1916, 2), (key1930, 2), (key1916, 2), (key1612, -1), (key1640, -1), (key1259, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1916, -1), (key1930, -1), (key1894, -1), (key1930, -1), (key1894, -1), (key1916, -1), (key1679, 1), (key1693, 1), (key1271, 1), (key1693, 1), (key1271, 1), (key1679, 1)]

def rawRow1871 : Integer.Sparse Key := [(key1693, -2), (key1679, -2), (key1679, -2), (key1640, 1), (key1612, 1), (key1640, 1), (key1534, 1), (key1612, 1), (key1534, 1), (key1930, 2), (key1916, 2), (key1916, 2), (key1640, -1), (key1612, -1), (key1640, -1), (key1259, -1), (key1612, -1), (key1259, -1), (key1930, -1), (key1916, -1), (key1930, -1), (key1894, -1), (key1916, -1), (key1894, -1), (key1693, 1), (key1679, 1), (key1693, 1), (key1271, 1), (key1679, 1), (key1271, 1)]

def rawRow1873 : Integer.Sparse Key := [(key1916, -2), (key1916, -2), (key1930, -2), (key1894, 1), (key1894, 1), (key1916, 1), (key1916, 1), (key1930, 1), (key1930, 1), (key1679, 2), (key1679, 2), (key1693, 2), (key1271, -1), (key1271, -1), (key1679, -1), (key1679, -1), (key1693, -1), (key1693, -1), (key1534, -1), (key1534, -1), (key1612, -1), (key1612, -1), (key1640, -1), (key1640, -1), (key1259, 1), (key1259, 1), (key1612, 1), (key1612, 1), (key1640, 1), (key1640, 1)]

def rawRow1874 : Integer.Sparse Key := [(key1916, -2), (key1930, -2), (key1916, -2), (key1916, 1), (key1930, 1), (key1894, 1), (key1930, 1), (key1894, 1), (key1916, 1), (key1679, 2), (key1693, 2), (key1679, 2), (key1679, -1), (key1693, -1), (key1271, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1612, -1), (key1640, -1), (key1534, -1), (key1640, -1), (key1534, -1), (key1612, -1), (key1612, 1), (key1640, 1), (key1259, 1), (key1640, 1), (key1259, 1), (key1612, 1)]

def rawRow1875 : Integer.Sparse Key := [(key1930, -2), (key1916, -2), (key1916, -2), (key1930, 1), (key1916, 1), (key1930, 1), (key1894, 1), (key1916, 1), (key1894, 1), (key1693, 2), (key1679, 2), (key1679, 2), (key1693, -1), (key1679, -1), (key1693, -1), (key1271, -1), (key1679, -1), (key1271, -1), (key1640, -1), (key1612, -1), (key1640, -1), (key1534, -1), (key1612, -1), (key1534, -1), (key1640, 1), (key1612, 1), (key1640, 1), (key1259, 1), (key1612, 1), (key1259, 1)]

def rawRow1876 : Integer.Sparse Key := [(key972, -2), (key978, -2), (key978, -2), (key978, 6), (key1086, 2), (key1092, 2), (key1092, 2), (key1092, -2), (key1092, -2), (key1227, -2), (key1163, -6), (key1163, 2), (key1163, 2), (key1244, 2)]

def rawRow1877 : Integer.Sparse Key := [(key978, -2), (key972, -2), (key978, -2), (key978, 6), (key1092, 2), (key1086, 2), (key1092, 2), (key1092, -2), (key1227, -2), (key1092, -2), (key1163, -6), (key1163, 2), (key1244, 2), (key1163, 2)]

def rawRow1878 : Integer.Sparse Key := [(key978, -2), (key978, -2), (key972, -2), (key978, 6), (key1092, 2), (key1092, 2), (key1086, 2), (key1227, -2), (key1092, -2), (key1092, -2), (key1163, -6), (key1244, 2), (key1163, 2), (key1163, 2)]

def rawRow1880 : Integer.Sparse Key := [(key1086, -2), (key1092, -2), (key1092, -2), (key1163, 6), (key972, 2), (key978, 2), (key978, 2), (key1163, -2), (key1163, -2), (key1244, -2), (key978, -6), (key1092, 2), (key1092, 2), (key1227, 2)]

def rawRow1881 : Integer.Sparse Key := [(key1092, -2), (key1086, -2), (key1092, -2), (key1163, 6), (key978, 2), (key972, 2), (key978, 2), (key1163, -2), (key1244, -2), (key1163, -2), (key978, -6), (key1092, 2), (key1227, 2), (key1092, 2)]

def rawRow1882 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1086, -2), (key1163, 6), (key978, 2), (key978, 2), (key972, 2), (key1244, -2), (key1163, -2), (key1163, -2), (key978, -6), (key1227, 2), (key1092, 2), (key1092, 2)]

def rawRow1883 : Integer.Sparse Key := [(key1092, -2), (key1092, -2), (key1163, -2), (key1086, 6), (key1227, 2), (key1227, 2), (key1244, 2), (key972, -2), (key1086, -2), (key1086, -2), (key1227, -6), (key978, 2), (key1092, 2), (key1092, 2)]

def rawRow1884 : Integer.Sparse Key := [(key1092, -2), (key1163, -2), (key1092, -2), (key1086, 6), (key1227, 2), (key1244, 2), (key1227, 2), (key1086, -2), (key972, -2), (key1086, -2), (key1227, -6), (key1092, 2), (key978, 2), (key1092, 2)]

def rawRow1885 : Integer.Sparse Key := [(key1163, -2), (key1092, -2), (key1092, -2), (key1086, 6), (key1244, 2), (key1227, 2), (key1227, 2), (key1086, -2), (key1086, -2), (key972, -2), (key1227, -6), (key1092, 2), (key1092, 2), (key978, 2)]

def rawRow1887 : Integer.Sparse Key := [(key1227, -2), (key1227, -2), (key1244, -2), (key1227, 6), (key1092, 2), (key1092, 2), (key1163, 2), (key978, -2), (key1092, -2), (key1092, -2), (key1086, -6), (key972, 2), (key1086, 2), (key1086, 2)]

def rawRow1888 : Integer.Sparse Key := [(key1227, -2), (key1244, -2), (key1227, -2), (key1227, 6), (key1092, 2), (key1163, 2), (key1092, 2), (key1092, -2), (key978, -2), (key1092, -2), (key1086, -6), (key1086, 2), (key972, 2), (key1086, 2)]

def rawRow1889 : Integer.Sparse Key := [(key1244, -2), (key1227, -2), (key1227, -2), (key1227, 6), (key1163, 2), (key1092, 2), (key1092, 2), (key1092, -2), (key1092, -2), (key978, -2), (key1086, -6), (key1086, 2), (key1086, 2), (key972, 2)]

end MUB6.Certificate.GramRows

end OAI
end


