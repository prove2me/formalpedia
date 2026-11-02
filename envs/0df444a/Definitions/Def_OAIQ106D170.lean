-- Prove2me | Definitions.Def_OAIQ106D170
-- name    : OAIQ106D170
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:34:36.17705+00:00
-- url     : https://prove2.me/theorems/96c48b8c-10de-4f84-8f75-fbfe429e58fd
-- title:
--   Definitions bundle OAIQ106D170 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 547 declarations of OpenAI's Lean: 547 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow2958`, `OAI.MUB6.Certificate.GramRows.rawRow2959`, `OAI.MUB6.Certificate.GramRows.rawRow296`, `OAI.MUB6.Certificate.GramRows.rawRow298`, `OAI.MUB6.Certificate.GramRows.rawRow2984`, `OAI.MUB6.Certificate.GramRows.rawRow2985`, `OAI.MUB6.Certificate.GramRows.rawRow2986`, `OAI.MUB6.Certificate.GramRows.rawRow2987`, `OAI.MUB6.Certificate.GramRows.rawRow2988`, `OAI.MUB6.Certificate.GramRows.rawRow2989`, `OAI.MUB6.Certificate.GramRows.rawRow299`, `OAI.MUB6.Certificate.GramRows.rawRow2990`, `OAI.MUB6.Certificate.GramRows.rawRow2991`, `OAI.MUB6.Certificate.GramRows.rawRow2992`, `OAI.MUB6.Certificate.GramRows.rawRow2993`, `OAI.MUB6.Certificate.GramRows.rawRow2994`, `OAI.MUB6.Certificate.GramRows.rawRow2995`, `OAI.MUB6.Certificate.GramRows.rawRow2996`, `OAI.MUB6.Certificate.GramRows.rawRow2997`, `OAI.MUB6.Certificate.GramRows.rawRow2998`, `OAI.MUB6.Certificate.GramRows.rawRow2999`, `OAI.MUB6.Certificate.GramRows.rawRow3`, `OAI.MUB6.Certificate.GramRows.rawRow300`, `OAI.MUB6.Certificate.GramRows.rawRow3000`, `OAI.MUB6.Certificate.GramRows.rawRow3001`, `OAI.MUB6.Certificate.GramRows.rawRow3002`, `OAI.MUB6.Certificate.GramRows.rawRow3003`, `OAI.MUB6.Certificate.GramRows.rawRow3004`, `OAI.MUB6.Certificate.GramRows.rawRow3005`, `OAI.MUB6.Certificate.GramRows.rawRow3006`, `OAI.MUB6.Certificate.GramRows.rawRow3007`, `OAI.MUB6.Certificate.GramRows.rawRow3008`, `OAI.MUB6.Certificate.GramRows.rawRow3009`, `OAI.MUB6.Certificate.GramRows.rawRow301`, `OAI.MUB6.Certificate.GramRows.rawRow3010`, `OAI.MUB6.Certificate.GramRows.rawRow3011`, `OAI.MUB6.Certificate.GramRows.rawRow3012`, `OAI.MUB6.Certificate.GramRows.rawRow3013`, `OAI.MUB6.Certificate.GramRows.rawRow3014`, `OAI.MUB6.Certificate.GramRows.rawRow3015` and 507 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block47`, `MutuallyUnbiased_GramRows_Block48`, `MutuallyUnbiased_GramRows_Block49`, `MutuallyUnbiased_GramRows_Block50`, `MutuallyUnbiased_GramRows_Block52`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block54`, `MutuallyUnbiased_GramRows_Block55`, `MutuallyUnbiased_GramRows_Block6`, `MutuallyUnbiased_GramRows_Block7`, `MutuallyUnbiased_GramRows_Block8`, `MutuallyUnbiased_GramRows_Block9`.
--
--   **Imports.** It imports the bundles `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087`, `OAIQ106D090`, `OAIQ106D092` and `OAIQ106D094` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MUB6.Certificate.GramEntries.Block0.entryEval`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEval3_3`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow0`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow1`, `OAI.MUB6.Certificate.GramEntries.Block0.entryEvalRow2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_13`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval14_14`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_10`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_13`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_6`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval15_7`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_0`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_1`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_2`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_3`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_4`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_5`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEval17_8`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow11`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow14`, `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow15` and `OAI.MUB6.Certificate.GramEntries.Block1.entryEvalRow8`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D086
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092
import Definitions.Def_OAIQ106D094

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow3 : Integer.Sparse Key := [(key248, -1), (key251, -1), (key260, 2), (key236, 1), (key239, 1), (key267, -1), (key271, -1), (key239, -2), (key251, 1), (key260, 1), (key316, 1), (key319, 1), (key335, -2), (key302, -1), (key305, -1), (key335, 1), (key340, 1), (key305, 2), (key319, -1), (key328, -1), (key406, -1), (key409, -1), (key467, 1), (key469, 1), (key385, 1), (key388, 1), (key467, -1), (key475, -1), (key388, -1), (key397, -1), (key409, 1), (key418, 1), (key578, 2), (key593, -1), (key595, -1), (key568, -2), (key593, 1), (key601, 1), (key568, 1), (key572, 1), (key578, -1), (key583, -1)]

def rawRow33 : Integer.Sparse Key := [(key568, -1), (key572, -1), (key568, 2), (key593, 1), (key595, 1), (key578, -1), (key593, -1), (key601, -2), (key583, 1), (key601, 1), (key267, 1), (key271, 1), (key267, -2), (key467, -1), (key469, -1), (key335, 1), (key467, 1), (key475, 2), (key340, -1), (key475, -1), (key251, -1), (key260, -1), (key239, 1), (key251, 1), (key388, 1), (key397, 1), (key305, -1), (key388, -1), (key418, -1), (key450, -1), (key328, 1), (key450, 1), (key248, 2), (key236, -1), (key248, -1), (key316, -2), (key302, 1), (key316, 1), (key406, 1), (key435, 1), (key385, -1), (key435, -1)]

def rawRow34 : Integer.Sparse Key := [(key572, -1), (key568, -1), (key568, 2), (key595, 1), (key593, 1), (key593, -1), (key578, -1), (key601, -2), (key601, 1), (key583, 1), (key271, 1), (key267, 1), (key267, -2), (key469, -1), (key467, -1), (key467, 1), (key335, 1), (key475, 2), (key475, -1), (key340, -1), (key260, -1), (key251, -1), (key251, 1), (key239, 1), (key397, 1), (key388, 1), (key388, -1), (key305, -1), (key450, -1), (key418, -1), (key450, 1), (key328, 1), (key248, 2), (key248, -1), (key236, -1), (key316, -2), (key316, 1), (key302, 1), (key435, 1), (key406, 1), (key435, -1), (key385, -1)]

def rawRow38 : Integer.Sparse Key := [(key593, -1), (key595, -1), (key601, 2), (key568, 1), (key572, 1), (key583, -1), (key601, -1), (key568, -2), (key578, 1), (key593, 1), (key467, 1), (key469, 1), (key475, -2), (key267, -1), (key271, -1), (key340, 1), (key475, 1), (key267, 2), (key335, -1), (key467, -1), (key388, -1), (key397, -1), (key418, 1), (key450, 1), (key251, 1), (key260, 1), (key328, -1), (key450, -1), (key239, -1), (key251, -1), (key305, 1), (key388, 1), (key385, 2), (key406, -1), (key435, -1), (key248, -2), (key316, 1), (key435, 1), (key236, 1), (key248, 1), (key302, -1), (key316, -1)]

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

def rawRow2958 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2517, -2), (key2520, 6), (key2459, 2), (key2531, 2), (key2456, 2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, -6), (key2517, 2), (key2361, 2), (key2456, 2)]

def rawRow2959 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2517, -2), (key2520, 6), (key2531, 2), (key2459, 2), (key2456, 2), (key2520, -2), (key2459, -2), (key2364, -2), (key2456, -6), (key2517, 2), (key2456, 2), (key2361, 2)]

def rawRow2984 : Integer.Sparse Key := [(key1999, -2), (key1999, -2), (key2003, -2), (key2003, 6), (key2268, 2), (key2268, 2), (key2272, 2), (key2272, -2), (key2324, -2), (key2324, -2), (key2294, -6), (key2294, 2), (key2336, 2), (key2336, 2)]

def rawRow2985 : Integer.Sparse Key := [(key1999, -2), (key2003, -2), (key1999, -2), (key2003, 6), (key2268, 2), (key2272, 2), (key2268, 2), (key2324, -2), (key2272, -2), (key2324, -2), (key2294, -6), (key2336, 2), (key2294, 2), (key2336, 2)]

def rawRow2986 : Integer.Sparse Key := [(key2003, -2), (key1999, -2), (key1999, -2), (key2003, 6), (key2272, 2), (key2268, 2), (key2268, 2), (key2324, -2), (key2324, -2), (key2272, -2), (key2294, -6), (key2336, 2), (key2336, 2), (key2294, 2)]

def rawRow2987 : Integer.Sparse Key := [(key1999, -2), (key2003, -2), (key2003, -2), (key1999, 6), (key2323, 2), (key2324, 2), (key2324, 2), (key2268, -2), (key2268, -2), (key2323, -2), (key2336, -6), (key2294, 2), (key2294, 2), (key2336, 2)]

def rawRow2988 : Integer.Sparse Key := [(key2003, -2), (key1999, -2), (key2003, -2), (key1999, 6), (key2324, 2), (key2323, 2), (key2324, 2), (key2268, -2), (key2323, -2), (key2268, -2), (key2336, -6), (key2294, 2), (key2336, 2), (key2294, 2)]

def rawRow2989 : Integer.Sparse Key := [(key2003, -2), (key2003, -2), (key1999, -2), (key1999, 6), (key2324, 2), (key2324, 2), (key2323, 2), (key2323, -2), (key2268, -2), (key2268, -2), (key2336, -6), (key2336, 2), (key2294, 2), (key2294, 2)]

def rawRow2990 : Integer.Sparse Key := [(key2268, -2), (key2268, -2), (key2272, -2), (key2294, 6), (key1999, 2), (key1999, 2), (key2003, 2), (key2294, -2), (key2336, -2), (key2336, -2), (key2003, -6), (key2272, 2), (key2324, 2), (key2324, 2)]

def rawRow2991 : Integer.Sparse Key := [(key2268, -2), (key2272, -2), (key2268, -2), (key2294, 6), (key1999, 2), (key2003, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2336, -2), (key2003, -6), (key2324, 2), (key2272, 2), (key2324, 2)]

def rawRow2992 : Integer.Sparse Key := [(key2272, -2), (key2268, -2), (key2268, -2), (key2294, 6), (key2003, 2), (key1999, 2), (key1999, 2), (key2336, -2), (key2336, -2), (key2294, -2), (key2003, -6), (key2324, 2), (key2324, 2), (key2272, 2)]

def rawRow2993 : Integer.Sparse Key := [(key2268, -2), (key2272, -2), (key2294, -2), (key2268, 6), (key2323, 2), (key2324, 2), (key2336, 2), (key1999, -2), (key2268, -2), (key2323, -2), (key2324, -6), (key2003, 2), (key2272, 2), (key2324, 2)]

def rawRow2994 : Integer.Sparse Key := [(key2272, -2), (key2268, -2), (key2294, -2), (key2268, 6), (key2324, 2), (key2323, 2), (key2336, 2), (key1999, -2), (key2323, -2), (key2268, -2), (key2324, -6), (key2003, 2), (key2324, 2), (key2272, 2)]

def rawRow2995 : Integer.Sparse Key := [(key2268, -2), (key2294, -2), (key2272, -2), (key2268, 6), (key2323, 2), (key2336, 2), (key2324, 2), (key2268, -2), (key1999, -2), (key2323, -2), (key2324, -6), (key2272, 2), (key2003, 2), (key2324, 2)]

def rawRow2996 : Integer.Sparse Key := [(key2294, -2), (key2268, -2), (key2272, -2), (key2268, 6), (key2336, 2), (key2323, 2), (key2324, 2), (key2268, -2), (key2323, -2), (key1999, -2), (key2324, -6), (key2272, 2), (key2324, 2), (key2003, 2)]

def rawRow2997 : Integer.Sparse Key := [(key2272, -2), (key2294, -2), (key2268, -2), (key2268, 6), (key2324, 2), (key2336, 2), (key2323, 2), (key2323, -2), (key1999, -2), (key2268, -2), (key2324, -6), (key2324, 2), (key2003, 2), (key2272, 2)]

def rawRow2998 : Integer.Sparse Key := [(key2294, -2), (key2272, -2), (key2268, -2), (key2268, 6), (key2336, 2), (key2324, 2), (key2323, 2), (key2323, -2), (key2268, -2), (key1999, -2), (key2324, -6), (key2324, 2), (key2272, 2), (key2003, 2)]

def rawRow2999 : Integer.Sparse Key := [(key2323, -2), (key2324, -2), (key2324, -2), (key2336, 6), (key1999, 2), (key2003, 2), (key2003, 2), (key2294, -2), (key2294, -2), (key2336, -2), (key1999, -6), (key2268, 2), (key2268, 2), (key2323, 2)]

def rawRow3000 : Integer.Sparse Key := [(key2324, -2), (key2323, -2), (key2324, -2), (key2336, 6), (key2003, 2), (key1999, 2), (key2003, 2), (key2294, -2), (key2336, -2), (key2294, -2), (key1999, -6), (key2268, 2), (key2323, 2), (key2268, 2)]

def rawRow3001 : Integer.Sparse Key := [(key2324, -2), (key2324, -2), (key2323, -2), (key2336, 6), (key2003, 2), (key2003, 2), (key1999, 2), (key2336, -2), (key2294, -2), (key2294, -2), (key1999, -6), (key2323, 2), (key2268, 2), (key2268, 2)]

def rawRow3002 : Integer.Sparse Key := [(key2323, -2), (key2324, -2), (key2336, -2), (key2324, 6), (key2268, 2), (key2272, 2), (key2294, 2), (key2003, -2), (key2272, -2), (key2324, -2), (key2268, -6), (key1999, 2), (key2268, 2), (key2323, 2)]

def rawRow3003 : Integer.Sparse Key := [(key2324, -2), (key2323, -2), (key2336, -2), (key2324, 6), (key2272, 2), (key2268, 2), (key2294, 2), (key2003, -2), (key2324, -2), (key2272, -2), (key2268, -6), (key1999, 2), (key2323, 2), (key2268, 2)]

def rawRow3004 : Integer.Sparse Key := [(key2323, -2), (key2336, -2), (key2324, -2), (key2324, 6), (key2268, 2), (key2294, 2), (key2272, 2), (key2272, -2), (key2003, -2), (key2324, -2), (key2268, -6), (key2268, 2), (key1999, 2), (key2323, 2)]

def rawRow3005 : Integer.Sparse Key := [(key2336, -2), (key2323, -2), (key2324, -2), (key2324, 6), (key2294, 2), (key2268, 2), (key2272, 2), (key2272, -2), (key2324, -2), (key2003, -2), (key2268, -6), (key2268, 2), (key2323, 2), (key1999, 2)]

def rawRow3006 : Integer.Sparse Key := [(key2324, -2), (key2336, -2), (key2323, -2), (key2324, 6), (key2272, 2), (key2294, 2), (key2268, 2), (key2324, -2), (key2003, -2), (key2272, -2), (key2268, -6), (key2323, 2), (key1999, 2), (key2268, 2)]

def rawRow3007 : Integer.Sparse Key := [(key2336, -2), (key2324, -2), (key2323, -2), (key2324, 6), (key2294, 2), (key2272, 2), (key2268, 2), (key2324, -2), (key2272, -2), (key2003, -2), (key2268, -6), (key2323, 2), (key2268, 2), (key1999, 2)]

def rawRow3008 : Integer.Sparse Key := [(key2362, -2), (key2365, -2), (key2365, -2), (key2365, 2), (key2365, 2), (key2367, 2), (key2457, 2), (key2460, 2), (key2460, 2), (key2460, -1), (key2460, -1), (key2521, -1), (key2521, -1), (key2525, -1), (key2525, -1), (key2532, -2), (key2532, -2), (key2533, -2), (key2532, 1), (key2532, 1), (key2562, 1), (key2562, 1), (key2564, 1), (key2564, 1)]

def rawRow3009 : Integer.Sparse Key := [(key2365, -2), (key2362, -2), (key2365, -2), (key2365, 2), (key2367, 2), (key2365, 2), (key2460, 2), (key2457, 2), (key2460, 2), (key2521, -1), (key2525, -1), (key2460, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2532, -2), (key2533, -2), (key2532, -2), (key2562, 1), (key2564, 1), (key2532, 1), (key2564, 1), (key2532, 1), (key2562, 1)]

def rawRow3010 : Integer.Sparse Key := [(key2365, -2), (key2365, -2), (key2362, -2), (key2367, 2), (key2365, 2), (key2365, 2), (key2460, 2), (key2460, 2), (key2457, 2), (key2525, -1), (key2521, -1), (key2525, -1), (key2460, -1), (key2521, -1), (key2460, -1), (key2533, -2), (key2532, -2), (key2532, -2), (key2564, 1), (key2562, 1), (key2564, 1), (key2532, 1), (key2562, 1), (key2532, 1)]

def rawRow3011 : Integer.Sparse Key := [(key2365, -2), (key2365, -2), (key2367, -2), (key2362, 2), (key2365, 2), (key2365, 2), (key2521, 2), (key2521, 2), (key2525, 2), (key2457, -1), (key2460, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2521, -1), (key2562, -2), (key2564, -2), (key2564, -2), (key2532, 1), (key2533, 1), (key2532, 1), (key2564, 1), (key2533, 1), (key2564, 1)]

def rawRow3012 : Integer.Sparse Key := [(key2365, -2), (key2367, -2), (key2365, -2), (key2365, 2), (key2362, 2), (key2365, 2), (key2521, 2), (key2525, 2), (key2521, 2), (key2460, -1), (key2457, -1), (key2521, -1), (key2457, -1), (key2521, -1), (key2460, -1), (key2564, -2), (key2562, -2), (key2564, -2), (key2533, 1), (key2532, 1), (key2564, 1), (key2532, 1), (key2564, 1), (key2533, 1)]

def rawRow3013 : Integer.Sparse Key := [(key2367, -2), (key2365, -2), (key2365, -2), (key2365, 2), (key2365, 2), (key2362, 2), (key2525, 2), (key2521, 2), (key2521, 2), (key2521, -1), (key2521, -1), (key2460, -1), (key2460, -1), (key2457, -1), (key2457, -1), (key2564, -2), (key2564, -2), (key2562, -2), (key2564, 1), (key2564, 1), (key2533, 1), (key2533, 1), (key2532, 1), (key2532, 1)]

def rawRow3014 : Integer.Sparse Key := [(key2457, -2), (key2460, -2), (key2460, -2), (key2521, 2), (key2521, 2), (key2525, 2), (key2362, 2), (key2365, 2), (key2365, 2), (key2532, -1), (key2532, -1), (key2562, -1), (key2562, -1), (key2564, -1), (key2564, -1), (key2365, -2), (key2365, -2), (key2367, -2), (key2460, 1), (key2460, 1), (key2521, 1), (key2521, 1), (key2525, 1), (key2525, 1)]

def rawRow3015 : Integer.Sparse Key := [(key2460, -2), (key2457, -2), (key2460, -2), (key2521, 2), (key2525, 2), (key2521, 2), (key2365, 2), (key2362, 2), (key2365, 2), (key2562, -1), (key2564, -1), (key2532, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2365, -2), (key2367, -2), (key2365, -2), (key2521, 1), (key2525, 1), (key2460, 1), (key2525, 1), (key2460, 1), (key2521, 1)]

def rawRow3016 : Integer.Sparse Key := [(key2460, -2), (key2460, -2), (key2457, -2), (key2525, 2), (key2521, 2), (key2521, 2), (key2365, 2), (key2365, 2), (key2362, 2), (key2564, -1), (key2562, -1), (key2564, -1), (key2532, -1), (key2562, -1), (key2532, -1), (key2367, -2), (key2365, -2), (key2365, -2), (key2525, 1), (key2521, 1), (key2525, 1), (key2460, 1), (key2521, 1), (key2460, 1)]

def rawRow3017 : Integer.Sparse Key := [(key2460, -2), (key2521, -2), (key2525, -2), (key2457, 2), (key2460, 2), (key2521, 2), (key2532, 2), (key2562, 2), (key2564, 2), (key2362, -1), (key2365, -1), (key2457, -1), (key2521, -1), (key2532, -1), (key2562, -1), (key2521, -2), (key2525, -2), (key2564, -2), (key2365, 1), (key2367, 1), (key2460, 1), (key2525, 1), (key2533, 1), (key2564, 1)]

def rawRow3018 : Integer.Sparse Key := [(key2460, -2), (key2525, -2), (key2521, -2), (key2460, 2), (key2457, 2), (key2521, 2), (key2532, 2), (key2564, 2), (key2562, 2), (key2365, -1), (key2362, -1), (key2521, -1), (key2457, -1), (key2562, -1), (key2532, -1), (key2525, -2), (key2521, -2), (key2564, -2), (key2367, 1), (key2365, 1), (key2525, 1), (key2460, 1), (key2564, 1), (key2533, 1)]

def rawRow3019 : Integer.Sparse Key := [(key2521, -2), (key2460, -2), (key2525, -2), (key2457, 2), (key2521, 2), (key2460, 2), (key2562, 2), (key2532, 2), (key2564, 2), (key2457, -1), (key2521, -1), (key2362, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2521, -2), (key2564, -2), (key2525, -2), (key2460, 1), (key2533, 1), (key2365, 1), (key2564, 1), (key2367, 1), (key2525, 1)]

def rawRow3020 : Integer.Sparse Key := [(key2521, -2), (key2525, -2), (key2460, -2), (key2521, 2), (key2457, 2), (key2460, 2), (key2562, 2), (key2564, 2), (key2532, 2), (key2521, -1), (key2457, -1), (key2562, -1), (key2362, -1), (key2521, -1), (key2365, -1), (key2564, -2), (key2521, -2), (key2525, -2), (key2533, 1), (key2460, 1), (key2564, 1), (key2365, 1), (key2525, 1), (key2367, 1)]

def rawRow3021 : Integer.Sparse Key := [(key2525, -2), (key2460, -2), (key2521, -2), (key2460, 2), (key2521, 2), (key2457, 2), (key2564, 2), (key2532, 2), (key2562, 2), (key2532, -1), (key2562, -1), (key2365, -1), (key2521, -1), (key2362, -1), (key2457, -1), (key2525, -2), (key2564, -2), (key2521, -2), (key2525, 1), (key2564, 1), (key2367, 1), (key2533, 1), (key2365, 1), (key2460, 1)]

def rawRow3022 : Integer.Sparse Key := [(key2525, -2), (key2521, -2), (key2460, -2), (key2521, 2), (key2460, 2), (key2457, 2), (key2564, 2), (key2562, 2), (key2532, 2), (key2562, -1), (key2532, -1), (key2521, -1), (key2365, -1), (key2457, -1), (key2362, -1), (key2564, -2), (key2525, -2), (key2521, -2), (key2564, 1), (key2525, 1), (key2533, 1), (key2367, 1), (key2460, 1), (key2365, 1)]

def rawRow3023 : Integer.Sparse Key := [(key2532, -2), (key2532, -2), (key2533, -2), (key2562, 2), (key2564, 2), (key2564, 2), (key2365, 2), (key2365, 2), (key2367, 2), (key2521, -1), (key2525, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2564, -1), (key2362, -2), (key2365, -2), (key2365, -2), (key2457, 1), (key2460, 1), (key2457, 1), (key2521, 1), (key2460, 1), (key2521, 1)]

def rawRow3024 : Integer.Sparse Key := [(key2532, -2), (key2533, -2), (key2532, -2), (key2564, 2), (key2562, 2), (key2564, 2), (key2365, 2), (key2367, 2), (key2365, 2), (key2525, -1), (key2521, -1), (key2564, -1), (key2521, -1), (key2564, -1), (key2525, -1), (key2365, -2), (key2362, -2), (key2365, -2), (key2460, 1), (key2457, 1), (key2521, 1), (key2457, 1), (key2521, 1), (key2460, 1)]

def rawRow3025 : Integer.Sparse Key := [(key2533, -2), (key2532, -2), (key2532, -2), (key2564, 2), (key2564, 2), (key2562, 2), (key2367, 2), (key2365, 2), (key2365, 2), (key2564, -1), (key2564, -1), (key2525, -1), (key2525, -1), (key2521, -1), (key2521, -1), (key2365, -2), (key2365, -2), (key2362, -2), (key2521, 1), (key2521, 1), (key2460, 1), (key2460, 1), (key2457, 1), (key2457, 1)]

def rawRow3026 : Integer.Sparse Key := [(key2532, -2), (key2562, -2), (key2564, -2), (key2532, 2), (key2533, 2), (key2564, 2), (key2460, 2), (key2521, 2), (key2525, 2), (key2365, -1), (key2367, -1), (key2460, -1), (key2533, -1), (key2525, -1), (key2564, -1), (key2457, -2), (key2460, -2), (key2521, -2), (key2362, 1), (key2365, 1), (key2457, 1), (key2521, 1), (key2532, 1), (key2562, 1)]

def rawRow3027 : Integer.Sparse Key := [(key2532, -2), (key2564, -2), (key2562, -2), (key2533, 2), (key2532, 2), (key2564, 2), (key2460, 2), (key2525, 2), (key2521, 2), (key2367, -1), (key2365, -1), (key2533, -1), (key2460, -1), (key2564, -1), (key2525, -1), (key2460, -2), (key2457, -2), (key2521, -2), (key2365, 1), (key2362, 1), (key2521, 1), (key2457, 1), (key2562, 1), (key2532, 1)]

def rawRow3028 : Integer.Sparse Key := [(key2562, -2), (key2532, -2), (key2564, -2), (key2532, 2), (key2564, 2), (key2533, 2), (key2521, 2), (key2460, 2), (key2525, 2), (key2460, -1), (key2525, -1), (key2365, -1), (key2564, -1), (key2367, -1), (key2533, -1), (key2457, -2), (key2521, -2), (key2460, -2), (key2457, 1), (key2521, 1), (key2362, 1), (key2562, 1), (key2365, 1), (key2521, 1)]

def rawRow3029 : Integer.Sparse Key := [(key2562, -2), (key2564, -2), (key2532, -2), (key2564, 2), (key2532, 2), (key2533, 2), (key2521, 2), (key2525, 2), (key2460, 2), (key2525, -1), (key2460, -1), (key2564, -1), (key2365, -1), (key2533, -1), (key2367, -1), (key2521, -2), (key2457, -2), (key2460, -2), (key2521, 1), (key2457, 1), (key2562, 1), (key2362, 1), (key2521, 1), (key2365, 1)]

def rawRow3030 : Integer.Sparse Key := [(key2564, -2), (key2532, -2), (key2562, -2), (key2533, 2), (key2564, 2), (key2532, 2), (key2525, 2), (key2460, 2), (key2521, 2), (key2533, -1), (key2564, -1), (key2367, -1), (key2525, -1), (key2365, -1), (key2460, -1), (key2460, -2), (key2521, -2), (key2457, -2), (key2532, 1), (key2562, 1), (key2365, 1), (key2521, 1), (key2362, 1), (key2457, 1)]

def rawRow3031 : Integer.Sparse Key := [(key2564, -2), (key2562, -2), (key2532, -2), (key2564, 2), (key2533, 2), (key2532, 2), (key2525, 2), (key2521, 2), (key2460, 2), (key2564, -1), (key2533, -1), (key2525, -1), (key2367, -1), (key2460, -1), (key2365, -1), (key2521, -2), (key2460, -2), (key2457, -2), (key2562, 1), (key2532, 1), (key2521, 1), (key2365, 1), (key2457, 1), (key2362, 1)]

def rawRow3050 : Integer.Sparse Key := [(key1471, -6), (key1384, 2), (key1417, 2), (key1417, 2), (key1902, 6), (key1289, -2), (key1566, -2), (key1566, -2), (key1895, -2), (key1917, -2), (key1917, -2), (key1350, 2), (key1680, 2), (key1680, 2)]

def rawRow3051 : Integer.Sparse Key := [(key1471, -6), (key1417, 2), (key1384, 2), (key1417, 2), (key1902, 6), (key1566, -2), (key1289, -2), (key1566, -2), (key1917, -2), (key1895, -2), (key1917, -2), (key1680, 2), (key1350, 2), (key1680, 2)]

def rawRow3052 : Integer.Sparse Key := [(key1471, -6), (key1417, 2), (key1417, 2), (key1384, 2), (key1902, 6), (key1566, -2), (key1566, -2), (key1289, -2), (key1917, -2), (key1917, -2), (key1895, -2), (key1680, 2), (key1680, 2), (key1350, 2)]

def rawRow3053 : Integer.Sparse Key := [(key1680, -6), (key1539, 2), (key1566, 2), (key1615, 2), (key1917, 6), (key1309, -2), (key1417, -2), (key1615, -2), (key1895, -2), (key1902, -2), (key1917, -2), (key1350, 2), (key1471, 2), (key1680, 2)]

def rawRow3054 : Integer.Sparse Key := [(key1680, -6), (key1539, 2), (key1615, 2), (key1566, 2), (key1917, 6), (key1309, -2), (key1615, -2), (key1417, -2), (key1895, -2), (key1917, -2), (key1902, -2), (key1350, 2), (key1680, 2), (key1471, 2)]

def rawRow3055 : Integer.Sparse Key := [(key1680, -6), (key1566, 2), (key1539, 2), (key1615, 2), (key1917, 6), (key1417, -2), (key1309, -2), (key1615, -2), (key1902, -2), (key1895, -2), (key1917, -2), (key1471, 2), (key1350, 2), (key1680, 2)]

def rawRow3056 : Integer.Sparse Key := [(key1680, -6), (key1566, 2), (key1615, 2), (key1539, 2), (key1917, 6), (key1417, -2), (key1615, -2), (key1309, -2), (key1902, -2), (key1917, -2), (key1895, -2), (key1471, 2), (key1680, 2), (key1350, 2)]

def rawRow3057 : Integer.Sparse Key := [(key1680, -6), (key1615, 2), (key1539, 2), (key1566, 2), (key1917, 6), (key1615, -2), (key1309, -2), (key1417, -2), (key1917, -2), (key1895, -2), (key1902, -2), (key1680, 2), (key1350, 2), (key1471, 2)]

def rawRow3058 : Integer.Sparse Key := [(key1680, -6), (key1615, 2), (key1566, 2), (key1539, 2), (key1917, 6), (key1615, -2), (key1417, -2), (key1309, -2), (key1917, -2), (key1902, -2), (key1895, -2), (key1680, 2), (key1471, 2), (key1350, 2)]

def rawRow3059 : Integer.Sparse Key := [(key1902, -6), (key1895, 2), (key1917, 2), (key1917, 2), (key1471, 6), (key1350, -2), (key1680, -2), (key1680, -2), (key1384, -2), (key1417, -2), (key1417, -2), (key1289, 2), (key1566, 2), (key1566, 2)]

def rawRow3060 : Integer.Sparse Key := [(key1902, -6), (key1917, 2), (key1895, 2), (key1917, 2), (key1471, 6), (key1680, -2), (key1350, -2), (key1680, -2), (key1417, -2), (key1384, -2), (key1417, -2), (key1566, 2), (key1289, 2), (key1566, 2)]

def rawRow3061 : Integer.Sparse Key := [(key1902, -6), (key1917, 2), (key1917, 2), (key1895, 2), (key1471, 6), (key1680, -2), (key1680, -2), (key1350, -2), (key1417, -2), (key1417, -2), (key1384, -2), (key1566, 2), (key1566, 2), (key1289, 2)]

def rawRow3062 : Integer.Sparse Key := [(key1917, -6), (key1895, 2), (key1902, 2), (key1917, 2), (key1680, 6), (key1350, -2), (key1471, -2), (key1680, -2), (key1539, -2), (key1566, -2), (key1615, -2), (key1309, 2), (key1417, 2), (key1615, 2)]

def rawRow3063 : Integer.Sparse Key := [(key1917, -6), (key1895, 2), (key1917, 2), (key1902, 2), (key1680, 6), (key1350, -2), (key1680, -2), (key1471, -2), (key1539, -2), (key1615, -2), (key1566, -2), (key1309, 2), (key1615, 2), (key1417, 2)]

def rawRow3064 : Integer.Sparse Key := [(key1917, -6), (key1902, 2), (key1895, 2), (key1917, 2), (key1680, 6), (key1471, -2), (key1350, -2), (key1680, -2), (key1566, -2), (key1539, -2), (key1615, -2), (key1417, 2), (key1309, 2), (key1615, 2)]

def rawRow3065 : Integer.Sparse Key := [(key1917, -6), (key1902, 2), (key1917, 2), (key1895, 2), (key1680, 6), (key1471, -2), (key1680, -2), (key1350, -2), (key1566, -2), (key1615, -2), (key1539, -2), (key1417, 2), (key1615, 2), (key1309, 2)]

def rawRow3066 : Integer.Sparse Key := [(key1917, -6), (key1917, 2), (key1895, 2), (key1902, 2), (key1680, 6), (key1680, -2), (key1350, -2), (key1471, -2), (key1615, -2), (key1539, -2), (key1566, -2), (key1615, 2), (key1309, 2), (key1417, 2)]

def rawRow3067 : Integer.Sparse Key := [(key1917, -6), (key1917, 2), (key1902, 2), (key1895, 2), (key1680, 6), (key1680, -2), (key1471, -2), (key1350, -2), (key1615, -2), (key1566, -2), (key1539, -2), (key1615, 2), (key1417, 2), (key1309, 2)]

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

def rawRow3086 : Integer.Sparse Key := [(key1028, -2), (key1036, -2), (key1071, -2), (key1036, 6), (key1106, 2), (key1114, 2), (key1150, 2), (key1001, -2), (key1114, -2), (key1232, -2), (key1123, -6), (key1015, 2), (key1123, 2), (key1235, 2)]

def rawRow3087 : Integer.Sparse Key := [(key1036, -2), (key1028, -2), (key1071, -2), (key1036, 6), (key1114, 2), (key1106, 2), (key1150, 2), (key1001, -2), (key1232, -2), (key1114, -2), (key1123, -6), (key1015, 2), (key1235, 2), (key1123, 2)]

def rawRow3088 : Integer.Sparse Key := [(key1028, -2), (key1071, -2), (key1036, -2), (key1036, 6), (key1106, 2), (key1150, 2), (key1114, 2), (key1114, -2), (key1001, -2), (key1232, -2), (key1123, -6), (key1123, 2), (key1015, 2), (key1235, 2)]

def rawRow3089 : Integer.Sparse Key := [(key1071, -2), (key1028, -2), (key1036, -2), (key1036, 6), (key1150, 2), (key1106, 2), (key1114, 2), (key1114, -2), (key1232, -2), (key1001, -2), (key1123, -6), (key1123, 2), (key1235, 2), (key1015, 2)]

def rawRow3090 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1028, -2), (key1036, 6), (key1114, 2), (key1150, 2), (key1106, 2), (key1232, -2), (key1001, -2), (key1114, -2), (key1123, -6), (key1235, 2), (key1015, 2), (key1123, 2)]

def rawRow3091 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1028, -2), (key1036, 6), (key1150, 2), (key1114, 2), (key1106, 2), (key1232, -2), (key1114, -2), (key1001, -2), (key1123, -6), (key1235, 2), (key1123, 2), (key1015, 2)]

def rawRow3092 : Integer.Sparse Key := [(key1036, -2), (key1036, -2), (key1071, -2), (key1028, 6), (key1232, 2), (key1232, 2), (key1242, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1235, -6), (key1015, 2), (key1123, 2), (key1123, 2)]

def rawRow3093 : Integer.Sparse Key := [(key1036, -2), (key1071, -2), (key1036, -2), (key1028, 6), (key1232, 2), (key1242, 2), (key1232, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1235, -6), (key1123, 2), (key1015, 2), (key1123, 2)]

def rawRow3094 : Integer.Sparse Key := [(key1071, -2), (key1036, -2), (key1036, -2), (key1028, 6), (key1242, 2), (key1232, 2), (key1232, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1235, -6), (key1123, 2), (key1123, 2), (key1015, 2)]

def rawRow3095 : Integer.Sparse Key := [(key1106, -2), (key1114, -2), (key1150, -2), (key1123, 6), (key1028, 2), (key1036, 2), (key1071, 2), (key1015, -2), (key1123, -2), (key1235, -2), (key1036, -6), (key1001, 2), (key1114, 2), (key1232, 2)]

def rawRow3096 : Integer.Sparse Key := [(key1114, -2), (key1106, -2), (key1150, -2), (key1123, 6), (key1036, 2), (key1028, 2), (key1071, 2), (key1015, -2), (key1235, -2), (key1123, -2), (key1036, -6), (key1001, 2), (key1232, 2), (key1114, 2)]

def rawRow3097 : Integer.Sparse Key := [(key1106, -2), (key1150, -2), (key1114, -2), (key1123, 6), (key1028, 2), (key1071, 2), (key1036, 2), (key1123, -2), (key1015, -2), (key1235, -2), (key1036, -6), (key1114, 2), (key1001, 2), (key1232, 2)]

def rawRow3098 : Integer.Sparse Key := [(key1150, -2), (key1106, -2), (key1114, -2), (key1123, 6), (key1071, 2), (key1028, 2), (key1036, 2), (key1123, -2), (key1235, -2), (key1015, -2), (key1036, -6), (key1114, 2), (key1232, 2), (key1001, 2)]

def rawRow3099 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1106, -2), (key1123, 6), (key1036, 2), (key1071, 2), (key1028, 2), (key1235, -2), (key1015, -2), (key1123, -2), (key1036, -6), (key1232, 2), (key1001, 2), (key1114, 2)]

def rawRow3100 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1106, -2), (key1123, 6), (key1071, 2), (key1036, 2), (key1028, 2), (key1235, -2), (key1123, -2), (key1015, -2), (key1036, -6), (key1232, 2), (key1114, 2), (key1001, 2)]

def rawRow3101 : Integer.Sparse Key := [(key1114, -2), (key1123, -2), (key1150, -2), (key1106, 6), (key1232, 2), (key1235, 2), (key1242, 2), (key993, -2), (key1028, -2), (key1106, -2), (key1232, -6), (key1001, 2), (key1036, 2), (key1114, 2)]

def rawRow3102 : Integer.Sparse Key := [(key1123, -2), (key1114, -2), (key1150, -2), (key1106, 6), (key1235, 2), (key1232, 2), (key1242, 2), (key993, -2), (key1106, -2), (key1028, -2), (key1232, -6), (key1001, 2), (key1114, 2), (key1036, 2)]

def rawRow3103 : Integer.Sparse Key := [(key1114, -2), (key1150, -2), (key1123, -2), (key1106, 6), (key1232, 2), (key1242, 2), (key1235, 2), (key1028, -2), (key993, -2), (key1106, -2), (key1232, -6), (key1036, 2), (key1001, 2), (key1114, 2)]

def rawRow3104 : Integer.Sparse Key := [(key1150, -2), (key1114, -2), (key1123, -2), (key1106, 6), (key1242, 2), (key1232, 2), (key1235, 2), (key1028, -2), (key1106, -2), (key993, -2), (key1232, -6), (key1036, 2), (key1114, 2), (key1001, 2)]

def rawRow3105 : Integer.Sparse Key := [(key1123, -2), (key1150, -2), (key1114, -2), (key1106, 6), (key1235, 2), (key1242, 2), (key1232, 2), (key1106, -2), (key993, -2), (key1028, -2), (key1232, -6), (key1114, 2), (key1001, 2), (key1036, 2)]

def rawRow3106 : Integer.Sparse Key := [(key1150, -2), (key1123, -2), (key1114, -2), (key1106, 6), (key1242, 2), (key1235, 2), (key1232, 2), (key1106, -2), (key1028, -2), (key993, -2), (key1232, -6), (key1114, 2), (key1036, 2), (key1001, 2)]

def rawRow3107 : Integer.Sparse Key := [(key1232, -2), (key1232, -2), (key1242, -2), (key1235, 6), (key1036, 2), (key1036, 2), (key1071, 2), (key1015, -2), (key1123, -2), (key1123, -2), (key1028, -6), (key993, 2), (key1106, 2), (key1106, 2)]

def rawRow3108 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1232, -2), (key1235, 6), (key1036, 2), (key1071, 2), (key1036, 2), (key1123, -2), (key1015, -2), (key1123, -2), (key1028, -6), (key1106, 2), (key993, 2), (key1106, 2)]

def rawRow3109 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1232, -2), (key1235, 6), (key1071, 2), (key1036, 2), (key1036, 2), (key1123, -2), (key1123, -2), (key1015, -2), (key1028, -6), (key1106, 2), (key1106, 2), (key993, 2)]

def rawRow3110 : Integer.Sparse Key := [(key1232, -2), (key1235, -2), (key1242, -2), (key1232, 6), (key1114, 2), (key1123, 2), (key1150, 2), (key1001, -2), (key1036, -2), (key1114, -2), (key1106, -6), (key993, 2), (key1028, 2), (key1106, 2)]

def rawRow3111 : Integer.Sparse Key := [(key1235, -2), (key1232, -2), (key1242, -2), (key1232, 6), (key1123, 2), (key1114, 2), (key1150, 2), (key1001, -2), (key1114, -2), (key1036, -2), (key1106, -6), (key993, 2), (key1106, 2), (key1028, 2)]

def rawRow3112 : Integer.Sparse Key := [(key1232, -2), (key1242, -2), (key1235, -2), (key1232, 6), (key1114, 2), (key1150, 2), (key1123, 2), (key1036, -2), (key1001, -2), (key1114, -2), (key1106, -6), (key1028, 2), (key993, 2), (key1106, 2)]

def rawRow3113 : Integer.Sparse Key := [(key1242, -2), (key1232, -2), (key1235, -2), (key1232, 6), (key1150, 2), (key1114, 2), (key1123, 2), (key1036, -2), (key1114, -2), (key1001, -2), (key1106, -6), (key1028, 2), (key1106, 2), (key993, 2)]

def rawRow3114 : Integer.Sparse Key := [(key1235, -2), (key1242, -2), (key1232, -2), (key1232, 6), (key1123, 2), (key1150, 2), (key1114, 2), (key1114, -2), (key1001, -2), (key1036, -2), (key1106, -6), (key1106, 2), (key993, 2), (key1028, 2)]

def rawRow3115 : Integer.Sparse Key := [(key1242, -2), (key1235, -2), (key1232, -2), (key1232, 6), (key1150, 2), (key1123, 2), (key1114, 2), (key1114, -2), (key1036, -2), (key1001, -2), (key1106, -6), (key1106, 2), (key1028, 2), (key993, 2)]

def rawRow3116 : Integer.Sparse Key := [(key2780, -6), (key2665, 2), (key2780, 2), (key2789, 2), (key2803, 6), (key2610, -2), (key2803, -2), (key2824, -2), (key2700, -2), (key2853, -2), (key2855, -2), (key2626, 2), (key2853, 2), (key2865, 2)]

def rawRow3117 : Integer.Sparse Key := [(key2780, -6), (key2665, 2), (key2789, 2), (key2780, 2), (key2803, 6), (key2610, -2), (key2824, -2), (key2803, -2), (key2700, -2), (key2855, -2), (key2853, -2), (key2626, 2), (key2865, 2), (key2853, 2)]

def rawRow3118 : Integer.Sparse Key := [(key2780, -6), (key2780, 2), (key2665, 2), (key2789, 2), (key2803, 6), (key2803, -2), (key2610, -2), (key2824, -2), (key2853, -2), (key2700, -2), (key2855, -2), (key2853, 2), (key2626, 2), (key2865, 2)]

def rawRow3119 : Integer.Sparse Key := [(key2780, -6), (key2780, 2), (key2789, 2), (key2665, 2), (key2803, 6), (key2803, -2), (key2824, -2), (key2610, -2), (key2853, -2), (key2855, -2), (key2700, -2), (key2853, 2), (key2865, 2), (key2626, 2)]

def rawRow3120 : Integer.Sparse Key := [(key2780, -6), (key2789, 2), (key2665, 2), (key2780, 2), (key2803, 6), (key2824, -2), (key2610, -2), (key2803, -2), (key2855, -2), (key2700, -2), (key2853, -2), (key2865, 2), (key2626, 2), (key2853, 2)]

def rawRow3121 : Integer.Sparse Key := [(key2780, -6), (key2789, 2), (key2780, 2), (key2665, 2), (key2803, 6), (key2824, -2), (key2803, -2), (key2610, -2), (key2855, -2), (key2853, -2), (key2700, -2), (key2865, 2), (key2853, 2), (key2626, 2)]

def rawRow3122 : Integer.Sparse Key := [(key2789, -6), (key2665, 2), (key2780, 2), (key2780, 2), (key2824, 6), (key2610, -2), (key2803, -2), (key2803, -2), (key2721, -2), (key2865, -2), (key2865, -2), (key2635, 2), (key2855, 2), (key2855, 2)]

def rawRow3123 : Integer.Sparse Key := [(key2789, -6), (key2780, 2), (key2665, 2), (key2780, 2), (key2824, 6), (key2803, -2), (key2610, -2), (key2803, -2), (key2865, -2), (key2721, -2), (key2865, -2), (key2855, 2), (key2635, 2), (key2855, 2)]

def rawRow3124 : Integer.Sparse Key := [(key2789, -6), (key2780, 2), (key2780, 2), (key2665, 2), (key2824, 6), (key2803, -2), (key2803, -2), (key2610, -2), (key2865, -2), (key2865, -2), (key2721, -2), (key2855, 2), (key2855, 2), (key2635, 2)]

def rawRow3125 : Integer.Sparse Key := [(key2803, -6), (key2700, 2), (key2853, 2), (key2855, 2), (key2780, 6), (key2626, -2), (key2853, -2), (key2865, -2), (key2665, -2), (key2780, -2), (key2789, -2), (key2610, 2), (key2803, 2), (key2824, 2)]

def rawRow3126 : Integer.Sparse Key := [(key2803, -6), (key2700, 2), (key2855, 2), (key2853, 2), (key2780, 6), (key2626, -2), (key2865, -2), (key2853, -2), (key2665, -2), (key2789, -2), (key2780, -2), (key2610, 2), (key2824, 2), (key2803, 2)]

def rawRow3127 : Integer.Sparse Key := [(key2803, -6), (key2853, 2), (key2700, 2), (key2855, 2), (key2780, 6), (key2853, -2), (key2626, -2), (key2865, -2), (key2780, -2), (key2665, -2), (key2789, -2), (key2803, 2), (key2610, 2), (key2824, 2)]

def rawRow3128 : Integer.Sparse Key := [(key2803, -6), (key2853, 2), (key2855, 2), (key2700, 2), (key2780, 6), (key2853, -2), (key2865, -2), (key2626, -2), (key2780, -2), (key2789, -2), (key2665, -2), (key2803, 2), (key2824, 2), (key2610, 2)]

def rawRow3129 : Integer.Sparse Key := [(key2803, -6), (key2855, 2), (key2700, 2), (key2853, 2), (key2780, 6), (key2865, -2), (key2626, -2), (key2853, -2), (key2789, -2), (key2665, -2), (key2780, -2), (key2824, 2), (key2610, 2), (key2803, 2)]

def rawRow3130 : Integer.Sparse Key := [(key2803, -6), (key2855, 2), (key2853, 2), (key2700, 2), (key2780, 6), (key2865, -2), (key2853, -2), (key2626, -2), (key2789, -2), (key2780, -2), (key2665, -2), (key2824, 2), (key2803, 2), (key2610, 2)]

def rawRow3131 : Integer.Sparse Key := [(key2855, -6), (key2700, 2), (key2803, 2), (key2853, 2), (key2865, 6), (key2626, -2), (key2780, -2), (key2853, -2), (key2721, -2), (key2824, -2), (key2865, -2), (key2635, 2), (key2789, 2), (key2855, 2)]

def rawRow3132 : Integer.Sparse Key := [(key2855, -6), (key2700, 2), (key2853, 2), (key2803, 2), (key2865, 6), (key2626, -2), (key2853, -2), (key2780, -2), (key2721, -2), (key2865, -2), (key2824, -2), (key2635, 2), (key2855, 2), (key2789, 2)]

def rawRow3133 : Integer.Sparse Key := [(key2855, -6), (key2803, 2), (key2700, 2), (key2853, 2), (key2865, 6), (key2780, -2), (key2626, -2), (key2853, -2), (key2824, -2), (key2721, -2), (key2865, -2), (key2789, 2), (key2635, 2), (key2855, 2)]

def rawRow3134 : Integer.Sparse Key := [(key2855, -6), (key2803, 2), (key2853, 2), (key2700, 2), (key2865, 6), (key2780, -2), (key2853, -2), (key2626, -2), (key2824, -2), (key2865, -2), (key2721, -2), (key2789, 2), (key2855, 2), (key2635, 2)]

def rawRow3135 : Integer.Sparse Key := [(key2855, -6), (key2853, 2), (key2700, 2), (key2803, 2), (key2865, 6), (key2853, -2), (key2626, -2), (key2780, -2), (key2865, -2), (key2721, -2), (key2824, -2), (key2855, 2), (key2635, 2), (key2789, 2)]

def rawRow3136 : Integer.Sparse Key := [(key2855, -6), (key2853, 2), (key2803, 2), (key2700, 2), (key2865, 6), (key2853, -2), (key2780, -2), (key2626, -2), (key2865, -2), (key2824, -2), (key2721, -2), (key2855, 2), (key2789, 2), (key2635, 2)]

def rawRow3137 : Integer.Sparse Key := [(key2824, -6), (key2721, 2), (key2865, 2), (key2865, 2), (key2789, 6), (key2635, -2), (key2855, -2), (key2855, -2), (key2665, -2), (key2780, -2), (key2780, -2), (key2610, 2), (key2803, 2), (key2803, 2)]

def rawRow3138 : Integer.Sparse Key := [(key2824, -6), (key2865, 2), (key2721, 2), (key2865, 2), (key2789, 6), (key2855, -2), (key2635, -2), (key2855, -2), (key2780, -2), (key2665, -2), (key2780, -2), (key2803, 2), (key2610, 2), (key2803, 2)]

def rawRow3139 : Integer.Sparse Key := [(key2824, -6), (key2865, 2), (key2865, 2), (key2721, 2), (key2789, 6), (key2855, -2), (key2855, -2), (key2635, -2), (key2780, -2), (key2780, -2), (key2665, -2), (key2803, 2), (key2803, 2), (key2610, 2)]

def rawRow3140 : Integer.Sparse Key := [(key2865, -6), (key2721, 2), (key2824, 2), (key2865, 2), (key2855, 6), (key2635, -2), (key2789, -2), (key2855, -2), (key2700, -2), (key2803, -2), (key2853, -2), (key2626, 2), (key2780, 2), (key2853, 2)]

def rawRow3141 : Integer.Sparse Key := [(key2865, -6), (key2721, 2), (key2865, 2), (key2824, 2), (key2855, 6), (key2635, -2), (key2855, -2), (key2789, -2), (key2700, -2), (key2853, -2), (key2803, -2), (key2626, 2), (key2853, 2), (key2780, 2)]

def rawRow3142 : Integer.Sparse Key := [(key2865, -6), (key2824, 2), (key2721, 2), (key2865, 2), (key2855, 6), (key2789, -2), (key2635, -2), (key2855, -2), (key2803, -2), (key2700, -2), (key2853, -2), (key2780, 2), (key2626, 2), (key2853, 2)]

def rawRow3143 : Integer.Sparse Key := [(key2865, -6), (key2824, 2), (key2865, 2), (key2721, 2), (key2855, 6), (key2789, -2), (key2855, -2), (key2635, -2), (key2803, -2), (key2853, -2), (key2700, -2), (key2780, 2), (key2853, 2), (key2626, 2)]

def rawRow3144 : Integer.Sparse Key := [(key2865, -6), (key2865, 2), (key2721, 2), (key2824, 2), (key2855, 6), (key2855, -2), (key2635, -2), (key2789, -2), (key2853, -2), (key2700, -2), (key2803, -2), (key2853, 2), (key2626, 2), (key2780, 2)]

def rawRow3145 : Integer.Sparse Key := [(key2865, -6), (key2865, 2), (key2824, 2), (key2721, 2), (key2855, 6), (key2855, -2), (key2789, -2), (key2635, -2), (key2853, -2), (key2803, -2), (key2700, -2), (key2853, 2), (key2780, 2), (key2626, 2)]

def rawRow3146 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1568, -1), (key1904, -1), (key1594, -1), (key1912, -1), (key1299, 2), (key1576, 2), (key1904, 2), (key1311, 1), (key1319, 1), (key1617, 1), (key1919, 1), (key1634, 1), (key1927, 1), (key1319, -1), (key1352, -1), (key1549, -1), (key1897, -1), (key1682, -1), (key1919, -1), (key1327, -2), (key1625, -2), (key1921, -2), (key1327, 1), (key1355, 1), (key1557, 1), (key1900, 1), (key1684, 1), (key1921, 1)]

def rawRow3147 : Integer.Sparse Key := [(key1299, -1), (key1291, -1), (key1904, -1), (key1568, -1), (key1912, -1), (key1594, -1), (key1299, 2), (key1904, 2), (key1576, 2), (key1319, 1), (key1311, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1634, 1), (key1352, -1), (key1319, -1), (key1897, -1), (key1549, -1), (key1919, -1), (key1682, -1), (key1327, -2), (key1921, -2), (key1625, -2), (key1355, 1), (key1327, 1), (key1900, 1), (key1557, 1), (key1921, 1), (key1684, 1)]

def rawRow3148 : Integer.Sparse Key := [(key1568, -1), (key1594, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1576, 2), (key1299, 2), (key1904, 2), (key1617, 1), (key1634, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1919, 1), (key1549, -1), (key1682, -1), (key1319, -1), (key1919, -1), (key1352, -1), (key1897, -1), (key1625, -2), (key1327, -2), (key1921, -2), (key1557, 1), (key1684, 1), (key1327, 1), (key1921, 1), (key1355, 1), (key1900, 1)]

def rawRow3149 : Integer.Sparse Key := [(key1594, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1904, -1), (key1299, -1), (key1576, 2), (key1904, 2), (key1299, 2), (key1634, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1919, 1), (key1319, 1), (key1682, -1), (key1549, -1), (key1919, -1), (key1319, -1), (key1897, -1), (key1352, -1), (key1625, -2), (key1921, -2), (key1327, -2), (key1684, 1), (key1557, 1), (key1921, 1), (key1327, 1), (key1900, 1), (key1355, 1)]

def rawRow3150 : Integer.Sparse Key := [(key1904, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1291, -1), (key1568, -1), (key1904, 2), (key1299, 2), (key1576, 2), (key1919, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1311, 1), (key1617, 1), (key1897, -1), (key1919, -1), (key1352, -1), (key1682, -1), (key1319, -1), (key1549, -1), (key1921, -2), (key1327, -2), (key1625, -2), (key1900, 1), (key1921, 1), (key1355, 1), (key1684, 1), (key1327, 1), (key1557, 1)]

def rawRow3151 : Integer.Sparse Key := [(key1912, -1), (key1904, -1), (key1594, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1904, 2), (key1576, 2), (key1299, 2), (key1927, 1), (key1919, 1), (key1634, 1), (key1319, 1), (key1617, 1), (key1311, 1), (key1919, -1), (key1897, -1), (key1682, -1), (key1352, -1), (key1549, -1), (key1319, -1), (key1921, -2), (key1625, -2), (key1327, -2), (key1921, 1), (key1900, 1), (key1684, 1), (key1355, 1), (key1557, 1), (key1327, 1)]

def rawRow3155 : Integer.Sparse Key := [(key1311, -1), (key1319, -1), (key1617, -1), (key1919, -1), (key1634, -1), (key1927, -1), (key1327, 2), (key1625, 2), (key1921, 2), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1), (key1327, -1), (key1355, -1), (key1557, -1), (key1900, -1), (key1684, -1), (key1921, -1), (key1299, -2), (key1576, -2), (key1904, -2), (key1319, 1), (key1352, 1), (key1549, 1), (key1897, 1), (key1682, 1), (key1919, 1)]

def rawRow3156 : Integer.Sparse Key := [(key1319, -1), (key1311, -1), (key1919, -1), (key1617, -1), (key1927, -1), (key1634, -1), (key1327, 2), (key1921, 2), (key1625, 2), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1), (key1355, -1), (key1327, -1), (key1900, -1), (key1557, -1), (key1921, -1), (key1684, -1), (key1299, -2), (key1904, -2), (key1576, -2), (key1352, 1), (key1319, 1), (key1897, 1), (key1549, 1), (key1919, 1), (key1682, 1)]

def rawRow3157 : Integer.Sparse Key := [(key1617, -1), (key1634, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1625, 2), (key1327, 2), (key1921, 2), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1), (key1557, -1), (key1684, -1), (key1327, -1), (key1921, -1), (key1355, -1), (key1900, -1), (key1576, -2), (key1299, -2), (key1904, -2), (key1549, 1), (key1682, 1), (key1319, 1), (key1919, 1), (key1352, 1), (key1897, 1)]

def rawRow3158 : Integer.Sparse Key := [(key1634, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1919, -1), (key1319, -1), (key1625, 2), (key1921, 2), (key1327, 2), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1), (key1684, -1), (key1557, -1), (key1921, -1), (key1327, -1), (key1900, -1), (key1355, -1), (key1576, -2), (key1904, -2), (key1299, -2), (key1682, 1), (key1549, 1), (key1919, 1), (key1319, 1), (key1897, 1), (key1352, 1)]

def rawRow3159 : Integer.Sparse Key := [(key1919, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1311, -1), (key1617, -1), (key1921, 2), (key1327, 2), (key1625, 2), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1), (key1900, -1), (key1921, -1), (key1355, -1), (key1684, -1), (key1327, -1), (key1557, -1), (key1904, -2), (key1299, -2), (key1576, -2), (key1897, 1), (key1919, 1), (key1352, 1), (key1682, 1), (key1319, 1), (key1549, 1)]

def rawRow3160 : Integer.Sparse Key := [(key1927, -1), (key1919, -1), (key1634, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1921, 2), (key1625, 2), (key1327, 2), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1), (key1921, -1), (key1900, -1), (key1684, -1), (key1355, -1), (key1557, -1), (key1327, -1), (key1904, -2), (key1576, -2), (key1299, -2), (key1919, 1), (key1897, 1), (key1682, 1), (key1352, 1), (key1549, 1), (key1319, 1)]

def rawRow3161 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1427, -1), (key1625, -1), (key1445, -1), (key1634, -1), (key1311, 2), (key1419, 2), (key1617, 2), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1), (key1291, -1), (key1311, -1), (key1386, -1), (key1541, -1), (key1419, -1), (key1568, -1), (key1352, -2), (key1473, -2), (key1682, -2), (key1299, 1), (key1319, 1), (key1394, 1), (key1549, 1), (key1427, 1), (key1576, 1)]

def rawRow3162 : Integer.Sparse Key := [(key1327, -1), (key1319, -1), (key1625, -1), (key1427, -1), (key1634, -1), (key1445, -1), (key1311, 2), (key1617, 2), (key1419, 2), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1), (key1311, -1), (key1291, -1), (key1541, -1), (key1386, -1), (key1568, -1), (key1419, -1), (key1352, -2), (key1682, -2), (key1473, -2), (key1319, 1), (key1299, 1), (key1549, 1), (key1394, 1), (key1576, 1), (key1427, 1)]

def rawRow3163 : Integer.Sparse Key := [(key1427, -1), (key1445, -1), (key1319, -1), (key1634, -1), (key1327, -1), (key1625, -1), (key1419, 2), (key1311, 2), (key1617, 2), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1), (key1386, -1), (key1419, -1), (key1291, -1), (key1568, -1), (key1311, -1), (key1541, -1), (key1473, -2), (key1352, -2), (key1682, -2), (key1394, 1), (key1427, 1), (key1299, 1), (key1576, 1), (key1319, 1), (key1549, 1)]

def rawRow3164 : Integer.Sparse Key := [(key1445, -1), (key1427, -1), (key1634, -1), (key1319, -1), (key1625, -1), (key1327, -1), (key1419, 2), (key1617, 2), (key1311, 2), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1), (key1419, -1), (key1386, -1), (key1568, -1), (key1291, -1), (key1541, -1), (key1311, -1), (key1473, -2), (key1682, -2), (key1352, -2), (key1427, 1), (key1394, 1), (key1576, 1), (key1299, 1), (key1549, 1), (key1319, 1)]

def rawRow3165 : Integer.Sparse Key := [(key1625, -1), (key1634, -1), (key1327, -1), (key1445, -1), (key1319, -1), (key1427, -1), (key1617, 2), (key1311, 2), (key1419, 2), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1), (key1541, -1), (key1568, -1), (key1311, -1), (key1419, -1), (key1291, -1), (key1386, -1), (key1682, -2), (key1352, -2), (key1473, -2), (key1549, 1), (key1576, 1), (key1319, 1), (key1427, 1), (key1299, 1), (key1394, 1)]

def rawRow3166 : Integer.Sparse Key := [(key1634, -1), (key1625, -1), (key1445, -1), (key1327, -1), (key1427, -1), (key1319, -1), (key1617, 2), (key1419, 2), (key1311, 2), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1), (key1568, -1), (key1541, -1), (key1419, -1), (key1311, -1), (key1386, -1), (key1291, -1), (key1682, -2), (key1473, -2), (key1352, -2), (key1576, 1), (key1549, 1), (key1427, 1), (key1319, 1), (key1394, 1), (key1299, 1)]

def rawRow3170 : Integer.Sparse Key := [(key1352, -1), (key1355, -1), (key1473, -1), (key1684, -1), (key1481, -1), (key1690, -1), (key1352, 2), (key1473, 2), (key1682, 2), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1), (key1299, -1), (key1319, -1), (key1394, -1), (key1549, -1), (key1427, -1), (key1576, -1), (key1311, -2), (key1419, -2), (key1617, -2), (key1291, 1), (key1311, 1), (key1386, 1), (key1541, 1), (key1419, 1), (key1568, 1)]

def rawRow3171 : Integer.Sparse Key := [(key1355, -1), (key1352, -1), (key1684, -1), (key1473, -1), (key1690, -1), (key1481, -1), (key1352, 2), (key1682, 2), (key1473, 2), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1), (key1319, -1), (key1299, -1), (key1549, -1), (key1394, -1), (key1576, -1), (key1427, -1), (key1311, -2), (key1617, -2), (key1419, -2), (key1311, 1), (key1291, 1), (key1541, 1), (key1386, 1), (key1568, 1), (key1419, 1)]

def rawRow3172 : Integer.Sparse Key := [(key1473, -1), (key1481, -1), (key1352, -1), (key1690, -1), (key1355, -1), (key1684, -1), (key1473, 2), (key1352, 2), (key1682, 2), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1), (key1394, -1), (key1427, -1), (key1299, -1), (key1576, -1), (key1319, -1), (key1549, -1), (key1419, -2), (key1311, -2), (key1617, -2), (key1386, 1), (key1419, 1), (key1291, 1), (key1568, 1), (key1311, 1), (key1541, 1)]

def rawRow3173 : Integer.Sparse Key := [(key1481, -1), (key1473, -1), (key1690, -1), (key1352, -1), (key1684, -1), (key1355, -1), (key1473, 2), (key1682, 2), (key1352, 2), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1), (key1427, -1), (key1394, -1), (key1576, -1), (key1299, -1), (key1549, -1), (key1319, -1), (key1419, -2), (key1617, -2), (key1311, -2), (key1419, 1), (key1386, 1), (key1568, 1), (key1291, 1), (key1541, 1), (key1311, 1)]

def rawRow3174 : Integer.Sparse Key := [(key1684, -1), (key1690, -1), (key1355, -1), (key1481, -1), (key1352, -1), (key1473, -1), (key1682, 2), (key1352, 2), (key1473, 2), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1), (key1549, -1), (key1576, -1), (key1319, -1), (key1427, -1), (key1299, -1), (key1394, -1), (key1617, -2), (key1311, -2), (key1419, -2), (key1541, 1), (key1568, 1), (key1311, 1), (key1419, 1), (key1291, 1), (key1386, 1)]

def rawRow3175 : Integer.Sparse Key := [(key1690, -1), (key1684, -1), (key1481, -1), (key1355, -1), (key1473, -1), (key1352, -1), (key1682, 2), (key1473, 2), (key1352, 2), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1), (key1576, -1), (key1549, -1), (key1427, -1), (key1319, -1), (key1394, -1), (key1299, -1), (key1617, -2), (key1419, -2), (key1311, -2), (key1568, 1), (key1541, 1), (key1419, 1), (key1311, 1), (key1386, 1), (key1291, 1)]

def rawRow3176 : Integer.Sparse Key := [(key2679, -2), (key2691, -2), (key3014, -2), (key2684, 2), (key2691, 2), (key2820, 2), (key2710, 2), (key2717, 2), (key3024, 2), (key2717, -6), (key2754, -2), (key2755, -2), (key2921, -2), (key2755, 6)]

def rawRow3177 : Integer.Sparse Key := [(key2691, -2), (key2679, -2), (key3014, -2), (key2691, 2), (key2684, 2), (key2820, 2), (key2717, 2), (key2710, 2), (key3024, 2), (key2717, -6), (key2755, -2), (key2754, -2), (key2921, -2), (key2755, 6)]

def rawRow3178 : Integer.Sparse Key := [(key3047, -2), (key3115, -2), (key2691, -2), (key2684, 2), (key2820, 2), (key2691, 2), (key2710, 2), (key3024, 2), (key2717, 2), (key2717, -6), (key2754, -2), (key2921, -2), (key2755, -2), (key2755, 6)]

def rawRow3179 : Integer.Sparse Key := [(key3115, -2), (key3047, -2), (key2691, -2), (key2820, 2), (key2684, 2), (key2691, 2), (key3024, 2), (key2710, 2), (key2717, 2), (key2717, -6), (key2921, -2), (key2754, -2), (key2755, -2), (key2755, 6)]

def rawRow3180 : Integer.Sparse Key := [(key3058, -2), (key3115, -2), (key2679, -2), (key2691, 2), (key2820, 2), (key2684, 2), (key2717, 2), (key3024, 2), (key2710, 2), (key2717, -6), (key2755, -2), (key2921, -2), (key2754, -2), (key2755, 6)]

def rawRow3181 : Integer.Sparse Key := [(key3115, -2), (key3058, -2), (key3047, -2), (key2820, 2), (key2691, 2), (key2684, 2), (key3024, 2), (key2717, 2), (key2710, 2), (key2717, -6), (key2921, -2), (key2755, -2), (key2754, -2), (key2755, 6)]

def rawRow3182 : Integer.Sparse Key := [(key3053, -2), (key3053, -2), (key3105, -2), (key2679, 2), (key2679, 2), (key2813, 2), (key2717, 2), (key2717, 2), (key3024, 2), (key2710, -6), (key2755, -2), (key2755, -2), (key2921, -2), (key2754, 6)]

def rawRow3183 : Integer.Sparse Key := [(key3053, -2), (key3105, -2), (key3053, -2), (key3047, 2), (key3096, 2), (key2679, 2), (key2717, 2), (key3024, 2), (key2717, 2), (key2710, -6), (key2755, -2), (key2921, -2), (key2755, -2), (key2754, 6)]

def rawRow3184 : Integer.Sparse Key := [(key3105, -2), (key3053, -2), (key3053, -2), (key3096, 2), (key3047, 2), (key3047, 2), (key3024, 2), (key2717, 2), (key2717, 2), (key2710, -6), (key2921, -2), (key2755, -2), (key2755, -2), (key2754, 6)]

def rawRow3185 : Integer.Sparse Key := [(key3061, -2), (key3075, -2), (key3143, -2), (key3068, 2), (key3076, 2), (key3142, 2), (key2679, 2), (key2691, 2), (key3014, 2), (key2755, -6), (key2684, -2), (key2691, -2), (key2820, -2), (key2717, 6)]

def rawRow3186 : Integer.Sparse Key := [(key3075, -2), (key3061, -2), (key3143, -2), (key3076, 2), (key3068, 2), (key3142, 2), (key2691, 2), (key2679, 2), (key3014, 2), (key2755, -6), (key2691, -2), (key2684, -2), (key2820, -2), (key2717, 6)]

def rawRow3187 : Integer.Sparse Key := [(key3061, -2), (key3143, -2), (key3075, -2), (key3068, 2), (key3142, 2), (key3076, 2), (key3047, 2), (key3115, 2), (key2691, 2), (key2755, -6), (key2684, -2), (key2820, -2), (key2691, -2), (key2717, 6)]

def rawRow3188 : Integer.Sparse Key := [(key3143, -2), (key3061, -2), (key3075, -2), (key3142, 2), (key3068, 2), (key3076, 2), (key3115, 2), (key3047, 2), (key2691, 2), (key2755, -6), (key2820, -2), (key2684, -2), (key2691, -2), (key2717, 6)]

def rawRow3189 : Integer.Sparse Key := [(key3075, -2), (key3143, -2), (key3061, -2), (key3076, 2), (key3142, 2), (key3068, 2), (key3058, 2), (key3115, 2), (key2679, 2), (key2755, -6), (key2691, -2), (key2820, -2), (key2684, -2), (key2717, 6)]

def rawRow3190 : Integer.Sparse Key := [(key3143, -2), (key3075, -2), (key3061, -2), (key3142, 2), (key3076, 2), (key3068, 2), (key3115, 2), (key3058, 2), (key3047, 2), (key2755, -6), (key2820, -2), (key2691, -2), (key2684, -2), (key2717, 6)]

def rawRow3191 : Integer.Sparse Key := [(key3053, -2), (key3068, -2), (key3105, -2), (key3047, 2), (key3061, 2), (key3096, 2), (key3058, 2), (key3076, 2), (key3115, 2), (key2679, -6), (key2691, -2), (key2717, -2), (key2820, -2), (key2684, 6)]

def rawRow3192 : Integer.Sparse Key := [(key3068, -2), (key3053, -2), (key3105, -2), (key3061, 2), (key3047, 2), (key3096, 2), (key3076, 2), (key3058, 2), (key3115, 2), (key2679, -6), (key2717, -2), (key2691, -2), (key2820, -2), (key2684, 6)]

def rawRow3193 : Integer.Sparse Key := [(key3053, -2), (key3105, -2), (key3068, -2), (key3047, 2), (key3096, 2), (key3061, 2), (key3058, 2), (key3115, 2), (key3076, 2), (key2679, -6), (key2691, -2), (key2820, -2), (key2717, -2), (key2684, 6)]

def rawRow3194 : Integer.Sparse Key := [(key3105, -2), (key3053, -2), (key3068, -2), (key3096, 2), (key3047, 2), (key3061, 2), (key3115, 2), (key3058, 2), (key3076, 2), (key3047, -6), (key2820, -2), (key2691, -2), (key2717, -2), (key2684, 6)]

def rawRow3195 : Integer.Sparse Key := [(key3068, -2), (key3105, -2), (key3053, -2), (key3061, 2), (key3096, 2), (key3047, 2), (key3076, 2), (key3115, 2), (key3058, 2), (key3047, -6), (key2717, -2), (key2820, -2), (key2691, -2), (key2684, 6)]

def rawRow3196 : Integer.Sparse Key := [(key3105, -2), (key3068, -2), (key3053, -2), (key3096, 2), (key3061, 2), (key3047, 2), (key3115, 2), (key3076, 2), (key3058, 2), (key3047, -6), (key2820, -2), (key2717, -2), (key2691, -2), (key2684, 6)]

def rawRow3197 : Integer.Sparse Key := [(key3075, -2), (key3075, -2), (key3143, -2), (key3076, 2), (key3076, 2), (key3142, 2), (key3053, 2), (key3053, 2), (key3105, 2), (key3068, -6), (key2679, -2), (key2679, -2), (key2813, -2), (key2710, 6)]

def rawRow3198 : Integer.Sparse Key := [(key3075, -2), (key3143, -2), (key3075, -2), (key3076, 2), (key3142, 2), (key3076, 2), (key3053, 2), (key3105, 2), (key3053, 2), (key3068, -6), (key3047, -2), (key3096, -2), (key2679, -2), (key2710, 6)]

def rawRow3199 : Integer.Sparse Key := [(key3143, -2), (key3075, -2), (key3075, -2), (key3142, 2), (key3076, 2), (key3076, 2), (key3105, 2), (key3053, 2), (key3053, 2), (key3068, -6), (key3096, -2), (key3047, -2), (key3047, -2), (key2710, 6)]

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

def rawRow3200 : Integer.Sparse Key := [(key3058, -2), (key3076, -2), (key3115, -2), (key3058, 2), (key3075, 2), (key3113, 2), (key3053, 2), (key3068, 2), (key3105, 2), (key3053, -6), (key3047, -2), (key3061, -2), (key3096, -2), (key2679, 6)]

def rawRow3201 : Integer.Sparse Key := [(key3076, -2), (key3058, -2), (key3115, -2), (key3075, 2), (key3058, 2), (key3113, 2), (key3068, 2), (key3053, 2), (key3105, 2), (key3053, -6), (key3061, -2), (key3047, -2), (key3096, -2), (key2679, 6)]

def rawRow3202 : Integer.Sparse Key := [(key3058, -2), (key3115, -2), (key3076, -2), (key3058, 2), (key3113, 2), (key3075, 2), (key3053, 2), (key3105, 2), (key3068, 2), (key3053, -6), (key3047, -2), (key3096, -2), (key3061, -2), (key2679, 6)]

def rawRow3203 : Integer.Sparse Key := [(key3115, -2), (key3058, -2), (key3076, -2), (key3113, 2), (key3058, 2), (key3075, 2), (key3105, 2), (key3053, 2), (key3068, 2), (key3053, -6), (key3096, -2), (key3047, -2), (key3061, -2), (key3047, 6)]

def rawRow3204 : Integer.Sparse Key := [(key3076, -2), (key3115, -2), (key3058, -2), (key3075, 2), (key3113, 2), (key3058, 2), (key3068, 2), (key3105, 2), (key3053, 2), (key3053, -6), (key3061, -2), (key3096, -2), (key3047, -2), (key3047, 6)]

def rawRow3205 : Integer.Sparse Key := [(key3115, -2), (key3076, -2), (key3058, -2), (key3113, 2), (key3075, 2), (key3058, 2), (key3105, 2), (key3068, 2), (key3053, 2), (key3053, -6), (key3096, -2), (key3061, -2), (key3047, -2), (key3047, 6)]

def rawRow3206 : Integer.Sparse Key := [(key1419, -2), (key1427, -2), (key1445, -2), (key1386, 1), (key1394, 1), (key1419, 1), (key1473, 1), (key1445, 1), (key1481, 1), (key1568, 2), (key1576, 2), (key1594, 2), (key1291, -1), (key1299, -1), (key1568, -1), (key1904, -1), (key1594, -1), (key1912, -1), (key1541, -1), (key1549, -1), (key1617, -1), (key1682, -1), (key1634, -1), (key1690, -1), (key1311, 1), (key1319, 1), (key1617, 1), (key1919, 1), (key1634, 1), (key1927, 1)]

def rawRow3207 : Integer.Sparse Key := [(key1427, -2), (key1419, -2), (key1445, -2), (key1394, 1), (key1386, 1), (key1473, 1), (key1419, 1), (key1481, 1), (key1445, 1), (key1576, 2), (key1568, 2), (key1594, 2), (key1299, -1), (key1291, -1), (key1904, -1), (key1568, -1), (key1912, -1), (key1594, -1), (key1549, -1), (key1541, -1), (key1682, -1), (key1617, -1), (key1690, -1), (key1634, -1), (key1319, 1), (key1311, 1), (key1919, 1), (key1617, 1), (key1927, 1), (key1634, 1)]

def rawRow3208 : Integer.Sparse Key := [(key1419, -2), (key1445, -2), (key1427, -2), (key1419, 1), (key1445, 1), (key1386, 1), (key1481, 1), (key1394, 1), (key1473, 1), (key1568, 2), (key1594, 2), (key1576, 2), (key1568, -1), (key1594, -1), (key1291, -1), (key1912, -1), (key1299, -1), (key1904, -1), (key1617, -1), (key1634, -1), (key1541, -1), (key1690, -1), (key1549, -1), (key1682, -1), (key1617, 1), (key1634, 1), (key1311, 1), (key1927, 1), (key1319, 1), (key1919, 1)]

def rawRow3209 : Integer.Sparse Key := [(key1445, -2), (key1419, -2), (key1427, -2), (key1445, 1), (key1419, 1), (key1481, 1), (key1386, 1), (key1473, 1), (key1394, 1), (key1594, 2), (key1568, 2), (key1576, 2), (key1594, -1), (key1568, -1), (key1912, -1), (key1291, -1), (key1904, -1), (key1299, -1), (key1634, -1), (key1617, -1), (key1690, -1), (key1541, -1), (key1682, -1), (key1549, -1), (key1634, 1), (key1617, 1), (key1927, 1), (key1311, 1), (key1919, 1), (key1319, 1)]

def rawRow3210 : Integer.Sparse Key := [(key1427, -2), (key1445, -2), (key1419, -2), (key1473, 1), (key1481, 1), (key1394, 1), (key1445, 1), (key1386, 1), (key1419, 1), (key1576, 2), (key1594, 2), (key1568, 2), (key1904, -1), (key1912, -1), (key1299, -1), (key1594, -1), (key1291, -1), (key1568, -1), (key1682, -1), (key1690, -1), (key1549, -1), (key1634, -1), (key1541, -1), (key1617, -1), (key1919, 1), (key1927, 1), (key1319, 1), (key1634, 1), (key1311, 1), (key1617, 1)]

def rawRow3211 : Integer.Sparse Key := [(key1445, -2), (key1427, -2), (key1419, -2), (key1481, 1), (key1473, 1), (key1445, 1), (key1394, 1), (key1419, 1), (key1386, 1), (key1594, 2), (key1576, 2), (key1568, 2), (key1912, -1), (key1904, -1), (key1594, -1), (key1299, -1), (key1568, -1), (key1291, -1), (key1690, -1), (key1682, -1), (key1634, -1), (key1549, -1), (key1617, -1), (key1541, -1), (key1927, 1), (key1919, 1), (key1634, 1), (key1319, 1), (key1617, 1), (key1311, 1)]

def rawRow3215 : Integer.Sparse Key := [(key1568, -2), (key1576, -2), (key1594, -2), (key1541, 1), (key1549, 1), (key1617, 1), (key1682, 1), (key1634, 1), (key1690, 1), (key1419, 2), (key1427, 2), (key1445, 2), (key1311, -1), (key1319, -1), (key1617, -1), (key1919, -1), (key1634, -1), (key1927, -1), (key1386, -1), (key1394, -1), (key1419, -1), (key1473, -1), (key1445, -1), (key1481, -1), (key1291, 1), (key1299, 1), (key1568, 1), (key1904, 1), (key1594, 1), (key1912, 1)]

def rawRow3216 : Integer.Sparse Key := [(key1576, -2), (key1568, -2), (key1594, -2), (key1549, 1), (key1541, 1), (key1682, 1), (key1617, 1), (key1690, 1), (key1634, 1), (key1427, 2), (key1419, 2), (key1445, 2), (key1319, -1), (key1311, -1), (key1919, -1), (key1617, -1), (key1927, -1), (key1634, -1), (key1394, -1), (key1386, -1), (key1473, -1), (key1419, -1), (key1481, -1), (key1445, -1), (key1299, 1), (key1291, 1), (key1904, 1), (key1568, 1), (key1912, 1), (key1594, 1)]

def rawRow3217 : Integer.Sparse Key := [(key1568, -2), (key1594, -2), (key1576, -2), (key1617, 1), (key1634, 1), (key1541, 1), (key1690, 1), (key1549, 1), (key1682, 1), (key1419, 2), (key1445, 2), (key1427, 2), (key1617, -1), (key1634, -1), (key1311, -1), (key1927, -1), (key1319, -1), (key1919, -1), (key1419, -1), (key1445, -1), (key1386, -1), (key1481, -1), (key1394, -1), (key1473, -1), (key1568, 1), (key1594, 1), (key1291, 1), (key1912, 1), (key1299, 1), (key1904, 1)]

def rawRow3218 : Integer.Sparse Key := [(key1594, -2), (key1568, -2), (key1576, -2), (key1634, 1), (key1617, 1), (key1690, 1), (key1541, 1), (key1682, 1), (key1549, 1), (key1445, 2), (key1419, 2), (key1427, 2), (key1634, -1), (key1617, -1), (key1927, -1), (key1311, -1), (key1919, -1), (key1319, -1), (key1445, -1), (key1419, -1), (key1481, -1), (key1386, -1), (key1473, -1), (key1394, -1), (key1594, 1), (key1568, 1), (key1912, 1), (key1291, 1), (key1904, 1), (key1299, 1)]

def rawRow3219 : Integer.Sparse Key := [(key1576, -2), (key1594, -2), (key1568, -2), (key1682, 1), (key1690, 1), (key1549, 1), (key1634, 1), (key1541, 1), (key1617, 1), (key1427, 2), (key1445, 2), (key1419, 2), (key1919, -1), (key1927, -1), (key1319, -1), (key1634, -1), (key1311, -1), (key1617, -1), (key1473, -1), (key1481, -1), (key1394, -1), (key1445, -1), (key1386, -1), (key1419, -1), (key1904, 1), (key1912, 1), (key1299, 1), (key1594, 1), (key1291, 1), (key1568, 1)]

def rawRow3220 : Integer.Sparse Key := [(key1594, -2), (key1576, -2), (key1568, -2), (key1690, 1), (key1682, 1), (key1634, 1), (key1549, 1), (key1617, 1), (key1541, 1), (key1445, 2), (key1427, 2), (key1419, 2), (key1927, -1), (key1919, -1), (key1634, -1), (key1319, -1), (key1617, -1), (key1311, -1), (key1481, -1), (key1473, -1), (key1445, -1), (key1394, -1), (key1419, -1), (key1386, -1), (key1912, 1), (key1904, 1), (key1594, 1), (key1299, 1), (key1568, 1), (key1291, 1)]

def rawRow3221 : Integer.Sparse Key := [(key1682, -2), (key1684, -2), (key1690, -2), (key1549, 1), (key1557, 1), (key1576, 1), (key1625, 1), (key1594, 1), (key1634, 1), (key1919, 2), (key1921, 2), (key1927, 2), (key1319, -1), (key1327, -1), (key1427, -1), (key1625, -1), (key1445, -1), (key1634, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1921, -1), (key1912, -1), (key1927, -1), (key1352, 1), (key1355, 1), (key1473, 1), (key1684, 1), (key1481, 1), (key1690, 1)]

def rawRow3222 : Integer.Sparse Key := [(key1684, -2), (key1682, -2), (key1690, -2), (key1557, 1), (key1549, 1), (key1625, 1), (key1576, 1), (key1634, 1), (key1594, 1), (key1921, 2), (key1919, 2), (key1927, 2), (key1327, -1), (key1319, -1), (key1625, -1), (key1427, -1), (key1634, -1), (key1445, -1), (key1900, -1), (key1897, -1), (key1921, -1), (key1904, -1), (key1927, -1), (key1912, -1), (key1355, 1), (key1352, 1), (key1684, 1), (key1473, 1), (key1690, 1), (key1481, 1)]

def rawRow3223 : Integer.Sparse Key := [(key1682, -2), (key1690, -2), (key1684, -2), (key1576, 1), (key1594, 1), (key1549, 1), (key1634, 1), (key1557, 1), (key1625, 1), (key1919, 2), (key1927, 2), (key1921, 2), (key1427, -1), (key1445, -1), (key1319, -1), (key1634, -1), (key1327, -1), (key1625, -1), (key1904, -1), (key1912, -1), (key1897, -1), (key1927, -1), (key1900, -1), (key1921, -1), (key1473, 1), (key1481, 1), (key1352, 1), (key1690, 1), (key1355, 1), (key1684, 1)]

def rawRow3224 : Integer.Sparse Key := [(key1690, -2), (key1682, -2), (key1684, -2), (key1594, 1), (key1576, 1), (key1634, 1), (key1549, 1), (key1625, 1), (key1557, 1), (key1927, 2), (key1919, 2), (key1921, 2), (key1445, -1), (key1427, -1), (key1634, -1), (key1319, -1), (key1625, -1), (key1327, -1), (key1912, -1), (key1904, -1), (key1927, -1), (key1897, -1), (key1921, -1), (key1900, -1), (key1481, 1), (key1473, 1), (key1690, 1), (key1352, 1), (key1684, 1), (key1355, 1)]

def rawRow3225 : Integer.Sparse Key := [(key1684, -2), (key1690, -2), (key1682, -2), (key1625, 1), (key1634, 1), (key1557, 1), (key1594, 1), (key1549, 1), (key1576, 1), (key1921, 2), (key1927, 2), (key1919, 2), (key1625, -1), (key1634, -1), (key1327, -1), (key1445, -1), (key1319, -1), (key1427, -1), (key1921, -1), (key1927, -1), (key1900, -1), (key1912, -1), (key1897, -1), (key1904, -1), (key1684, 1), (key1690, 1), (key1355, 1), (key1481, 1), (key1352, 1), (key1473, 1)]

def rawRow3226 : Integer.Sparse Key := [(key1690, -2), (key1684, -2), (key1682, -2), (key1634, 1), (key1625, 1), (key1594, 1), (key1557, 1), (key1576, 1), (key1549, 1), (key1927, 2), (key1921, 2), (key1919, 2), (key1634, -1), (key1625, -1), (key1445, -1), (key1327, -1), (key1427, -1), (key1319, -1), (key1927, -1), (key1921, -1), (key1912, -1), (key1900, -1), (key1904, -1), (key1897, -1), (key1690, 1), (key1684, 1), (key1481, 1), (key1355, 1), (key1473, 1), (key1352, 1)]

def rawRow3230 : Integer.Sparse Key := [(key1919, -2), (key1921, -2), (key1927, -2), (key1897, 1), (key1900, 1), (key1904, 1), (key1921, 1), (key1912, 1), (key1927, 1), (key1682, 2), (key1684, 2), (key1690, 2), (key1352, -1), (key1355, -1), (key1473, -1), (key1684, -1), (key1481, -1), (key1690, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1625, -1), (key1594, -1), (key1634, -1), (key1319, 1), (key1327, 1), (key1427, 1), (key1625, 1), (key1445, 1), (key1634, 1)]

def rawRow3231 : Integer.Sparse Key := [(key1921, -2), (key1919, -2), (key1927, -2), (key1900, 1), (key1897, 1), (key1921, 1), (key1904, 1), (key1927, 1), (key1912, 1), (key1684, 2), (key1682, 2), (key1690, 2), (key1355, -1), (key1352, -1), (key1684, -1), (key1473, -1), (key1690, -1), (key1481, -1), (key1557, -1), (key1549, -1), (key1625, -1), (key1576, -1), (key1634, -1), (key1594, -1), (key1327, 1), (key1319, 1), (key1625, 1), (key1427, 1), (key1634, 1), (key1445, 1)]

def rawRow3232 : Integer.Sparse Key := [(key1919, -2), (key1927, -2), (key1921, -2), (key1904, 1), (key1912, 1), (key1897, 1), (key1927, 1), (key1900, 1), (key1921, 1), (key1682, 2), (key1690, 2), (key1684, 2), (key1473, -1), (key1481, -1), (key1352, -1), (key1690, -1), (key1355, -1), (key1684, -1), (key1576, -1), (key1594, -1), (key1549, -1), (key1634, -1), (key1557, -1), (key1625, -1), (key1427, 1), (key1445, 1), (key1319, 1), (key1634, 1), (key1327, 1), (key1625, 1)]

def rawRow3233 : Integer.Sparse Key := [(key1927, -2), (key1919, -2), (key1921, -2), (key1912, 1), (key1904, 1), (key1927, 1), (key1897, 1), (key1921, 1), (key1900, 1), (key1690, 2), (key1682, 2), (key1684, 2), (key1481, -1), (key1473, -1), (key1690, -1), (key1352, -1), (key1684, -1), (key1355, -1), (key1594, -1), (key1576, -1), (key1634, -1), (key1549, -1), (key1625, -1), (key1557, -1), (key1445, 1), (key1427, 1), (key1634, 1), (key1319, 1), (key1625, 1), (key1327, 1)]

def rawRow3234 : Integer.Sparse Key := [(key1921, -2), (key1927, -2), (key1919, -2), (key1921, 1), (key1927, 1), (key1900, 1), (key1912, 1), (key1897, 1), (key1904, 1), (key1684, 2), (key1690, 2), (key1682, 2), (key1684, -1), (key1690, -1), (key1355, -1), (key1481, -1), (key1352, -1), (key1473, -1), (key1625, -1), (key1634, -1), (key1557, -1), (key1594, -1), (key1549, -1), (key1576, -1), (key1625, 1), (key1634, 1), (key1327, 1), (key1445, 1), (key1319, 1), (key1427, 1)]

def rawRow3235 : Integer.Sparse Key := [(key1927, -2), (key1921, -2), (key1919, -2), (key1927, 1), (key1921, 1), (key1912, 1), (key1900, 1), (key1904, 1), (key1897, 1), (key1690, 2), (key1684, 2), (key1682, 2), (key1690, -1), (key1684, -1), (key1481, -1), (key1355, -1), (key1473, -1), (key1352, -1), (key1634, -1), (key1625, -1), (key1594, -1), (key1557, -1), (key1576, -1), (key1549, -1), (key1634, 1), (key1625, 1), (key1445, 1), (key1327, 1), (key1427, 1), (key1319, 1)]

def rawRow3236 : Integer.Sparse Key := [(key1029, -2), (key1035, -2), (key1070, -2), (key1035, 6), (key1107, 2), (key1113, 2), (key1149, 2), (key1000, -2), (key1113, -2), (key1231, -2), (key1122, -6), (key1014, 2), (key1122, 2), (key1234, 2)]

def rawRow3237 : Integer.Sparse Key := [(key1035, -2), (key1029, -2), (key1070, -2), (key1035, 6), (key1113, 2), (key1107, 2), (key1149, 2), (key1000, -2), (key1231, -2), (key1113, -2), (key1122, -6), (key1014, 2), (key1234, 2), (key1122, 2)]

def rawRow3238 : Integer.Sparse Key := [(key1029, -2), (key1070, -2), (key1035, -2), (key1035, 6), (key1107, 2), (key1149, 2), (key1113, 2), (key1113, -2), (key1000, -2), (key1231, -2), (key1122, -6), (key1122, 2), (key1014, 2), (key1234, 2)]

def rawRow3239 : Integer.Sparse Key := [(key1070, -2), (key1029, -2), (key1035, -2), (key1035, 6), (key1149, 2), (key1107, 2), (key1113, 2), (key1113, -2), (key1231, -2), (key1000, -2), (key1122, -6), (key1122, 2), (key1234, 2), (key1014, 2)]

def rawRow3240 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1029, -2), (key1035, 6), (key1113, 2), (key1149, 2), (key1107, 2), (key1231, -2), (key1000, -2), (key1113, -2), (key1122, -6), (key1234, 2), (key1014, 2), (key1122, 2)]

def rawRow3241 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1029, -2), (key1035, 6), (key1149, 2), (key1113, 2), (key1107, 2), (key1231, -2), (key1113, -2), (key1000, -2), (key1122, -6), (key1234, 2), (key1122, 2), (key1014, 2)]

def rawRow3242 : Integer.Sparse Key := [(key1035, -2), (key1035, -2), (key1070, -2), (key1029, 6), (key1231, 2), (key1231, 2), (key1241, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1234, -6), (key1014, 2), (key1122, 2), (key1122, 2)]

def rawRow3243 : Integer.Sparse Key := [(key1035, -2), (key1070, -2), (key1035, -2), (key1029, 6), (key1231, 2), (key1241, 2), (key1231, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1234, -6), (key1122, 2), (key1014, 2), (key1122, 2)]

def rawRow3244 : Integer.Sparse Key := [(key1070, -2), (key1035, -2), (key1035, -2), (key1029, 6), (key1241, 2), (key1231, 2), (key1231, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1234, -6), (key1122, 2), (key1122, 2), (key1014, 2)]

def rawRow3245 : Integer.Sparse Key := [(key1107, -2), (key1113, -2), (key1149, -2), (key1122, 6), (key1029, 2), (key1035, 2), (key1070, 2), (key1014, -2), (key1122, -2), (key1234, -2), (key1035, -6), (key1000, 2), (key1113, 2), (key1231, 2)]

def rawRow3246 : Integer.Sparse Key := [(key1113, -2), (key1107, -2), (key1149, -2), (key1122, 6), (key1035, 2), (key1029, 2), (key1070, 2), (key1014, -2), (key1234, -2), (key1122, -2), (key1035, -6), (key1000, 2), (key1231, 2), (key1113, 2)]

def rawRow3247 : Integer.Sparse Key := [(key1107, -2), (key1149, -2), (key1113, -2), (key1122, 6), (key1029, 2), (key1070, 2), (key1035, 2), (key1122, -2), (key1014, -2), (key1234, -2), (key1035, -6), (key1113, 2), (key1000, 2), (key1231, 2)]

def rawRow3248 : Integer.Sparse Key := [(key1149, -2), (key1107, -2), (key1113, -2), (key1122, 6), (key1070, 2), (key1029, 2), (key1035, 2), (key1122, -2), (key1234, -2), (key1014, -2), (key1035, -6), (key1113, 2), (key1231, 2), (key1000, 2)]

def rawRow3249 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1107, -2), (key1122, 6), (key1035, 2), (key1070, 2), (key1029, 2), (key1234, -2), (key1014, -2), (key1122, -2), (key1035, -6), (key1231, 2), (key1000, 2), (key1113, 2)]

def rawRow3250 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1107, -2), (key1122, 6), (key1070, 2), (key1035, 2), (key1029, 2), (key1234, -2), (key1122, -2), (key1014, -2), (key1035, -6), (key1231, 2), (key1113, 2), (key1000, 2)]

def rawRow3251 : Integer.Sparse Key := [(key1113, -2), (key1122, -2), (key1149, -2), (key1107, 6), (key1231, 2), (key1234, 2), (key1241, 2), (key994, -2), (key1029, -2), (key1107, -2), (key1231, -6), (key1000, 2), (key1035, 2), (key1113, 2)]

def rawRow3252 : Integer.Sparse Key := [(key1122, -2), (key1113, -2), (key1149, -2), (key1107, 6), (key1234, 2), (key1231, 2), (key1241, 2), (key994, -2), (key1107, -2), (key1029, -2), (key1231, -6), (key1000, 2), (key1113, 2), (key1035, 2)]

def rawRow3253 : Integer.Sparse Key := [(key1113, -2), (key1149, -2), (key1122, -2), (key1107, 6), (key1231, 2), (key1241, 2), (key1234, 2), (key1029, -2), (key994, -2), (key1107, -2), (key1231, -6), (key1035, 2), (key1000, 2), (key1113, 2)]

def rawRow3254 : Integer.Sparse Key := [(key1149, -2), (key1113, -2), (key1122, -2), (key1107, 6), (key1241, 2), (key1231, 2), (key1234, 2), (key1029, -2), (key1107, -2), (key994, -2), (key1231, -6), (key1035, 2), (key1113, 2), (key1000, 2)]

def rawRow3255 : Integer.Sparse Key := [(key1122, -2), (key1149, -2), (key1113, -2), (key1107, 6), (key1234, 2), (key1241, 2), (key1231, 2), (key1107, -2), (key994, -2), (key1029, -2), (key1231, -6), (key1113, 2), (key1000, 2), (key1035, 2)]

def rawRow3256 : Integer.Sparse Key := [(key1149, -2), (key1122, -2), (key1113, -2), (key1107, 6), (key1241, 2), (key1234, 2), (key1231, 2), (key1107, -2), (key1029, -2), (key994, -2), (key1231, -6), (key1113, 2), (key1035, 2), (key1000, 2)]

def rawRow3257 : Integer.Sparse Key := [(key1231, -2), (key1231, -2), (key1241, -2), (key1234, 6), (key1035, 2), (key1035, 2), (key1070, 2), (key1014, -2), (key1122, -2), (key1122, -2), (key1029, -6), (key994, 2), (key1107, 2), (key1107, 2)]

def rawRow3258 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1231, -2), (key1234, 6), (key1035, 2), (key1070, 2), (key1035, 2), (key1122, -2), (key1014, -2), (key1122, -2), (key1029, -6), (key1107, 2), (key994, 2), (key1107, 2)]

def rawRow3259 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1231, -2), (key1234, 6), (key1070, 2), (key1035, 2), (key1035, 2), (key1122, -2), (key1122, -2), (key1014, -2), (key1029, -6), (key1107, 2), (key1107, 2), (key994, 2)]

def rawRow3260 : Integer.Sparse Key := [(key1231, -2), (key1234, -2), (key1241, -2), (key1231, 6), (key1113, 2), (key1122, 2), (key1149, 2), (key1000, -2), (key1035, -2), (key1113, -2), (key1107, -6), (key994, 2), (key1029, 2), (key1107, 2)]

def rawRow3261 : Integer.Sparse Key := [(key1234, -2), (key1231, -2), (key1241, -2), (key1231, 6), (key1122, 2), (key1113, 2), (key1149, 2), (key1000, -2), (key1113, -2), (key1035, -2), (key1107, -6), (key994, 2), (key1107, 2), (key1029, 2)]

def rawRow3262 : Integer.Sparse Key := [(key1231, -2), (key1241, -2), (key1234, -2), (key1231, 6), (key1113, 2), (key1149, 2), (key1122, 2), (key1035, -2), (key1000, -2), (key1113, -2), (key1107, -6), (key1029, 2), (key994, 2), (key1107, 2)]

def rawRow3263 : Integer.Sparse Key := [(key1241, -2), (key1231, -2), (key1234, -2), (key1231, 6), (key1149, 2), (key1113, 2), (key1122, 2), (key1035, -2), (key1113, -2), (key1000, -2), (key1107, -6), (key1029, 2), (key1107, 2), (key994, 2)]

def rawRow3264 : Integer.Sparse Key := [(key1234, -2), (key1241, -2), (key1231, -2), (key1231, 6), (key1122, 2), (key1149, 2), (key1113, 2), (key1113, -2), (key1000, -2), (key1035, -2), (key1107, -6), (key1107, 2), (key994, 2), (key1029, 2)]

def rawRow3265 : Integer.Sparse Key := [(key1241, -2), (key1234, -2), (key1231, -2), (key1231, 6), (key1149, 2), (key1122, 2), (key1113, 2), (key1113, -2), (key1035, -2), (key1000, -2), (key1107, -6), (key1107, 2), (key1029, 2), (key994, 2)]

def rawRow3296 : Integer.Sparse Key := [(key2398, -2), (key2404, -2), (key2435, -2), (key2404, 6), (key2839, 2), (key2845, 2), (key3019, 2), (key2589, -2), (key2845, -2), (key2876, -2), (key2916, -6), (key2604, 2), (key2916, 2), (key2925, 2)]

def rawRow3297 : Integer.Sparse Key := [(key2404, -2), (key2398, -2), (key2435, -2), (key2404, 6), (key2845, 2), (key2839, 2), (key3019, 2), (key2589, -2), (key2876, -2), (key2845, -2), (key2916, -6), (key2604, 2), (key2925, 2), (key2916, 2)]

def rawRow3298 : Integer.Sparse Key := [(key2398, -2), (key2435, -2), (key2404, -2), (key2404, 6), (key2839, 2), (key3019, 2), (key2845, 2), (key2845, -2), (key2589, -2), (key2876, -2), (key2916, -6), (key2916, 2), (key2604, 2), (key2925, 2)]

def rawRow3299 : Integer.Sparse Key := [(key2435, -2), (key2398, -2), (key2404, -2), (key2404, 6), (key3019, 2), (key2839, 2), (key2845, 2), (key2845, -2), (key2876, -2), (key2589, -2), (key2916, -6), (key2916, 2), (key2925, 2), (key2604, 2)]

def rawRow3300 : Integer.Sparse Key := [(key2404, -2), (key2435, -2), (key2398, -2), (key2404, 6), (key2845, 2), (key3019, 2), (key2839, 2), (key2876, -2), (key2589, -2), (key2845, -2), (key2916, -6), (key2925, 2), (key2604, 2), (key2916, 2)]

def rawRow3301 : Integer.Sparse Key := [(key2435, -2), (key2404, -2), (key2398, -2), (key2404, 6), (key3019, 2), (key2845, 2), (key2839, 2), (key2876, -2), (key2845, -2), (key2589, -2), (key2916, -6), (key2925, 2), (key2916, 2), (key2604, 2)]

def rawRow3305 : Integer.Sparse Key := [(key2464, -2), (key2470, -2), (key2501, -2), (key2478, 6), (key2398, 2), (key2404, 2), (key2435, 2), (key2604, -2), (key2916, -2), (key2925, -2), (key2768, -6), (key2589, 2), (key2845, 2), (key2876, 2)]

def rawRow3306 : Integer.Sparse Key := [(key2470, -2), (key2464, -2), (key2501, -2), (key2478, 6), (key2404, 2), (key2398, 2), (key2435, 2), (key2604, -2), (key2925, -2), (key2916, -2), (key2768, -6), (key2589, 2), (key2876, 2), (key2845, 2)]

def rawRow3307 : Integer.Sparse Key := [(key2464, -2), (key2501, -2), (key2470, -2), (key2478, 6), (key2398, 2), (key2435, 2), (key2404, 2), (key2916, -2), (key2604, -2), (key2925, -2), (key2768, -6), (key2845, 2), (key2589, 2), (key2876, 2)]

def rawRow3308 : Integer.Sparse Key := [(key2501, -2), (key2464, -2), (key2470, -2), (key2478, 6), (key2435, 2), (key2398, 2), (key2404, 2), (key2916, -2), (key2925, -2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2589, 2)]

def rawRow3309 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2464, -2), (key2478, 6), (key2404, 2), (key2435, 2), (key2398, 2), (key2925, -2), (key2604, -2), (key2916, -2), (key2768, -6), (key2876, 2), (key2589, 2), (key2845, 2)]

def rawRow3310 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2464, -2), (key2478, 6), (key2435, 2), (key2404, 2), (key2398, 2), (key2925, -2), (key2916, -2), (key2604, -2), (key2768, -6), (key2876, 2), (key2845, 2), (key2589, 2)]

def rawRow3311 : Integer.Sparse Key := [(key2470, -2), (key2478, -2), (key2501, -2), (key2464, 6), (key2568, 2), (key2570, 2), (key2575, 2), (key2370, -2), (key2762, -2), (key2839, -2), (key2876, -6), (key2589, 2), (key2768, 2), (key2845, 2)]

def rawRow3312 : Integer.Sparse Key := [(key2478, -2), (key2470, -2), (key2501, -2), (key2464, 6), (key2570, 2), (key2568, 2), (key2575, 2), (key2370, -2), (key2839, -2), (key2762, -2), (key2876, -6), (key2589, 2), (key2845, 2), (key2768, 2)]

def rawRow3313 : Integer.Sparse Key := [(key2470, -2), (key2501, -2), (key2478, -2), (key2464, 6), (key2568, 2), (key2575, 2), (key2570, 2), (key2398, -2), (key2583, -2), (key2839, -2), (key2876, -6), (key2768, 2), (key2589, 2), (key2845, 2)]

def rawRow3314 : Integer.Sparse Key := [(key2501, -2), (key2470, -2), (key2478, -2), (key2464, 6), (key2575, 2), (key2568, 2), (key2570, 2), (key2398, -2), (key2839, -2), (key2583, -2), (key2876, -6), (key2768, 2), (key2845, 2), (key2589, 2)]

def rawRow3315 : Integer.Sparse Key := [(key2478, -2), (key2501, -2), (key2470, -2), (key2464, 6), (key2570, 2), (key2575, 2), (key2568, 2), (key2464, -2), (key2370, -2), (key2762, -2), (key2876, -6), (key2845, 2), (key2589, 2), (key2768, 2)]

def rawRow3316 : Integer.Sparse Key := [(key2501, -2), (key2478, -2), (key2470, -2), (key2464, 6), (key2575, 2), (key2570, 2), (key2568, 2), (key2464, -2), (key2398, -2), (key2583, -2), (key2876, -6), (key2845, 2), (key2768, 2), (key2589, 2)]

def rawRow3320 : Integer.Sparse Key := [(key2568, -2), (key2570, -2), (key2575, -2), (key2568, 6), (key2470, 2), (key2478, 2), (key2501, 2), (key2376, -2), (key2404, -2), (key2470, -2), (key2464, -6), (key2370, 2), (key2762, 2), (key2839, 2)]

def rawRow3321 : Integer.Sparse Key := [(key2570, -2), (key2568, -2), (key2575, -2), (key2568, 6), (key2478, 2), (key2470, 2), (key2501, 2), (key2376, -2), (key2470, -2), (key2404, -2), (key2464, -6), (key2370, 2), (key2839, 2), (key2762, 2)]

def rawRow3322 : Integer.Sparse Key := [(key2568, -2), (key2575, -2), (key2570, -2), (key2568, 6), (key2470, 2), (key2501, 2), (key2478, 2), (key2404, -2), (key2376, -2), (key2470, -2), (key2464, -6), (key2398, 2), (key2583, 2), (key2839, 2)]

def rawRow3323 : Integer.Sparse Key := [(key2575, -2), (key2568, -2), (key2570, -2), (key2568, 6), (key2501, 2), (key2470, 2), (key2478, 2), (key2404, -2), (key2470, -2), (key2376, -2), (key2464, -6), (key2398, 2), (key2839, 2), (key2583, 2)]

def rawRow3324 : Integer.Sparse Key := [(key2570, -2), (key2575, -2), (key2568, -2), (key2568, 6), (key2478, 2), (key2501, 2), (key2470, 2), (key2470, -2), (key2376, -2), (key2404, -2), (key2464, -6), (key2464, 2), (key2370, 2), (key2762, 2)]

def rawRow3325 : Integer.Sparse Key := [(key2575, -2), (key2570, -2), (key2568, -2), (key2568, 6), (key2501, 2), (key2478, 2), (key2470, 2), (key2470, -2), (key2404, -2), (key2376, -2), (key2464, -6), (key2464, 2), (key2398, 2), (key2583, 2)]

def rawRow3326 : Integer.Sparse Key := [(key2763, -2), (key2767, -2), (key2930, -2), (key2767, 6), (key2840, 2), (key2844, 2), (key2967, 2), (key2588, -2), (key2844, -2), (key2875, -2), (key2888, -6), (key2599, 2), (key2888, 2), (key2909, 2)]

def rawRow3327 : Integer.Sparse Key := [(key2767, -2), (key2763, -2), (key2930, -2), (key2767, 6), (key2844, 2), (key2840, 2), (key2967, 2), (key2588, -2), (key2875, -2), (key2844, -2), (key2888, -6), (key2599, 2), (key2909, 2), (key2888, 2)]

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

def rawRow3328 : Integer.Sparse Key := [(key2763, -2), (key2930, -2), (key2767, -2), (key2767, 6), (key2840, 2), (key2967, 2), (key2844, 2), (key2844, -2), (key2588, -2), (key2875, -2), (key2888, -6), (key2888, 2), (key2599, 2), (key2909, 2)]

def rawRow3329 : Integer.Sparse Key := [(key2930, -2), (key2763, -2), (key2767, -2), (key2767, 6), (key2967, 2), (key2840, 2), (key2844, 2), (key2844, -2), (key2875, -2), (key2588, -2), (key2888, -6), (key2888, 2), (key2909, 2), (key2599, 2)]

def rawRow3330 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2763, -2), (key2767, 6), (key2844, 2), (key2967, 2), (key2840, 2), (key2875, -2), (key2588, -2), (key2844, -2), (key2888, -6), (key2909, 2), (key2599, 2), (key2888, 2)]

def rawRow3331 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2763, -2), (key2767, 6), (key2967, 2), (key2844, 2), (key2840, 2), (key2875, -2), (key2844, -2), (key2588, -2), (key2888, -6), (key2909, 2), (key2888, 2), (key2599, 2)]

def rawRow3332 : Integer.Sparse Key := [(key2767, -2), (key2767, -2), (key2930, -2), (key2763, 6), (key2875, 2), (key2875, 2), (key2988, 2), (key2584, -2), (key2840, -2), (key2840, -2), (key2909, -6), (key2599, 2), (key2888, 2), (key2888, 2)]

def rawRow3333 : Integer.Sparse Key := [(key2767, -2), (key2930, -2), (key2767, -2), (key2763, 6), (key2875, 2), (key2988, 2), (key2875, 2), (key2840, -2), (key2584, -2), (key2840, -2), (key2909, -6), (key2888, 2), (key2599, 2), (key2888, 2)]

def rawRow3334 : Integer.Sparse Key := [(key2930, -2), (key2767, -2), (key2767, -2), (key2763, 6), (key2988, 2), (key2875, 2), (key2875, 2), (key2840, -2), (key2840, -2), (key2584, -2), (key2909, -6), (key2888, 2), (key2888, 2), (key2599, 2)]

def rawRow3335 : Integer.Sparse Key := [(key2840, -2), (key2844, -2), (key2967, -2), (key2888, 6), (key2763, 2), (key2767, 2), (key2930, 2), (key2599, -2), (key2888, -2), (key2909, -2), (key2767, -6), (key2588, 2), (key2844, 2), (key2875, 2)]

def rawRow3336 : Integer.Sparse Key := [(key2844, -2), (key2840, -2), (key2967, -2), (key2888, 6), (key2767, 2), (key2763, 2), (key2930, 2), (key2599, -2), (key2909, -2), (key2888, -2), (key2767, -6), (key2588, 2), (key2875, 2), (key2844, 2)]

def rawRow3337 : Integer.Sparse Key := [(key2840, -2), (key2967, -2), (key2844, -2), (key2888, 6), (key2763, 2), (key2930, 2), (key2767, 2), (key2888, -2), (key2599, -2), (key2909, -2), (key2767, -6), (key2844, 2), (key2588, 2), (key2875, 2)]

def rawRow3338 : Integer.Sparse Key := [(key2967, -2), (key2840, -2), (key2844, -2), (key2888, 6), (key2930, 2), (key2763, 2), (key2767, 2), (key2888, -2), (key2909, -2), (key2599, -2), (key2767, -6), (key2844, 2), (key2875, 2), (key2588, 2)]

def rawRow3339 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2840, -2), (key2888, 6), (key2767, 2), (key2930, 2), (key2763, 2), (key2909, -2), (key2599, -2), (key2888, -2), (key2767, -6), (key2875, 2), (key2588, 2), (key2844, 2)]

def rawRow3340 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2840, -2), (key2888, 6), (key2930, 2), (key2767, 2), (key2763, 2), (key2909, -2), (key2888, -2), (key2599, -2), (key2767, -6), (key2875, 2), (key2844, 2), (key2588, 2)]

def rawRow3341 : Integer.Sparse Key := [(key2844, -2), (key2888, -2), (key2967, -2), (key2840, 6), (key2875, 2), (key2909, 2), (key2988, 2), (key2584, -2), (key2763, -2), (key2840, -2), (key2875, -6), (key2588, 2), (key2767, 2), (key2844, 2)]

def rawRow3342 : Integer.Sparse Key := [(key2888, -2), (key2844, -2), (key2967, -2), (key2840, 6), (key2909, 2), (key2875, 2), (key2988, 2), (key2584, -2), (key2840, -2), (key2763, -2), (key2875, -6), (key2588, 2), (key2844, 2), (key2767, 2)]

def rawRow3343 : Integer.Sparse Key := [(key2844, -2), (key2967, -2), (key2888, -2), (key2840, 6), (key2875, 2), (key2988, 2), (key2909, 2), (key2763, -2), (key2584, -2), (key2840, -2), (key2875, -6), (key2767, 2), (key2588, 2), (key2844, 2)]

def rawRow3344 : Integer.Sparse Key := [(key2967, -2), (key2844, -2), (key2888, -2), (key2840, 6), (key2988, 2), (key2875, 2), (key2909, 2), (key2763, -2), (key2840, -2), (key2584, -2), (key2875, -6), (key2767, 2), (key2844, 2), (key2588, 2)]

def rawRow3345 : Integer.Sparse Key := [(key2888, -2), (key2967, -2), (key2844, -2), (key2840, 6), (key2909, 2), (key2988, 2), (key2875, 2), (key2840, -2), (key2584, -2), (key2763, -2), (key2875, -6), (key2844, 2), (key2588, 2), (key2767, 2)]

def rawRow3346 : Integer.Sparse Key := [(key2967, -2), (key2888, -2), (key2844, -2), (key2840, 6), (key2988, 2), (key2909, 2), (key2875, 2), (key2840, -2), (key2763, -2), (key2584, -2), (key2875, -6), (key2844, 2), (key2767, 2), (key2588, 2)]

def rawRow3347 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2988, -2), (key2909, 6), (key2767, 2), (key2767, 2), (key2930, 2), (key2599, -2), (key2888, -2), (key2888, -2), (key2763, -6), (key2584, 2), (key2840, 2), (key2840, 2)]

def rawRow3348 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2875, -2), (key2909, 6), (key2767, 2), (key2930, 2), (key2767, 2), (key2888, -2), (key2599, -2), (key2888, -2), (key2763, -6), (key2840, 2), (key2584, 2), (key2840, 2)]

def rawRow3349 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2875, -2), (key2909, 6), (key2930, 2), (key2767, 2), (key2767, 2), (key2888, -2), (key2888, -2), (key2599, -2), (key2763, -6), (key2840, 2), (key2840, 2), (key2584, 2)]

def rawRow3350 : Integer.Sparse Key := [(key2875, -2), (key2909, -2), (key2988, -2), (key2875, 6), (key2844, 2), (key2888, 2), (key2967, 2), (key2588, -2), (key2767, -2), (key2844, -2), (key2840, -6), (key2584, 2), (key2763, 2), (key2840, 2)]

def rawRow3351 : Integer.Sparse Key := [(key2909, -2), (key2875, -2), (key2988, -2), (key2875, 6), (key2888, 2), (key2844, 2), (key2967, 2), (key2588, -2), (key2844, -2), (key2767, -2), (key2840, -6), (key2584, 2), (key2840, 2), (key2763, 2)]

def rawRow3352 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2909, -2), (key2875, 6), (key2844, 2), (key2967, 2), (key2888, 2), (key2767, -2), (key2588, -2), (key2844, -2), (key2840, -6), (key2763, 2), (key2584, 2), (key2840, 2)]

def rawRow3353 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2909, -2), (key2875, 6), (key2967, 2), (key2844, 2), (key2888, 2), (key2767, -2), (key2844, -2), (key2588, -2), (key2840, -6), (key2763, 2), (key2840, 2), (key2584, 2)]

def rawRow3354 : Integer.Sparse Key := [(key2909, -2), (key2988, -2), (key2875, -2), (key2875, 6), (key2888, 2), (key2967, 2), (key2844, 2), (key2844, -2), (key2588, -2), (key2767, -2), (key2840, -6), (key2840, 2), (key2584, 2), (key2763, 2)]

def rawRow3355 : Integer.Sparse Key := [(key2988, -2), (key2909, -2), (key2875, -2), (key2875, 6), (key2967, 2), (key2888, 2), (key2844, 2), (key2844, -2), (key2767, -2), (key2588, -2), (key2840, -6), (key2840, 2), (key2763, 2), (key2584, 2)]

def rawRow3386 : Integer.Sparse Key := [(key2174, -2), (key2176, -2), (key2187, -2), (key2176, 6), (key2274, 2), (key2276, 2), (key2287, 2), (key2079, -2), (key2276, -2), (key2341, -2), (key2279, -6), (key2085, 2), (key2279, 2), (key2343, 2)]

def rawRow3387 : Integer.Sparse Key := [(key2176, -2), (key2174, -2), (key2187, -2), (key2176, 6), (key2276, 2), (key2274, 2), (key2287, 2), (key2079, -2), (key2341, -2), (key2276, -2), (key2279, -6), (key2085, 2), (key2343, 2), (key2279, 2)]

def rawRow3388 : Integer.Sparse Key := [(key2174, -2), (key2187, -2), (key2176, -2), (key2176, 6), (key2274, 2), (key2287, 2), (key2276, 2), (key2276, -2), (key2079, -2), (key2341, -2), (key2279, -6), (key2279, 2), (key2085, 2), (key2343, 2)]

def rawRow3389 : Integer.Sparse Key := [(key2187, -2), (key2174, -2), (key2176, -2), (key2176, 6), (key2287, 2), (key2274, 2), (key2276, 2), (key2276, -2), (key2341, -2), (key2079, -2), (key2279, -6), (key2279, 2), (key2343, 2), (key2085, 2)]

def rawRow3390 : Integer.Sparse Key := [(key2176, -2), (key2187, -2), (key2174, -2), (key2176, 6), (key2276, 2), (key2287, 2), (key2274, 2), (key2341, -2), (key2079, -2), (key2276, -2), (key2279, -6), (key2343, 2), (key2085, 2), (key2279, 2)]

def rawRow3391 : Integer.Sparse Key := [(key2187, -2), (key2176, -2), (key2174, -2), (key2176, 6), (key2287, 2), (key2276, 2), (key2274, 2), (key2341, -2), (key2276, -2), (key2079, -2), (key2279, -6), (key2343, 2), (key2279, 2), (key2085, 2)]

def rawRow3392 : Integer.Sparse Key := [(key2176, -2), (key2176, -2), (key2187, -2), (key2174, 6), (key2341, 2), (key2341, 2), (key2347, 2), (key2077, -2), (key2274, -2), (key2274, -2), (key2343, -6), (key2085, 2), (key2279, 2), (key2279, 2)]

def rawRow3393 : Integer.Sparse Key := [(key2176, -2), (key2187, -2), (key2176, -2), (key2174, 6), (key2341, 2), (key2347, 2), (key2341, 2), (key2274, -2), (key2077, -2), (key2274, -2), (key2343, -6), (key2279, 2), (key2085, 2), (key2279, 2)]

def rawRow3394 : Integer.Sparse Key := [(key2187, -2), (key2176, -2), (key2176, -2), (key2174, 6), (key2347, 2), (key2341, 2), (key2341, 2), (key2274, -2), (key2274, -2), (key2077, -2), (key2343, -6), (key2279, 2), (key2279, 2), (key2085, 2)]

def rawRow3395 : Integer.Sparse Key := [(key2274, -2), (key2276, -2), (key2287, -2), (key2279, 6), (key2174, 2), (key2176, 2), (key2187, 2), (key2085, -2), (key2279, -2), (key2343, -2), (key2176, -6), (key2079, 2), (key2276, 2), (key2341, 2)]

def rawRow3396 : Integer.Sparse Key := [(key2276, -2), (key2274, -2), (key2287, -2), (key2279, 6), (key2176, 2), (key2174, 2), (key2187, 2), (key2085, -2), (key2343, -2), (key2279, -2), (key2176, -6), (key2079, 2), (key2341, 2), (key2276, 2)]

def rawRow3397 : Integer.Sparse Key := [(key2274, -2), (key2287, -2), (key2276, -2), (key2279, 6), (key2174, 2), (key2187, 2), (key2176, 2), (key2279, -2), (key2085, -2), (key2343, -2), (key2176, -6), (key2276, 2), (key2079, 2), (key2341, 2)]

def rawRow3398 : Integer.Sparse Key := [(key2287, -2), (key2274, -2), (key2276, -2), (key2279, 6), (key2187, 2), (key2174, 2), (key2176, 2), (key2279, -2), (key2343, -2), (key2085, -2), (key2176, -6), (key2276, 2), (key2341, 2), (key2079, 2)]

def rawRow3399 : Integer.Sparse Key := [(key2276, -2), (key2287, -2), (key2274, -2), (key2279, 6), (key2176, 2), (key2187, 2), (key2174, 2), (key2343, -2), (key2085, -2), (key2279, -2), (key2176, -6), (key2341, 2), (key2079, 2), (key2276, 2)]

def rawRow3400 : Integer.Sparse Key := [(key2287, -2), (key2276, -2), (key2274, -2), (key2279, 6), (key2187, 2), (key2176, 2), (key2174, 2), (key2343, -2), (key2279, -2), (key2085, -2), (key2176, -6), (key2341, 2), (key2276, 2), (key2079, 2)]

def rawRow3401 : Integer.Sparse Key := [(key2276, -2), (key2279, -2), (key2287, -2), (key2274, 6), (key2341, 2), (key2343, 2), (key2347, 2), (key2077, -2), (key2174, -2), (key2274, -2), (key2341, -6), (key2079, 2), (key2176, 2), (key2276, 2)]

def rawRow3402 : Integer.Sparse Key := [(key2279, -2), (key2276, -2), (key2287, -2), (key2274, 6), (key2343, 2), (key2341, 2), (key2347, 2), (key2077, -2), (key2274, -2), (key2174, -2), (key2341, -6), (key2079, 2), (key2276, 2), (key2176, 2)]

def rawRow3403 : Integer.Sparse Key := [(key2276, -2), (key2287, -2), (key2279, -2), (key2274, 6), (key2341, 2), (key2347, 2), (key2343, 2), (key2174, -2), (key2077, -2), (key2274, -2), (key2341, -6), (key2176, 2), (key2079, 2), (key2276, 2)]

def rawRow3404 : Integer.Sparse Key := [(key2287, -2), (key2276, -2), (key2279, -2), (key2274, 6), (key2347, 2), (key2341, 2), (key2343, 2), (key2174, -2), (key2274, -2), (key2077, -2), (key2341, -6), (key2176, 2), (key2276, 2), (key2079, 2)]

def rawRow3405 : Integer.Sparse Key := [(key2279, -2), (key2287, -2), (key2276, -2), (key2274, 6), (key2343, 2), (key2347, 2), (key2341, 2), (key2274, -2), (key2077, -2), (key2174, -2), (key2341, -6), (key2276, 2), (key2079, 2), (key2176, 2)]

def rawRow3406 : Integer.Sparse Key := [(key2287, -2), (key2279, -2), (key2276, -2), (key2274, 6), (key2347, 2), (key2343, 2), (key2341, 2), (key2274, -2), (key2174, -2), (key2077, -2), (key2341, -6), (key2276, 2), (key2176, 2), (key2079, 2)]

def rawRow3407 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2347, -2), (key2343, 6), (key2176, 2), (key2176, 2), (key2187, 2), (key2085, -2), (key2279, -2), (key2279, -2), (key2174, -6), (key2077, 2), (key2274, 2), (key2274, 2)]

def rawRow3408 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2341, -2), (key2343, 6), (key2176, 2), (key2187, 2), (key2176, 2), (key2279, -2), (key2085, -2), (key2279, -2), (key2174, -6), (key2274, 2), (key2077, 2), (key2274, 2)]

def rawRow3409 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2341, -2), (key2343, 6), (key2187, 2), (key2176, 2), (key2176, 2), (key2279, -2), (key2279, -2), (key2085, -2), (key2174, -6), (key2274, 2), (key2274, 2), (key2077, 2)]

def rawRow3410 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2347, -2), (key2341, 6), (key2276, 2), (key2279, 2), (key2287, 2), (key2079, -2), (key2176, -2), (key2276, -2), (key2274, -6), (key2077, 2), (key2174, 2), (key2274, 2)]

def rawRow3411 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2347, -2), (key2341, 6), (key2279, 2), (key2276, 2), (key2287, 2), (key2079, -2), (key2276, -2), (key2176, -2), (key2274, -6), (key2077, 2), (key2274, 2), (key2174, 2)]

def rawRow3412 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2343, -2), (key2341, 6), (key2276, 2), (key2287, 2), (key2279, 2), (key2176, -2), (key2079, -2), (key2276, -2), (key2274, -6), (key2174, 2), (key2077, 2), (key2274, 2)]

def rawRow3413 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2343, -2), (key2341, 6), (key2287, 2), (key2276, 2), (key2279, 2), (key2176, -2), (key2276, -2), (key2079, -2), (key2274, -6), (key2174, 2), (key2274, 2), (key2077, 2)]

def rawRow3414 : Integer.Sparse Key := [(key2343, -2), (key2347, -2), (key2341, -2), (key2341, 6), (key2279, 2), (key2287, 2), (key2276, 2), (key2276, -2), (key2079, -2), (key2176, -2), (key2274, -6), (key2274, 2), (key2077, 2), (key2174, 2)]

def rawRow3415 : Integer.Sparse Key := [(key2347, -2), (key2343, -2), (key2341, -2), (key2341, 6), (key2287, 2), (key2279, 2), (key2276, 2), (key2276, -2), (key2176, -2), (key2079, -2), (key2274, -6), (key2274, 2), (key2174, 2), (key2077, 2)]

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

def rawRow3704 : Integer.Sparse Key := [(key1296, -2), (key1788, -2), (key1798, -2), (key1296, 1), (key1302, 1), (key1573, 1), (key1596, 1), (key1790, 1), (key1798, 1), (key1316, 2), (key1813, 2), (key1825, 2), (key1316, -1), (key1329, -1), (key1424, -1), (key1447, -1), (key1817, -1), (key1825, -1), (key1337, -1), (key1339, -1), (key1655, -1), (key1667, -1), (key1839, -1), (key1844, -1), (key1337, 1), (key1345, 1), (key1455, 1), (key1466, 1), (key1841, 1), (key1844, 1)]

def rawRow3705 : Integer.Sparse Key := [(key1296, -2), (key1798, -2), (key1788, -2), (key1302, 1), (key1296, 1), (key1596, 1), (key1573, 1), (key1798, 1), (key1790, 1), (key1316, 2), (key1825, 2), (key1813, 2), (key1329, -1), (key1316, -1), (key1447, -1), (key1424, -1), (key1825, -1), (key1817, -1), (key1339, -1), (key1337, -1), (key1667, -1), (key1655, -1), (key1844, -1), (key1839, -1), (key1345, 1), (key1337, 1), (key1466, 1), (key1455, 1), (key1844, 1), (key1841, 1)]

def rawRow3706 : Integer.Sparse Key := [(key1788, -2), (key1296, -2), (key1798, -2), (key1573, 1), (key1790, 1), (key1296, 1), (key1798, 1), (key1302, 1), (key1596, 1), (key1813, 2), (key1316, 2), (key1825, 2), (key1424, -1), (key1817, -1), (key1316, -1), (key1825, -1), (key1329, -1), (key1447, -1), (key1655, -1), (key1839, -1), (key1337, -1), (key1844, -1), (key1339, -1), (key1667, -1), (key1455, 1), (key1841, 1), (key1337, 1), (key1844, 1), (key1345, 1), (key1466, 1)]

def rawRow3707 : Integer.Sparse Key := [(key1788, -2), (key1798, -2), (key1296, -2), (key1790, 1), (key1573, 1), (key1798, 1), (key1296, 1), (key1596, 1), (key1302, 1), (key1813, 2), (key1825, 2), (key1316, 2), (key1817, -1), (key1424, -1), (key1825, -1), (key1316, -1), (key1447, -1), (key1329, -1), (key1839, -1), (key1655, -1), (key1844, -1), (key1337, -1), (key1667, -1), (key1339, -1), (key1841, 1), (key1455, 1), (key1844, 1), (key1337, 1), (key1466, 1), (key1345, 1)]

def rawRow3708 : Integer.Sparse Key := [(key1798, -2), (key1296, -2), (key1788, -2), (key1596, 1), (key1798, 1), (key1302, 1), (key1790, 1), (key1296, 1), (key1573, 1), (key1825, 2), (key1316, 2), (key1813, 2), (key1447, -1), (key1825, -1), (key1329, -1), (key1817, -1), (key1316, -1), (key1424, -1), (key1667, -1), (key1844, -1), (key1339, -1), (key1839, -1), (key1337, -1), (key1655, -1), (key1466, 1), (key1844, 1), (key1345, 1), (key1841, 1), (key1337, 1), (key1455, 1)]

def rawRow3709 : Integer.Sparse Key := [(key1798, -2), (key1788, -2), (key1296, -2), (key1798, 1), (key1596, 1), (key1790, 1), (key1302, 1), (key1573, 1), (key1296, 1), (key1825, 2), (key1813, 2), (key1316, 2), (key1825, -1), (key1447, -1), (key1817, -1), (key1329, -1), (key1424, -1), (key1316, -1), (key1844, -1), (key1667, -1), (key1839, -1), (key1339, -1), (key1655, -1), (key1337, -1), (key1844, 1), (key1466, 1), (key1841, 1), (key1345, 1), (key1455, 1), (key1337, 1)]

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

def rawRow3713 : Integer.Sparse Key := [(key1316, -2), (key1813, -2), (key1825, -2), (key1337, 1), (key1339, 1), (key1655, 1), (key1667, 1), (key1839, 1), (key1844, 1), (key1296, 2), (key1788, 2), (key1798, 2), (key1337, -1), (key1345, -1), (key1455, -1), (key1466, -1), (key1841, -1), (key1844, -1), (key1296, -1), (key1302, -1), (key1573, -1), (key1596, -1), (key1790, -1), (key1798, -1), (key1316, 1), (key1329, 1), (key1424, 1), (key1447, 1), (key1817, 1), (key1825, 1)]

def rawRow3714 : Integer.Sparse Key := [(key1316, -2), (key1825, -2), (key1813, -2), (key1339, 1), (key1337, 1), (key1667, 1), (key1655, 1), (key1844, 1), (key1839, 1), (key1296, 2), (key1798, 2), (key1788, 2), (key1345, -1), (key1337, -1), (key1466, -1), (key1455, -1), (key1844, -1), (key1841, -1), (key1302, -1), (key1296, -1), (key1596, -1), (key1573, -1), (key1798, -1), (key1790, -1), (key1329, 1), (key1316, 1), (key1447, 1), (key1424, 1), (key1825, 1), (key1817, 1)]

def rawRow3715 : Integer.Sparse Key := [(key1813, -2), (key1316, -2), (key1825, -2), (key1655, 1), (key1839, 1), (key1337, 1), (key1844, 1), (key1339, 1), (key1667, 1), (key1788, 2), (key1296, 2), (key1798, 2), (key1455, -1), (key1841, -1), (key1337, -1), (key1844, -1), (key1345, -1), (key1466, -1), (key1573, -1), (key1790, -1), (key1296, -1), (key1798, -1), (key1302, -1), (key1596, -1), (key1424, 1), (key1817, 1), (key1316, 1), (key1825, 1), (key1329, 1), (key1447, 1)]

def rawRow3716 : Integer.Sparse Key := [(key1813, -2), (key1825, -2), (key1316, -2), (key1839, 1), (key1655, 1), (key1844, 1), (key1337, 1), (key1667, 1), (key1339, 1), (key1788, 2), (key1798, 2), (key1296, 2), (key1841, -1), (key1455, -1), (key1844, -1), (key1337, -1), (key1466, -1), (key1345, -1), (key1790, -1), (key1573, -1), (key1798, -1), (key1296, -1), (key1596, -1), (key1302, -1), (key1817, 1), (key1424, 1), (key1825, 1), (key1316, 1), (key1447, 1), (key1329, 1)]

def rawRow3717 : Integer.Sparse Key := [(key1825, -2), (key1316, -2), (key1813, -2), (key1667, 1), (key1844, 1), (key1339, 1), (key1839, 1), (key1337, 1), (key1655, 1), (key1798, 2), (key1296, 2), (key1788, 2), (key1466, -1), (key1844, -1), (key1345, -1), (key1841, -1), (key1337, -1), (key1455, -1), (key1596, -1), (key1798, -1), (key1302, -1), (key1790, -1), (key1296, -1), (key1573, -1), (key1447, 1), (key1825, 1), (key1329, 1), (key1817, 1), (key1316, 1), (key1424, 1)]

def rawRow3718 : Integer.Sparse Key := [(key1825, -2), (key1813, -2), (key1316, -2), (key1844, 1), (key1667, 1), (key1839, 1), (key1339, 1), (key1655, 1), (key1337, 1), (key1798, 2), (key1788, 2), (key1296, 2), (key1844, -1), (key1466, -1), (key1841, -1), (key1345, -1), (key1455, -1), (key1337, -1), (key1798, -1), (key1596, -1), (key1790, -1), (key1302, -1), (key1573, -1), (key1296, -1), (key1825, 1), (key1447, 1), (key1817, 1), (key1329, 1), (key1424, 1), (key1316, 1)]

def rawRow3719 : Integer.Sparse Key := [(key1339, -2), (key1774, -2), (key1839, -2), (key1316, 1), (key1337, 1), (key1546, 1), (key1655, 1), (key1772, 1), (key1813, 1), (key1345, 2), (key1780, 2), (key1841, 2), (key1296, -1), (key1337, -1), (key1391, -1), (key1455, -1), (key1772, -1), (key1788, -1), (key1329, -1), (key1345, -1), (key1559, -1), (key1659, -1), (key1780, -1), (key1817, -1), (key1302, 1), (key1339, 1), (key1397, 1), (key1457, 1), (key1774, 1), (key1790, 1)]

def rawRow3720 : Integer.Sparse Key := [(key1339, -2), (key1839, -2), (key1774, -2), (key1337, 1), (key1316, 1), (key1655, 1), (key1546, 1), (key1813, 1), (key1772, 1), (key1345, 2), (key1841, 2), (key1780, 2), (key1337, -1), (key1296, -1), (key1455, -1), (key1391, -1), (key1788, -1), (key1772, -1), (key1345, -1), (key1329, -1), (key1659, -1), (key1559, -1), (key1817, -1), (key1780, -1), (key1339, 1), (key1302, 1), (key1457, 1), (key1397, 1), (key1790, 1), (key1774, 1)]

def rawRow3721 : Integer.Sparse Key := [(key1774, -2), (key1339, -2), (key1839, -2), (key1546, 1), (key1772, 1), (key1316, 1), (key1813, 1), (key1337, 1), (key1655, 1), (key1780, 2), (key1345, 2), (key1841, 2), (key1391, -1), (key1772, -1), (key1296, -1), (key1788, -1), (key1337, -1), (key1455, -1), (key1559, -1), (key1780, -1), (key1329, -1), (key1817, -1), (key1345, -1), (key1659, -1), (key1397, 1), (key1774, 1), (key1302, 1), (key1790, 1), (key1339, 1), (key1457, 1)]

def rawRow3722 : Integer.Sparse Key := [(key1774, -2), (key1839, -2), (key1339, -2), (key1772, 1), (key1546, 1), (key1813, 1), (key1316, 1), (key1655, 1), (key1337, 1), (key1780, 2), (key1841, 2), (key1345, 2), (key1772, -1), (key1391, -1), (key1788, -1), (key1296, -1), (key1455, -1), (key1337, -1), (key1780, -1), (key1559, -1), (key1817, -1), (key1329, -1), (key1659, -1), (key1345, -1), (key1774, 1), (key1397, 1), (key1790, 1), (key1302, 1), (key1457, 1), (key1339, 1)]

def rawRow3723 : Integer.Sparse Key := [(key1839, -2), (key1339, -2), (key1774, -2), (key1655, 1), (key1813, 1), (key1337, 1), (key1772, 1), (key1316, 1), (key1546, 1), (key1841, 2), (key1345, 2), (key1780, 2), (key1455, -1), (key1788, -1), (key1337, -1), (key1772, -1), (key1296, -1), (key1391, -1), (key1659, -1), (key1817, -1), (key1345, -1), (key1780, -1), (key1329, -1), (key1559, -1), (key1457, 1), (key1790, 1), (key1339, 1), (key1774, 1), (key1302, 1), (key1397, 1)]

def rawRow3724 : Integer.Sparse Key := [(key1839, -2), (key1774, -2), (key1339, -2), (key1813, 1), (key1655, 1), (key1772, 1), (key1337, 1), (key1546, 1), (key1316, 1), (key1841, 2), (key1780, 2), (key1345, 2), (key1788, -1), (key1455, -1), (key1772, -1), (key1337, -1), (key1391, -1), (key1296, -1), (key1817, -1), (key1659, -1), (key1780, -1), (key1345, -1), (key1559, -1), (key1329, -1), (key1790, 1), (key1457, 1), (key1774, 1), (key1339, 1), (key1397, 1), (key1302, 1)]

def rawRow3728 : Integer.Sparse Key := [(key1345, -2), (key1780, -2), (key1841, -2), (key1329, 1), (key1345, 1), (key1559, 1), (key1659, 1), (key1780, 1), (key1817, 1), (key1339, 2), (key1774, 2), (key1839, 2), (key1302, -1), (key1339, -1), (key1397, -1), (key1457, -1), (key1774, -1), (key1790, -1), (key1316, -1), (key1337, -1), (key1546, -1), (key1655, -1), (key1772, -1), (key1813, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1455, 1), (key1772, 1), (key1788, 1)]

def rawRow3729 : Integer.Sparse Key := [(key1345, -2), (key1841, -2), (key1780, -2), (key1345, 1), (key1329, 1), (key1659, 1), (key1559, 1), (key1817, 1), (key1780, 1), (key1339, 2), (key1839, 2), (key1774, 2), (key1339, -1), (key1302, -1), (key1457, -1), (key1397, -1), (key1790, -1), (key1774, -1), (key1337, -1), (key1316, -1), (key1655, -1), (key1546, -1), (key1813, -1), (key1772, -1), (key1337, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1772, 1)]

def rawRow3730 : Integer.Sparse Key := [(key1780, -2), (key1345, -2), (key1841, -2), (key1559, 1), (key1780, 1), (key1329, 1), (key1817, 1), (key1345, 1), (key1659, 1), (key1774, 2), (key1339, 2), (key1839, 2), (key1397, -1), (key1774, -1), (key1302, -1), (key1790, -1), (key1339, -1), (key1457, -1), (key1546, -1), (key1772, -1), (key1316, -1), (key1813, -1), (key1337, -1), (key1655, -1), (key1391, 1), (key1772, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1455, 1)]

def rawRow3731 : Integer.Sparse Key := [(key1780, -2), (key1841, -2), (key1345, -2), (key1780, 1), (key1559, 1), (key1817, 1), (key1329, 1), (key1659, 1), (key1345, 1), (key1774, 2), (key1839, 2), (key1339, 2), (key1774, -1), (key1397, -1), (key1790, -1), (key1302, -1), (key1457, -1), (key1339, -1), (key1772, -1), (key1546, -1), (key1813, -1), (key1316, -1), (key1655, -1), (key1337, -1), (key1772, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1455, 1), (key1337, 1)]

def rawRow3732 : Integer.Sparse Key := [(key1841, -2), (key1345, -2), (key1780, -2), (key1659, 1), (key1817, 1), (key1345, 1), (key1780, 1), (key1329, 1), (key1559, 1), (key1839, 2), (key1339, 2), (key1774, 2), (key1457, -1), (key1790, -1), (key1339, -1), (key1774, -1), (key1302, -1), (key1397, -1), (key1655, -1), (key1813, -1), (key1337, -1), (key1772, -1), (key1316, -1), (key1546, -1), (key1455, 1), (key1788, 1), (key1337, 1), (key1772, 1), (key1296, 1), (key1391, 1)]

def rawRow3733 : Integer.Sparse Key := [(key1841, -2), (key1780, -2), (key1345, -2), (key1817, 1), (key1659, 1), (key1780, 1), (key1345, 1), (key1559, 1), (key1329, 1), (key1839, 2), (key1774, 2), (key1339, 2), (key1790, -1), (key1457, -1), (key1774, -1), (key1339, -1), (key1397, -1), (key1302, -1), (key1813, -1), (key1655, -1), (key1772, -1), (key1337, -1), (key1546, -1), (key1316, -1), (key1788, 1), (key1455, 1), (key1772, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

def rawRow3734 : Integer.Sparse Key := [(key384, -6), (key301, 2), (key384, 2), (key393, 2), (key405, 6), (key235, -2), (key405, -2), (key416, -2), (key315, -2), (key434, -2), (key438, -2), (key247, 2), (key434, 2), (key448, 2)]

def rawRow3735 : Integer.Sparse Key := [(key384, -6), (key301, 2), (key393, 2), (key384, 2), (key405, 6), (key235, -2), (key416, -2), (key405, -2), (key315, -2), (key438, -2), (key434, -2), (key247, 2), (key448, 2), (key434, 2)]

def rawRow3736 : Integer.Sparse Key := [(key384, -6), (key384, 2), (key301, 2), (key393, 2), (key405, 6), (key405, -2), (key235, -2), (key416, -2), (key434, -2), (key315, -2), (key438, -2), (key434, 2), (key247, 2), (key448, 2)]

def rawRow3737 : Integer.Sparse Key := [(key384, -6), (key384, 2), (key393, 2), (key301, 2), (key405, 6), (key405, -2), (key416, -2), (key235, -2), (key434, -2), (key438, -2), (key315, -2), (key434, 2), (key448, 2), (key247, 2)]

def rawRow3738 : Integer.Sparse Key := [(key384, -6), (key393, 2), (key301, 2), (key384, 2), (key405, 6), (key416, -2), (key235, -2), (key405, -2), (key438, -2), (key315, -2), (key434, -2), (key448, 2), (key247, 2), (key434, 2)]

def rawRow3739 : Integer.Sparse Key := [(key384, -6), (key393, 2), (key384, 2), (key301, 2), (key405, 6), (key416, -2), (key405, -2), (key235, -2), (key438, -2), (key434, -2), (key315, -2), (key448, 2), (key434, 2), (key247, 2)]

def rawRow3740 : Integer.Sparse Key := [(key393, -6), (key301, 2), (key384, 2), (key384, 2), (key416, 6), (key235, -2), (key405, -2), (key405, -2), (key326, -2), (key448, -2), (key448, -2), (key256, 2), (key438, 2), (key438, 2)]

def rawRow3741 : Integer.Sparse Key := [(key393, -6), (key384, 2), (key301, 2), (key384, 2), (key416, 6), (key405, -2), (key235, -2), (key405, -2), (key448, -2), (key326, -2), (key448, -2), (key438, 2), (key256, 2), (key438, 2)]

def rawRow3742 : Integer.Sparse Key := [(key393, -6), (key384, 2), (key384, 2), (key301, 2), (key416, 6), (key405, -2), (key405, -2), (key235, -2), (key448, -2), (key448, -2), (key326, -2), (key438, 2), (key438, 2), (key256, 2)]

def rawRow3743 : Integer.Sparse Key := [(key405, -6), (key315, 2), (key434, 2), (key438, 2), (key384, 6), (key247, -2), (key434, -2), (key448, -2), (key301, -2), (key384, -2), (key393, -2), (key235, 2), (key405, 2), (key416, 2)]

def rawRow3744 : Integer.Sparse Key := [(key405, -6), (key315, 2), (key438, 2), (key434, 2), (key384, 6), (key247, -2), (key448, -2), (key434, -2), (key301, -2), (key393, -2), (key384, -2), (key235, 2), (key416, 2), (key405, 2)]

def rawRow3745 : Integer.Sparse Key := [(key405, -6), (key434, 2), (key315, 2), (key438, 2), (key384, 6), (key434, -2), (key247, -2), (key448, -2), (key384, -2), (key301, -2), (key393, -2), (key405, 2), (key235, 2), (key416, 2)]

def rawRow3746 : Integer.Sparse Key := [(key405, -6), (key434, 2), (key438, 2), (key315, 2), (key384, 6), (key434, -2), (key448, -2), (key247, -2), (key384, -2), (key393, -2), (key301, -2), (key405, 2), (key416, 2), (key235, 2)]

def rawRow3747 : Integer.Sparse Key := [(key405, -6), (key438, 2), (key315, 2), (key434, 2), (key384, 6), (key448, -2), (key247, -2), (key434, -2), (key393, -2), (key301, -2), (key384, -2), (key416, 2), (key235, 2), (key405, 2)]

def rawRow3748 : Integer.Sparse Key := [(key405, -6), (key438, 2), (key434, 2), (key315, 2), (key384, 6), (key448, -2), (key434, -2), (key247, -2), (key393, -2), (key384, -2), (key301, -2), (key416, 2), (key405, 2), (key235, 2)]

def rawRow3749 : Integer.Sparse Key := [(key438, -6), (key315, 2), (key405, 2), (key434, 2), (key448, 6), (key247, -2), (key384, -2), (key434, -2), (key326, -2), (key416, -2), (key448, -2), (key256, 2), (key393, 2), (key438, 2)]

def rawRow3750 : Integer.Sparse Key := [(key438, -6), (key315, 2), (key434, 2), (key405, 2), (key448, 6), (key247, -2), (key434, -2), (key384, -2), (key326, -2), (key448, -2), (key416, -2), (key256, 2), (key438, 2), (key393, 2)]

def rawRow3751 : Integer.Sparse Key := [(key438, -6), (key405, 2), (key315, 2), (key434, 2), (key448, 6), (key384, -2), (key247, -2), (key434, -2), (key416, -2), (key326, -2), (key448, -2), (key393, 2), (key256, 2), (key438, 2)]

def rawRow3752 : Integer.Sparse Key := [(key438, -6), (key405, 2), (key434, 2), (key315, 2), (key448, 6), (key384, -2), (key434, -2), (key247, -2), (key416, -2), (key448, -2), (key326, -2), (key393, 2), (key438, 2), (key256, 2)]

def rawRow3753 : Integer.Sparse Key := [(key438, -6), (key434, 2), (key315, 2), (key405, 2), (key448, 6), (key434, -2), (key247, -2), (key384, -2), (key448, -2), (key326, -2), (key416, -2), (key438, 2), (key256, 2), (key393, 2)]

def rawRow3754 : Integer.Sparse Key := [(key438, -6), (key434, 2), (key405, 2), (key315, 2), (key448, 6), (key434, -2), (key384, -2), (key247, -2), (key448, -2), (key416, -2), (key326, -2), (key438, 2), (key393, 2), (key256, 2)]

def rawRow3755 : Integer.Sparse Key := [(key416, -6), (key326, 2), (key448, 2), (key448, 2), (key393, 6), (key256, -2), (key438, -2), (key438, -2), (key301, -2), (key384, -2), (key384, -2), (key235, 2), (key405, 2), (key405, 2)]

def rawRow3756 : Integer.Sparse Key := [(key416, -6), (key448, 2), (key326, 2), (key448, 2), (key393, 6), (key438, -2), (key256, -2), (key438, -2), (key384, -2), (key301, -2), (key384, -2), (key405, 2), (key235, 2), (key405, 2)]

def rawRow3757 : Integer.Sparse Key := [(key416, -6), (key448, 2), (key448, 2), (key326, 2), (key393, 6), (key438, -2), (key438, -2), (key256, -2), (key384, -2), (key384, -2), (key301, -2), (key405, 2), (key405, 2), (key235, 2)]

def rawRow3758 : Integer.Sparse Key := [(key448, -6), (key326, 2), (key416, 2), (key448, 2), (key438, 6), (key256, -2), (key393, -2), (key438, -2), (key315, -2), (key405, -2), (key434, -2), (key247, 2), (key384, 2), (key434, 2)]

def rawRow3759 : Integer.Sparse Key := [(key448, -6), (key326, 2), (key448, 2), (key416, 2), (key438, 6), (key256, -2), (key438, -2), (key393, -2), (key315, -2), (key434, -2), (key405, -2), (key247, 2), (key434, 2), (key384, 2)]

def rawRow3760 : Integer.Sparse Key := [(key448, -6), (key416, 2), (key326, 2), (key448, 2), (key438, 6), (key393, -2), (key256, -2), (key438, -2), (key405, -2), (key315, -2), (key434, -2), (key384, 2), (key247, 2), (key434, 2)]

def rawRow3761 : Integer.Sparse Key := [(key448, -6), (key416, 2), (key448, 2), (key326, 2), (key438, 6), (key393, -2), (key438, -2), (key256, -2), (key405, -2), (key434, -2), (key315, -2), (key384, 2), (key434, 2), (key247, 2)]

def rawRow3762 : Integer.Sparse Key := [(key448, -6), (key448, 2), (key326, 2), (key416, 2), (key438, 6), (key438, -2), (key256, -2), (key393, -2), (key434, -2), (key315, -2), (key405, -2), (key434, 2), (key247, 2), (key384, 2)]

def rawRow3763 : Integer.Sparse Key := [(key448, -6), (key448, 2), (key416, 2), (key326, 2), (key438, 6), (key438, -2), (key393, -2), (key256, -2), (key434, -2), (key405, -2), (key315, -2), (key434, 2), (key384, 2), (key247, 2)]

def rawRow3764 : Integer.Sparse Key := [(key1542, -2), (key1548, -2), (key1896, -2), (key1387, 1), (key1393, 1), (key1542, 1), (key1556, 1), (key1896, 1), (key1899, 1), (key1569, 2), (key1575, 2), (key1903, 2), (key1292, -1), (key1298, -1), (key1569, -1), (key1593, -1), (key1903, -1), (key1911, -1), (key1420, -1), (key1426, -1), (key1618, -1), (key1624, -1), (key1918, -1), (key1920, -1), (key1312, 1), (key1318, 1), (key1618, 1), (key1633, 1), (key1918, 1), (key1926, 1)]

def rawRow3765 : Integer.Sparse Key := [(key1548, -2), (key1542, -2), (key1896, -2), (key1393, 1), (key1387, 1), (key1556, 1), (key1542, 1), (key1899, 1), (key1896, 1), (key1575, 2), (key1569, 2), (key1903, 2), (key1298, -1), (key1292, -1), (key1593, -1), (key1569, -1), (key1911, -1), (key1903, -1), (key1426, -1), (key1420, -1), (key1624, -1), (key1618, -1), (key1920, -1), (key1918, -1), (key1318, 1), (key1312, 1), (key1633, 1), (key1618, 1), (key1926, 1), (key1918, 1)]

def rawRow3766 : Integer.Sparse Key := [(key1542, -2), (key1896, -2), (key1548, -2), (key1542, 1), (key1896, 1), (key1387, 1), (key1899, 1), (key1393, 1), (key1556, 1), (key1569, 2), (key1903, 2), (key1575, 2), (key1569, -1), (key1903, -1), (key1292, -1), (key1911, -1), (key1298, -1), (key1593, -1), (key1618, -1), (key1918, -1), (key1420, -1), (key1920, -1), (key1426, -1), (key1624, -1), (key1618, 1), (key1918, 1), (key1312, 1), (key1926, 1), (key1318, 1), (key1633, 1)]

def rawRow3767 : Integer.Sparse Key := [(key1896, -2), (key1542, -2), (key1548, -2), (key1896, 1), (key1542, 1), (key1899, 1), (key1387, 1), (key1556, 1), (key1393, 1), (key1903, 2), (key1569, 2), (key1575, 2), (key1903, -1), (key1569, -1), (key1911, -1), (key1292, -1), (key1593, -1), (key1298, -1), (key1918, -1), (key1618, -1), (key1920, -1), (key1420, -1), (key1624, -1), (key1426, -1), (key1918, 1), (key1618, 1), (key1926, 1), (key1312, 1), (key1633, 1), (key1318, 1)]

def rawRow3768 : Integer.Sparse Key := [(key1548, -2), (key1896, -2), (key1542, -2), (key1556, 1), (key1899, 1), (key1393, 1), (key1896, 1), (key1387, 1), (key1542, 1), (key1575, 2), (key1903, 2), (key1569, 2), (key1593, -1), (key1911, -1), (key1298, -1), (key1903, -1), (key1292, -1), (key1569, -1), (key1624, -1), (key1920, -1), (key1426, -1), (key1918, -1), (key1420, -1), (key1618, -1), (key1633, 1), (key1926, 1), (key1318, 1), (key1918, 1), (key1312, 1), (key1618, 1)]

def rawRow3769 : Integer.Sparse Key := [(key1896, -2), (key1548, -2), (key1542, -2), (key1899, 1), (key1556, 1), (key1896, 1), (key1393, 1), (key1542, 1), (key1387, 1), (key1903, 2), (key1575, 2), (key1569, 2), (key1911, -1), (key1593, -1), (key1903, -1), (key1298, -1), (key1569, -1), (key1292, -1), (key1920, -1), (key1624, -1), (key1918, -1), (key1426, -1), (key1618, -1), (key1420, -1), (key1926, 1), (key1633, 1), (key1918, 1), (key1318, 1), (key1618, 1), (key1312, 1)]

def rawRow3773 : Integer.Sparse Key := [(key1569, -2), (key1575, -2), (key1903, -2), (key1420, 1), (key1426, 1), (key1618, 1), (key1624, 1), (key1918, 1), (key1920, 1), (key1542, 2), (key1548, 2), (key1896, 2), (key1312, -1), (key1318, -1), (key1618, -1), (key1633, -1), (key1918, -1), (key1926, -1), (key1387, -1), (key1393, -1), (key1542, -1), (key1556, -1), (key1896, -1), (key1899, -1), (key1292, 1), (key1298, 1), (key1569, 1), (key1593, 1), (key1903, 1), (key1911, 1)]

def rawRow3774 : Integer.Sparse Key := [(key1575, -2), (key1569, -2), (key1903, -2), (key1426, 1), (key1420, 1), (key1624, 1), (key1618, 1), (key1920, 1), (key1918, 1), (key1548, 2), (key1542, 2), (key1896, 2), (key1318, -1), (key1312, -1), (key1633, -1), (key1618, -1), (key1926, -1), (key1918, -1), (key1393, -1), (key1387, -1), (key1556, -1), (key1542, -1), (key1899, -1), (key1896, -1), (key1298, 1), (key1292, 1), (key1593, 1), (key1569, 1), (key1911, 1), (key1903, 1)]

def rawRow3775 : Integer.Sparse Key := [(key1569, -2), (key1903, -2), (key1575, -2), (key1618, 1), (key1918, 1), (key1420, 1), (key1920, 1), (key1426, 1), (key1624, 1), (key1542, 2), (key1896, 2), (key1548, 2), (key1618, -1), (key1918, -1), (key1312, -1), (key1926, -1), (key1318, -1), (key1633, -1), (key1542, -1), (key1896, -1), (key1387, -1), (key1899, -1), (key1393, -1), (key1556, -1), (key1569, 1), (key1903, 1), (key1292, 1), (key1911, 1), (key1298, 1), (key1593, 1)]

def rawRow3776 : Integer.Sparse Key := [(key1903, -2), (key1569, -2), (key1575, -2), (key1918, 1), (key1618, 1), (key1920, 1), (key1420, 1), (key1624, 1), (key1426, 1), (key1896, 2), (key1542, 2), (key1548, 2), (key1918, -1), (key1618, -1), (key1926, -1), (key1312, -1), (key1633, -1), (key1318, -1), (key1896, -1), (key1542, -1), (key1899, -1), (key1387, -1), (key1556, -1), (key1393, -1), (key1903, 1), (key1569, 1), (key1911, 1), (key1292, 1), (key1593, 1), (key1298, 1)]

def rawRow3777 : Integer.Sparse Key := [(key1575, -2), (key1903, -2), (key1569, -2), (key1624, 1), (key1920, 1), (key1426, 1), (key1918, 1), (key1420, 1), (key1618, 1), (key1548, 2), (key1896, 2), (key1542, 2), (key1633, -1), (key1926, -1), (key1318, -1), (key1918, -1), (key1312, -1), (key1618, -1), (key1556, -1), (key1899, -1), (key1393, -1), (key1896, -1), (key1387, -1), (key1542, -1), (key1593, 1), (key1911, 1), (key1298, 1), (key1903, 1), (key1292, 1), (key1569, 1)]

def rawRow3778 : Integer.Sparse Key := [(key1903, -2), (key1575, -2), (key1569, -2), (key1920, 1), (key1624, 1), (key1918, 1), (key1426, 1), (key1618, 1), (key1420, 1), (key1896, 2), (key1548, 2), (key1542, 2), (key1926, -1), (key1633, -1), (key1918, -1), (key1318, -1), (key1618, -1), (key1312, -1), (key1899, -1), (key1556, -1), (key1896, -1), (key1393, -1), (key1542, -1), (key1387, -1), (key1911, 1), (key1593, 1), (key1903, 1), (key1298, 1), (key1569, 1), (key1292, 1)]

def rawRow3779 : Integer.Sparse Key := [(key1624, -2), (key1683, -2), (key1920, -2), (key1426, 1), (key1472, 1), (key1575, 1), (key1681, 1), (key1903, 1), (key1918, 1), (key1633, 2), (key1689, 2), (key1926, 2), (key1318, -1), (key1351, -1), (key1548, -1), (key1681, -1), (key1896, -1), (key1918, -1), (key1444, -1), (key1480, -1), (key1593, -1), (key1689, -1), (key1911, -1), (key1926, -1), (key1326, 1), (key1354, 1), (key1556, 1), (key1683, 1), (key1899, 1), (key1920, 1)]

def rawRow3780 : Integer.Sparse Key := [(key1683, -2), (key1624, -2), (key1920, -2), (key1472, 1), (key1426, 1), (key1681, 1), (key1575, 1), (key1918, 1), (key1903, 1), (key1689, 2), (key1633, 2), (key1926, 2), (key1351, -1), (key1318, -1), (key1681, -1), (key1548, -1), (key1918, -1), (key1896, -1), (key1480, -1), (key1444, -1), (key1689, -1), (key1593, -1), (key1926, -1), (key1911, -1), (key1354, 1), (key1326, 1), (key1683, 1), (key1556, 1), (key1920, 1), (key1899, 1)]

def rawRow3781 : Integer.Sparse Key := [(key1624, -2), (key1920, -2), (key1683, -2), (key1575, 1), (key1903, 1), (key1426, 1), (key1918, 1), (key1472, 1), (key1681, 1), (key1633, 2), (key1926, 2), (key1689, 2), (key1548, -1), (key1896, -1), (key1318, -1), (key1918, -1), (key1351, -1), (key1681, -1), (key1593, -1), (key1911, -1), (key1444, -1), (key1926, -1), (key1480, -1), (key1689, -1), (key1556, 1), (key1899, 1), (key1326, 1), (key1920, 1), (key1354, 1), (key1683, 1)]

def rawRow3782 : Integer.Sparse Key := [(key1920, -2), (key1624, -2), (key1683, -2), (key1903, 1), (key1575, 1), (key1918, 1), (key1426, 1), (key1681, 1), (key1472, 1), (key1926, 2), (key1633, 2), (key1689, 2), (key1896, -1), (key1548, -1), (key1918, -1), (key1318, -1), (key1681, -1), (key1351, -1), (key1911, -1), (key1593, -1), (key1926, -1), (key1444, -1), (key1689, -1), (key1480, -1), (key1899, 1), (key1556, 1), (key1920, 1), (key1326, 1), (key1683, 1), (key1354, 1)]

def rawRow3783 : Integer.Sparse Key := [(key1683, -2), (key1920, -2), (key1624, -2), (key1681, 1), (key1918, 1), (key1472, 1), (key1903, 1), (key1426, 1), (key1575, 1), (key1689, 2), (key1926, 2), (key1633, 2), (key1681, -1), (key1918, -1), (key1351, -1), (key1896, -1), (key1318, -1), (key1548, -1), (key1689, -1), (key1926, -1), (key1480, -1), (key1911, -1), (key1444, -1), (key1593, -1), (key1683, 1), (key1920, 1), (key1354, 1), (key1899, 1), (key1326, 1), (key1556, 1)]

def rawRow3784 : Integer.Sparse Key := [(key1920, -2), (key1683, -2), (key1624, -2), (key1918, 1), (key1681, 1), (key1903, 1), (key1472, 1), (key1575, 1), (key1426, 1), (key1926, 2), (key1689, 2), (key1633, 2), (key1918, -1), (key1681, -1), (key1896, -1), (key1351, -1), (key1548, -1), (key1318, -1), (key1926, -1), (key1689, -1), (key1911, -1), (key1480, -1), (key1593, -1), (key1444, -1), (key1920, 1), (key1683, 1), (key1899, 1), (key1354, 1), (key1556, 1), (key1326, 1)]

def rawRow3788 : Integer.Sparse Key := [(key1633, -2), (key1689, -2), (key1926, -2), (key1444, 1), (key1480, 1), (key1593, 1), (key1689, 1), (key1911, 1), (key1926, 1), (key1624, 2), (key1683, 2), (key1920, 2), (key1326, -1), (key1354, -1), (key1556, -1), (key1683, -1), (key1899, -1), (key1920, -1), (key1426, -1), (key1472, -1), (key1575, -1), (key1681, -1), (key1903, -1), (key1918, -1), (key1318, 1), (key1351, 1), (key1548, 1), (key1681, 1), (key1896, 1), (key1918, 1)]

def rawRow3789 : Integer.Sparse Key := [(key1689, -2), (key1633, -2), (key1926, -2), (key1480, 1), (key1444, 1), (key1689, 1), (key1593, 1), (key1926, 1), (key1911, 1), (key1683, 2), (key1624, 2), (key1920, 2), (key1354, -1), (key1326, -1), (key1683, -1), (key1556, -1), (key1920, -1), (key1899, -1), (key1472, -1), (key1426, -1), (key1681, -1), (key1575, -1), (key1918, -1), (key1903, -1), (key1351, 1), (key1318, 1), (key1681, 1), (key1548, 1), (key1918, 1), (key1896, 1)]

def rawRow3790 : Integer.Sparse Key := [(key1633, -2), (key1926, -2), (key1689, -2), (key1593, 1), (key1911, 1), (key1444, 1), (key1926, 1), (key1480, 1), (key1689, 1), (key1624, 2), (key1920, 2), (key1683, 2), (key1556, -1), (key1899, -1), (key1326, -1), (key1920, -1), (key1354, -1), (key1683, -1), (key1575, -1), (key1903, -1), (key1426, -1), (key1918, -1), (key1472, -1), (key1681, -1), (key1548, 1), (key1896, 1), (key1318, 1), (key1918, 1), (key1351, 1), (key1681, 1)]

def rawRow3791 : Integer.Sparse Key := [(key1926, -2), (key1633, -2), (key1689, -2), (key1911, 1), (key1593, 1), (key1926, 1), (key1444, 1), (key1689, 1), (key1480, 1), (key1920, 2), (key1624, 2), (key1683, 2), (key1899, -1), (key1556, -1), (key1920, -1), (key1326, -1), (key1683, -1), (key1354, -1), (key1903, -1), (key1575, -1), (key1918, -1), (key1426, -1), (key1681, -1), (key1472, -1), (key1896, 1), (key1548, 1), (key1918, 1), (key1318, 1), (key1681, 1), (key1351, 1)]

def rawRow3792 : Integer.Sparse Key := [(key1689, -2), (key1926, -2), (key1633, -2), (key1689, 1), (key1926, 1), (key1480, 1), (key1911, 1), (key1444, 1), (key1593, 1), (key1683, 2), (key1920, 2), (key1624, 2), (key1683, -1), (key1920, -1), (key1354, -1), (key1899, -1), (key1326, -1), (key1556, -1), (key1681, -1), (key1918, -1), (key1472, -1), (key1903, -1), (key1426, -1), (key1575, -1), (key1681, 1), (key1918, 1), (key1351, 1), (key1896, 1), (key1318, 1), (key1548, 1)]

def rawRow3793 : Integer.Sparse Key := [(key1926, -2), (key1689, -2), (key1633, -2), (key1926, 1), (key1689, 1), (key1911, 1), (key1480, 1), (key1593, 1), (key1444, 1), (key1920, 2), (key1683, 2), (key1624, 2), (key1920, -1), (key1683, -1), (key1899, -1), (key1354, -1), (key1556, -1), (key1326, -1), (key1918, -1), (key1681, -1), (key1903, -1), (key1472, -1), (key1575, -1), (key1426, -1), (key1918, 1), (key1681, 1), (key1896, 1), (key1351, 1), (key1548, 1), (key1318, 1)]

def rawRow3794 : Integer.Sparse Key := [(key44, -2), (key47, -2), (key73, -2), (key47, 6), (key101, 2), (key104, 2), (key136, 2), (key22, -2), (key104, -2), (key172, -2), (key114, -6), (key34, 2), (key114, 2), (key176, 2)]

def rawRow3795 : Integer.Sparse Key := [(key47, -2), (key44, -2), (key73, -2), (key47, 6), (key104, 2), (key101, 2), (key136, 2), (key22, -2), (key172, -2), (key104, -2), (key114, -6), (key34, 2), (key176, 2), (key114, 2)]

def rawRow3796 : Integer.Sparse Key := [(key44, -2), (key73, -2), (key47, -2), (key47, 6), (key101, 2), (key136, 2), (key104, 2), (key104, -2), (key22, -2), (key172, -2), (key114, -6), (key114, 2), (key34, 2), (key176, 2)]

def rawRow3797 : Integer.Sparse Key := [(key73, -2), (key44, -2), (key47, -2), (key47, 6), (key136, 2), (key101, 2), (key104, 2), (key104, -2), (key172, -2), (key22, -2), (key114, -6), (key114, 2), (key176, 2), (key34, 2)]

def rawRow3798 : Integer.Sparse Key := [(key47, -2), (key73, -2), (key44, -2), (key47, 6), (key104, 2), (key136, 2), (key101, 2), (key172, -2), (key22, -2), (key104, -2), (key114, -6), (key176, 2), (key34, 2), (key114, 2)]

def rawRow3799 : Integer.Sparse Key := [(key73, -2), (key47, -2), (key44, -2), (key47, 6), (key136, 2), (key104, 2), (key101, 2), (key172, -2), (key104, -2), (key22, -2), (key114, -6), (key176, 2), (key114, 2), (key34, 2)]

def rawRow3800 : Integer.Sparse Key := [(key47, -2), (key47, -2), (key73, -2), (key44, 6), (key172, 2), (key172, 2), (key181, 2), (key19, -2), (key101, -2), (key101, -2), (key176, -6), (key34, 2), (key114, 2), (key114, 2)]

def rawRow3801 : Integer.Sparse Key := [(key47, -2), (key73, -2), (key47, -2), (key44, 6), (key172, 2), (key181, 2), (key172, 2), (key101, -2), (key19, -2), (key101, -2), (key176, -6), (key114, 2), (key34, 2), (key114, 2)]

def rawRow3802 : Integer.Sparse Key := [(key73, -2), (key47, -2), (key47, -2), (key44, 6), (key181, 2), (key172, 2), (key172, 2), (key101, -2), (key101, -2), (key19, -2), (key176, -6), (key114, 2), (key114, 2), (key34, 2)]

def rawRow3803 : Integer.Sparse Key := [(key101, -2), (key104, -2), (key136, -2), (key114, 6), (key44, 2), (key47, 2), (key73, 2), (key34, -2), (key114, -2), (key176, -2), (key47, -6), (key22, 2), (key104, 2), (key172, 2)]

def rawRow3804 : Integer.Sparse Key := [(key104, -2), (key101, -2), (key136, -2), (key114, 6), (key47, 2), (key44, 2), (key73, 2), (key34, -2), (key176, -2), (key114, -2), (key47, -6), (key22, 2), (key172, 2), (key104, 2)]

def rawRow3805 : Integer.Sparse Key := [(key101, -2), (key136, -2), (key104, -2), (key114, 6), (key44, 2), (key73, 2), (key47, 2), (key114, -2), (key34, -2), (key176, -2), (key47, -6), (key104, 2), (key22, 2), (key172, 2)]

def rawRow3806 : Integer.Sparse Key := [(key136, -2), (key101, -2), (key104, -2), (key114, 6), (key73, 2), (key44, 2), (key47, 2), (key114, -2), (key176, -2), (key34, -2), (key47, -6), (key104, 2), (key172, 2), (key22, 2)]

def rawRow3807 : Integer.Sparse Key := [(key104, -2), (key136, -2), (key101, -2), (key114, 6), (key47, 2), (key73, 2), (key44, 2), (key176, -2), (key34, -2), (key114, -2), (key47, -6), (key172, 2), (key22, 2), (key104, 2)]

def rawRow3808 : Integer.Sparse Key := [(key136, -2), (key104, -2), (key101, -2), (key114, 6), (key73, 2), (key47, 2), (key44, 2), (key176, -2), (key114, -2), (key34, -2), (key47, -6), (key172, 2), (key104, 2), (key22, 2)]

def rawRow3809 : Integer.Sparse Key := [(key104, -2), (key114, -2), (key136, -2), (key101, 6), (key172, 2), (key176, 2), (key181, 2), (key19, -2), (key44, -2), (key101, -2), (key172, -6), (key22, 2), (key47, 2), (key104, 2)]

def rawRow3810 : Integer.Sparse Key := [(key114, -2), (key104, -2), (key136, -2), (key101, 6), (key176, 2), (key172, 2), (key181, 2), (key19, -2), (key101, -2), (key44, -2), (key172, -6), (key22, 2), (key104, 2), (key47, 2)]

def rawRow3811 : Integer.Sparse Key := [(key104, -2), (key136, -2), (key114, -2), (key101, 6), (key172, 2), (key181, 2), (key176, 2), (key44, -2), (key19, -2), (key101, -2), (key172, -6), (key47, 2), (key22, 2), (key104, 2)]

def rawRow3812 : Integer.Sparse Key := [(key136, -2), (key104, -2), (key114, -2), (key101, 6), (key181, 2), (key172, 2), (key176, 2), (key44, -2), (key101, -2), (key19, -2), (key172, -6), (key47, 2), (key104, 2), (key22, 2)]

def rawRow3813 : Integer.Sparse Key := [(key114, -2), (key136, -2), (key104, -2), (key101, 6), (key176, 2), (key181, 2), (key172, 2), (key101, -2), (key19, -2), (key44, -2), (key172, -6), (key104, 2), (key22, 2), (key47, 2)]

def rawRow3814 : Integer.Sparse Key := [(key136, -2), (key114, -2), (key104, -2), (key101, 6), (key181, 2), (key176, 2), (key172, 2), (key101, -2), (key44, -2), (key19, -2), (key172, -6), (key104, 2), (key47, 2), (key22, 2)]

def rawRow3815 : Integer.Sparse Key := [(key172, -2), (key172, -2), (key181, -2), (key176, 6), (key47, 2), (key47, 2), (key73, 2), (key34, -2), (key114, -2), (key114, -2), (key44, -6), (key19, 2), (key101, 2), (key101, 2)]

def rawRow3816 : Integer.Sparse Key := [(key172, -2), (key181, -2), (key172, -2), (key176, 6), (key47, 2), (key73, 2), (key47, 2), (key114, -2), (key34, -2), (key114, -2), (key44, -6), (key101, 2), (key19, 2), (key101, 2)]

def rawRow3817 : Integer.Sparse Key := [(key181, -2), (key172, -2), (key172, -2), (key176, 6), (key73, 2), (key47, 2), (key47, 2), (key114, -2), (key114, -2), (key34, -2), (key44, -6), (key101, 2), (key101, 2), (key19, 2)]

def rawRow3818 : Integer.Sparse Key := [(key172, -2), (key176, -2), (key181, -2), (key172, 6), (key104, 2), (key114, 2), (key136, 2), (key22, -2), (key47, -2), (key104, -2), (key101, -6), (key19, 2), (key44, 2), (key101, 2)]

def rawRow3819 : Integer.Sparse Key := [(key176, -2), (key172, -2), (key181, -2), (key172, 6), (key114, 2), (key104, 2), (key136, 2), (key22, -2), (key104, -2), (key47, -2), (key101, -6), (key19, 2), (key101, 2), (key44, 2)]

def rawRow3820 : Integer.Sparse Key := [(key172, -2), (key181, -2), (key176, -2), (key172, 6), (key104, 2), (key136, 2), (key114, 2), (key47, -2), (key22, -2), (key104, -2), (key101, -6), (key44, 2), (key19, 2), (key101, 2)]

def rawRow3821 : Integer.Sparse Key := [(key181, -2), (key172, -2), (key176, -2), (key172, 6), (key136, 2), (key104, 2), (key114, 2), (key47, -2), (key104, -2), (key22, -2), (key101, -6), (key44, 2), (key101, 2), (key19, 2)]

def rawRow3822 : Integer.Sparse Key := [(key176, -2), (key181, -2), (key172, -2), (key172, 6), (key114, 2), (key136, 2), (key104, 2), (key104, -2), (key22, -2), (key47, -2), (key101, -6), (key101, 2), (key19, 2), (key44, 2)]

def rawRow3823 : Integer.Sparse Key := [(key181, -2), (key176, -2), (key172, -2), (key172, 6), (key136, 2), (key114, 2), (key104, 2), (key104, -2), (key47, -2), (key22, -2), (key101, -6), (key101, 2), (key44, 2), (key19, 2)]

def rawRow3824 : Integer.Sparse Key := [(key1540, -6), (key1385, 2), (key1540, 2), (key1552, 2), (key1567, 6), (key1290, -2), (key1567, -2), (key1589, -2), (key1418, -2), (key1616, -2), (key1620, -2), (key1310, 2), (key1616, 2), (key1629, 2)]

def rawRow3825 : Integer.Sparse Key := [(key1540, -6), (key1385, 2), (key1552, 2), (key1540, 2), (key1567, 6), (key1290, -2), (key1589, -2), (key1567, -2), (key1418, -2), (key1620, -2), (key1616, -2), (key1310, 2), (key1629, 2), (key1616, 2)]

def rawRow3826 : Integer.Sparse Key := [(key1540, -6), (key1540, 2), (key1385, 2), (key1552, 2), (key1567, 6), (key1567, -2), (key1290, -2), (key1589, -2), (key1616, -2), (key1418, -2), (key1620, -2), (key1616, 2), (key1310, 2), (key1629, 2)]

def rawRow3827 : Integer.Sparse Key := [(key1540, -6), (key1540, 2), (key1552, 2), (key1385, 2), (key1567, 6), (key1567, -2), (key1589, -2), (key1290, -2), (key1616, -2), (key1620, -2), (key1418, -2), (key1616, 2), (key1629, 2), (key1310, 2)]

def rawRow3828 : Integer.Sparse Key := [(key1540, -6), (key1552, 2), (key1385, 2), (key1540, 2), (key1567, 6), (key1589, -2), (key1290, -2), (key1567, -2), (key1620, -2), (key1418, -2), (key1616, -2), (key1629, 2), (key1310, 2), (key1616, 2)]

def rawRow3829 : Integer.Sparse Key := [(key1540, -6), (key1552, 2), (key1540, 2), (key1385, 2), (key1567, 6), (key1589, -2), (key1567, -2), (key1290, -2), (key1620, -2), (key1616, -2), (key1418, -2), (key1629, 2), (key1616, 2), (key1310, 2)]

def rawRow3830 : Integer.Sparse Key := [(key1552, -6), (key1385, 2), (key1540, 2), (key1540, 2), (key1589, 6), (key1290, -2), (key1567, -2), (key1567, -2), (key1440, -2), (key1629, -2), (key1629, -2), (key1322, 2), (key1620, 2), (key1620, 2)]

def rawRow3831 : Integer.Sparse Key := [(key1552, -6), (key1540, 2), (key1385, 2), (key1540, 2), (key1589, 6), (key1567, -2), (key1290, -2), (key1567, -2), (key1629, -2), (key1440, -2), (key1629, -2), (key1620, 2), (key1322, 2), (key1620, 2)]

def rawRow3832 : Integer.Sparse Key := [(key1552, -6), (key1540, 2), (key1540, 2), (key1385, 2), (key1589, 6), (key1567, -2), (key1567, -2), (key1290, -2), (key1629, -2), (key1629, -2), (key1440, -2), (key1620, 2), (key1620, 2), (key1322, 2)]

def rawRow3833 : Integer.Sparse Key := [(key1567, -6), (key1418, 2), (key1616, 2), (key1620, 2), (key1540, 6), (key1310, -2), (key1616, -2), (key1629, -2), (key1385, -2), (key1540, -2), (key1552, -2), (key1290, 2), (key1567, 2), (key1589, 2)]

def rawRow3834 : Integer.Sparse Key := [(key1567, -6), (key1418, 2), (key1620, 2), (key1616, 2), (key1540, 6), (key1310, -2), (key1629, -2), (key1616, -2), (key1385, -2), (key1552, -2), (key1540, -2), (key1290, 2), (key1589, 2), (key1567, 2)]

def rawRow3835 : Integer.Sparse Key := [(key1567, -6), (key1616, 2), (key1418, 2), (key1620, 2), (key1540, 6), (key1616, -2), (key1310, -2), (key1629, -2), (key1540, -2), (key1385, -2), (key1552, -2), (key1567, 2), (key1290, 2), (key1589, 2)]

def rawRow3836 : Integer.Sparse Key := [(key1567, -6), (key1616, 2), (key1620, 2), (key1418, 2), (key1540, 6), (key1616, -2), (key1629, -2), (key1310, -2), (key1540, -2), (key1552, -2), (key1385, -2), (key1567, 2), (key1589, 2), (key1290, 2)]

def rawRow3837 : Integer.Sparse Key := [(key1567, -6), (key1620, 2), (key1418, 2), (key1616, 2), (key1540, 6), (key1629, -2), (key1310, -2), (key1616, -2), (key1552, -2), (key1385, -2), (key1540, -2), (key1589, 2), (key1290, 2), (key1567, 2)]

def rawRow3838 : Integer.Sparse Key := [(key1567, -6), (key1620, 2), (key1616, 2), (key1418, 2), (key1540, 6), (key1629, -2), (key1616, -2), (key1310, -2), (key1552, -2), (key1540, -2), (key1385, -2), (key1589, 2), (key1567, 2), (key1290, 2)]

def rawRow3839 : Integer.Sparse Key := [(key1620, -6), (key1418, 2), (key1567, 2), (key1616, 2), (key1629, 6), (key1310, -2), (key1540, -2), (key1616, -2), (key1440, -2), (key1589, -2), (key1629, -2), (key1322, 2), (key1552, 2), (key1620, 2)]

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

def rawRow3840 : Integer.Sparse Key := [(key1620, -6), (key1418, 2), (key1616, 2), (key1567, 2), (key1629, 6), (key1310, -2), (key1616, -2), (key1540, -2), (key1440, -2), (key1629, -2), (key1589, -2), (key1322, 2), (key1620, 2), (key1552, 2)]

def rawRow3841 : Integer.Sparse Key := [(key1620, -6), (key1567, 2), (key1418, 2), (key1616, 2), (key1629, 6), (key1540, -2), (key1310, -2), (key1616, -2), (key1589, -2), (key1440, -2), (key1629, -2), (key1552, 2), (key1322, 2), (key1620, 2)]

def rawRow3842 : Integer.Sparse Key := [(key1620, -6), (key1567, 2), (key1616, 2), (key1418, 2), (key1629, 6), (key1540, -2), (key1616, -2), (key1310, -2), (key1589, -2), (key1629, -2), (key1440, -2), (key1552, 2), (key1620, 2), (key1322, 2)]

def rawRow3843 : Integer.Sparse Key := [(key1620, -6), (key1616, 2), (key1418, 2), (key1567, 2), (key1629, 6), (key1616, -2), (key1310, -2), (key1540, -2), (key1629, -2), (key1440, -2), (key1589, -2), (key1620, 2), (key1322, 2), (key1552, 2)]

def rawRow3844 : Integer.Sparse Key := [(key1620, -6), (key1616, 2), (key1567, 2), (key1418, 2), (key1629, 6), (key1616, -2), (key1540, -2), (key1310, -2), (key1629, -2), (key1589, -2), (key1440, -2), (key1620, 2), (key1552, 2), (key1322, 2)]

def rawRow3845 : Integer.Sparse Key := [(key1589, -6), (key1440, 2), (key1629, 2), (key1629, 2), (key1552, 6), (key1322, -2), (key1620, -2), (key1620, -2), (key1385, -2), (key1540, -2), (key1540, -2), (key1290, 2), (key1567, 2), (key1567, 2)]

def rawRow3846 : Integer.Sparse Key := [(key1589, -6), (key1629, 2), (key1440, 2), (key1629, 2), (key1552, 6), (key1620, -2), (key1322, -2), (key1620, -2), (key1540, -2), (key1385, -2), (key1540, -2), (key1567, 2), (key1290, 2), (key1567, 2)]

def rawRow3847 : Integer.Sparse Key := [(key1589, -6), (key1629, 2), (key1629, 2), (key1440, 2), (key1552, 6), (key1620, -2), (key1620, -2), (key1322, -2), (key1540, -2), (key1540, -2), (key1385, -2), (key1567, 2), (key1567, 2), (key1290, 2)]

def rawRow3848 : Integer.Sparse Key := [(key1629, -6), (key1440, 2), (key1589, 2), (key1629, 2), (key1620, 6), (key1322, -2), (key1552, -2), (key1620, -2), (key1418, -2), (key1567, -2), (key1616, -2), (key1310, 2), (key1540, 2), (key1616, 2)]

def rawRow3849 : Integer.Sparse Key := [(key1629, -6), (key1440, 2), (key1629, 2), (key1589, 2), (key1620, 6), (key1322, -2), (key1620, -2), (key1552, -2), (key1418, -2), (key1616, -2), (key1567, -2), (key1310, 2), (key1616, 2), (key1540, 2)]

def rawRow3850 : Integer.Sparse Key := [(key1629, -6), (key1589, 2), (key1440, 2), (key1629, 2), (key1620, 6), (key1552, -2), (key1322, -2), (key1620, -2), (key1567, -2), (key1418, -2), (key1616, -2), (key1540, 2), (key1310, 2), (key1616, 2)]

def rawRow3851 : Integer.Sparse Key := [(key1629, -6), (key1589, 2), (key1629, 2), (key1440, 2), (key1620, 6), (key1552, -2), (key1620, -2), (key1322, -2), (key1567, -2), (key1616, -2), (key1418, -2), (key1540, 2), (key1616, 2), (key1310, 2)]

def rawRow3852 : Integer.Sparse Key := [(key1629, -6), (key1629, 2), (key1440, 2), (key1589, 2), (key1620, 6), (key1620, -2), (key1322, -2), (key1552, -2), (key1616, -2), (key1418, -2), (key1567, -2), (key1616, 2), (key1310, 2), (key1540, 2)]

def rawRow3853 : Integer.Sparse Key := [(key1629, -6), (key1629, 2), (key1589, 2), (key1440, 2), (key1620, 6), (key1620, -2), (key1552, -2), (key1322, -2), (key1616, -2), (key1567, -2), (key1418, -2), (key1616, 2), (key1540, 2), (key1310, 2)]

def rawRow3854 : Integer.Sparse Key := [(key237, -1), (key240, -1), (key407, -1), (key579, -1), (key420, -1), (key585, -1), (key240, 2), (key410, 2), (key579, 2), (key249, 1), (key252, 1), (key436, 1), (key594, 1), (key452, 1), (key603, 1), (key252, -1), (key268, -1), (key389, -1), (key569, -1), (key468, -1), (key594, -1), (key262, -2), (key444, -2), (key597, -2), (key262, 1), (key273, 1), (key399, 1), (key574, 1), (key471, 1), (key597, 1)]

def rawRow3855 : Integer.Sparse Key := [(key240, -1), (key237, -1), (key579, -1), (key407, -1), (key585, -1), (key420, -1), (key240, 2), (key579, 2), (key410, 2), (key252, 1), (key249, 1), (key594, 1), (key436, 1), (key603, 1), (key452, 1), (key268, -1), (key252, -1), (key569, -1), (key389, -1), (key594, -1), (key468, -1), (key262, -2), (key597, -2), (key444, -2), (key273, 1), (key262, 1), (key574, 1), (key399, 1), (key597, 1), (key471, 1)]

def rawRow3856 : Integer.Sparse Key := [(key407, -1), (key420, -1), (key237, -1), (key585, -1), (key240, -1), (key579, -1), (key410, 2), (key240, 2), (key579, 2), (key436, 1), (key452, 1), (key249, 1), (key603, 1), (key252, 1), (key594, 1), (key389, -1), (key468, -1), (key252, -1), (key594, -1), (key268, -1), (key569, -1), (key444, -2), (key262, -2), (key597, -2), (key399, 1), (key471, 1), (key262, 1), (key597, 1), (key273, 1), (key574, 1)]

def rawRow3857 : Integer.Sparse Key := [(key420, -1), (key407, -1), (key585, -1), (key237, -1), (key579, -1), (key240, -1), (key410, 2), (key579, 2), (key240, 2), (key452, 1), (key436, 1), (key603, 1), (key249, 1), (key594, 1), (key252, 1), (key468, -1), (key389, -1), (key594, -1), (key252, -1), (key569, -1), (key268, -1), (key444, -2), (key597, -2), (key262, -2), (key471, 1), (key399, 1), (key597, 1), (key262, 1), (key574, 1), (key273, 1)]

def rawRow3858 : Integer.Sparse Key := [(key579, -1), (key585, -1), (key240, -1), (key420, -1), (key237, -1), (key407, -1), (key579, 2), (key240, 2), (key410, 2), (key594, 1), (key603, 1), (key252, 1), (key452, 1), (key249, 1), (key436, 1), (key569, -1), (key594, -1), (key268, -1), (key468, -1), (key252, -1), (key389, -1), (key597, -2), (key262, -2), (key444, -2), (key574, 1), (key597, 1), (key273, 1), (key471, 1), (key262, 1), (key399, 1)]

def rawRow3859 : Integer.Sparse Key := [(key585, -1), (key579, -1), (key420, -1), (key240, -1), (key407, -1), (key237, -1), (key579, 2), (key410, 2), (key240, 2), (key603, 1), (key594, 1), (key452, 1), (key252, 1), (key436, 1), (key249, 1), (key594, -1), (key569, -1), (key468, -1), (key268, -1), (key389, -1), (key252, -1), (key597, -2), (key444, -2), (key262, -2), (key597, 1), (key574, 1), (key471, 1), (key273, 1), (key399, 1), (key262, 1)]

def rawRow3863 : Integer.Sparse Key := [(key249, -1), (key252, -1), (key436, -1), (key594, -1), (key452, -1), (key603, -1), (key262, 2), (key444, 2), (key597, 2), (key237, 1), (key240, 1), (key407, 1), (key579, 1), (key420, 1), (key585, 1), (key262, -1), (key273, -1), (key399, -1), (key574, -1), (key471, -1), (key597, -1), (key240, -2), (key410, -2), (key579, -2), (key252, 1), (key268, 1), (key389, 1), (key569, 1), (key468, 1), (key594, 1)]

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

def rawRow3968 : Integer.Sparse Key := [(key171, -2), (key174, -2), (key179, -2), (key171, 6), (key103, 2), (key112, 2), (key134, 2), (key21, -2), (key46, -2), (key103, -2), (key100, -6), (key18, 2), (key375, 2), (key426, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow296 : Integer.Sparse Key := [(key1305, -2), (key1305, 1), (key1301, 1), (key1332, 2), (key1332, -1), (key1321, -1), (key1349, -1), (key1348, -1), (key1349, 1), (key1342, 1), (key1400, 2), (key1400, -1), (key1396, -1), (key1450, -2), (key1450, 1), (key1429, 1), (key1470, 1), (key1469, 1), (key1470, -1), (key1460, -1), (key1562, -2), (key1562, 1), (key1551, 1), (key1599, 2), (key1599, -1), (key1578, -1), (key1676, -1), (key1670, -1), (key1676, 1), (key1662, 1), (key1784, 1), (key1783, 1), (key1784, -1), (key1777, -1), (key1802, -1), (key1801, -1), (key1802, 1), (key1793, 1), (key1834, 1), (key1828, 1), (key1834, -1), (key1820, -1)]

def rawRow298 : Integer.Sparse Key := [(key1342, -2), (key1321, 1), (key1342, 1), (key1348, 2), (key1301, -1), (key1348, -1), (key1332, -1), (key1349, -1), (key1305, 1), (key1349, 1), (key1460, 2), (key1429, -1), (key1460, -1), (key1469, -2), (key1396, 1), (key1469, 1), (key1450, 1), (key1470, 1), (key1400, -1), (key1470, -1), (key1662, -2), (key1578, 1), (key1662, 1), (key1670, 2), (key1551, -1), (key1670, -1), (key1599, -1), (key1676, -1), (key1562, 1), (key1676, 1), (key1820, 1), (key1843, 1), (key1793, -1), (key1843, -1), (key1828, -1), (key1846, -1), (key1777, 1), (key1846, 1), (key1801, 1), (key1849, 1), (key1783, -1), (key1849, -1)]

def rawRow299 : Integer.Sparse Key := [(key1342, -2), (key1342, 1), (key1321, 1), (key1348, 2), (key1348, -1), (key1301, -1), (key1349, -1), (key1332, -1), (key1349, 1), (key1305, 1), (key1460, 2), (key1460, -1), (key1429, -1), (key1469, -2), (key1469, 1), (key1396, 1), (key1470, 1), (key1450, 1), (key1470, -1), (key1400, -1), (key1662, -2), (key1662, 1), (key1578, 1), (key1670, 2), (key1670, -1), (key1551, -1), (key1676, -1), (key1599, -1), (key1676, 1), (key1562, 1), (key1843, 1), (key1820, 1), (key1843, -1), (key1793, -1), (key1846, -1), (key1828, -1), (key1846, 1), (key1777, 1), (key1849, 1), (key1801, 1), (key1849, -1), (key1783, -1)]

def rawRow300 : Integer.Sparse Key := [(key1332, -2), (key1348, 1), (key1349, 1), (key1305, 2), (key1342, -1), (key1349, -1), (key1301, -1), (key1305, -1), (key1321, 1), (key1332, 1), (key1450, 2), (key1469, -1), (key1470, -1), (key1400, -2), (key1460, 1), (key1470, 1), (key1396, 1), (key1400, 1), (key1429, -1), (key1450, -1), (key1599, -2), (key1670, 1), (key1676, 1), (key1562, 2), (key1662, -1), (key1676, -1), (key1551, -1), (key1562, -1), (key1578, 1), (key1599, 1), (key1801, 1), (key1802, 1), (key1828, -1), (key1834, -1), (key1783, -1), (key1784, -1), (key1820, 1), (key1834, 1), (key1777, 1), (key1784, 1), (key1793, -1), (key1802, -1)]

def rawRow301 : Integer.Sparse Key := [(key1332, -2), (key1349, 1), (key1348, 1), (key1305, 2), (key1349, -1), (key1342, -1), (key1305, -1), (key1301, -1), (key1332, 1), (key1321, 1), (key1450, 2), (key1470, -1), (key1469, -1), (key1400, -2), (key1470, 1), (key1460, 1), (key1400, 1), (key1396, 1), (key1450, -1), (key1429, -1), (key1599, -2), (key1676, 1), (key1670, 1), (key1562, 2), (key1676, -1), (key1662, -1), (key1562, -1), (key1551, -1), (key1599, 1), (key1578, 1), (key1802, 1), (key1801, 1), (key1834, -1), (key1828, -1), (key1784, -1), (key1783, -1), (key1834, 1), (key1820, 1), (key1784, 1), (key1777, 1), (key1802, -1), (key1793, -1)]

def rawRow302 : Integer.Sparse Key := [(key1348, -2), (key1332, 1), (key1349, 1), (key1342, 2), (key1305, -1), (key1349, -1), (key1321, -1), (key1342, -1), (key1301, 1), (key1348, 1), (key1469, 2), (key1450, -1), (key1470, -1), (key1460, -2), (key1400, 1), (key1470, 1), (key1429, 1), (key1460, 1), (key1396, -1), (key1469, -1), (key1670, -2), (key1599, 1), (key1676, 1), (key1662, 2), (key1562, -1), (key1676, -1), (key1578, -1), (key1662, -1), (key1551, 1), (key1670, 1), (key1828, 1), (key1846, 1), (key1801, -1), (key1849, -1), (key1820, -1), (key1843, -1), (key1783, 1), (key1849, 1), (key1793, 1), (key1843, 1), (key1777, -1), (key1846, -1)]

def rawRow303 : Integer.Sparse Key := [(key1348, -2), (key1349, 1), (key1332, 1), (key1342, 2), (key1349, -1), (key1305, -1), (key1342, -1), (key1321, -1), (key1348, 1), (key1301, 1), (key1469, 2), (key1470, -1), (key1450, -1), (key1460, -2), (key1470, 1), (key1400, 1), (key1460, 1), (key1429, 1), (key1469, -1), (key1396, -1), (key1670, -2), (key1676, 1), (key1599, 1), (key1662, 2), (key1676, -1), (key1562, -1), (key1662, -1), (key1578, -1), (key1670, 1), (key1551, 1), (key1846, 1), (key1828, 1), (key1849, -1), (key1801, -1), (key1843, -1), (key1820, -1), (key1849, 1), (key1783, 1), (key1843, 1), (key1793, 1), (key1846, -1), (key1777, -1)]

def rawRow305 : Integer.Sparse Key := [(key1400, -2), (key1396, 1), (key1400, 1), (key1562, 2), (key1551, -1), (key1562, -1), (key1783, -1), (key1784, -1), (key1777, 1), (key1784, 1), (key1305, 2), (key1301, -1), (key1305, -1), (key1599, -2), (key1578, 1), (key1599, 1), (key1801, 1), (key1802, 1), (key1793, -1), (key1802, -1), (key1332, -2), (key1321, 1), (key1332, 1), (key1450, 2), (key1429, -1), (key1450, -1), (key1828, -1), (key1834, -1), (key1820, 1), (key1834, 1), (key1348, 1), (key1349, 1), (key1342, -1), (key1349, -1), (key1469, -1), (key1470, -1), (key1460, 1), (key1470, 1), (key1670, 1), (key1676, 1), (key1662, -1), (key1676, -1)]

def rawRow306 : Integer.Sparse Key := [(key1400, -2), (key1400, 1), (key1396, 1), (key1562, 2), (key1562, -1), (key1551, -1), (key1784, -1), (key1783, -1), (key1784, 1), (key1777, 1), (key1305, 2), (key1305, -1), (key1301, -1), (key1599, -2), (key1599, 1), (key1578, 1), (key1802, 1), (key1801, 1), (key1802, -1), (key1793, -1), (key1332, -2), (key1332, 1), (key1321, 1), (key1450, 2), (key1450, -1), (key1429, -1), (key1834, -1), (key1828, -1), (key1834, 1), (key1820, 1), (key1349, 1), (key1348, 1), (key1349, -1), (key1342, -1), (key1470, -1), (key1469, -1), (key1470, 1), (key1460, 1), (key1676, 1), (key1670, 1), (key1676, -1), (key1662, -1)]

def rawRow308 : Integer.Sparse Key := [(key1777, -2), (key1551, 1), (key1777, 1), (key1783, 2), (key1396, -1), (key1783, -1), (key1562, -1), (key1784, -1), (key1400, 1), (key1784, 1), (key1793, 2), (key1578, -1), (key1793, -1), (key1801, -2), (key1301, 1), (key1801, 1), (key1599, 1), (key1802, 1), (key1305, -1), (key1802, -1), (key1820, -2), (key1429, 1), (key1820, 1), (key1828, 2), (key1321, -1), (key1828, -1), (key1450, -1), (key1834, -1), (key1332, 1), (key1834, 1), (key1662, 1), (key1843, 1), (key1460, -1), (key1843, -1), (key1670, -1), (key1846, -1), (key1342, 1), (key1846, 1), (key1469, 1), (key1849, 1), (key1348, -1), (key1849, -1)]

def rawRow309 : Integer.Sparse Key := [(key1777, -2), (key1777, 1), (key1551, 1), (key1783, 2), (key1783, -1), (key1396, -1), (key1784, -1), (key1562, -1), (key1784, 1), (key1400, 1), (key1793, 2), (key1793, -1), (key1578, -1), (key1801, -2), (key1801, 1), (key1301, 1), (key1802, 1), (key1599, 1), (key1802, -1), (key1305, -1), (key1820, -2), (key1820, 1), (key1429, 1), (key1828, 2), (key1828, -1), (key1321, -1), (key1834, -1), (key1450, -1), (key1834, 1), (key1332, 1), (key1843, 1), (key1662, 1), (key1843, -1), (key1460, -1), (key1846, -1), (key1670, -1), (key1846, 1), (key1342, 1), (key1849, 1), (key1469, 1), (key1849, -1), (key1348, -1)]

def rawRow310 : Integer.Sparse Key := [(key1562, -2), (key1783, 1), (key1784, 1), (key1400, 2), (key1777, -1), (key1784, -1), (key1396, -1), (key1400, -1), (key1551, 1), (key1562, 1), (key1599, 2), (key1801, -1), (key1802, -1), (key1305, -2), (key1793, 1), (key1802, 1), (key1301, 1), (key1305, 1), (key1578, -1), (key1599, -1), (key1450, -2), (key1828, 1), (key1834, 1), (key1332, 2), (key1820, -1), (key1834, -1), (key1321, -1), (key1332, -1), (key1429, 1), (key1450, 1), (key1469, 1), (key1470, 1), (key1670, -1), (key1676, -1), (key1348, -1), (key1349, -1), (key1662, 1), (key1676, 1), (key1342, 1), (key1349, 1), (key1460, -1), (key1470, -1)]

def rawRow311 : Integer.Sparse Key := [(key1562, -2), (key1784, 1), (key1783, 1), (key1400, 2), (key1784, -1), (key1777, -1), (key1400, -1), (key1396, -1), (key1562, 1), (key1551, 1), (key1599, 2), (key1802, -1), (key1801, -1), (key1305, -2), (key1802, 1), (key1793, 1), (key1305, 1), (key1301, 1), (key1599, -1), (key1578, -1), (key1450, -2), (key1834, 1), (key1828, 1), (key1332, 2), (key1834, -1), (key1820, -1), (key1332, -1), (key1321, -1), (key1450, 1), (key1429, 1), (key1470, 1), (key1469, 1), (key1676, -1), (key1670, -1), (key1349, -1), (key1348, -1), (key1676, 1), (key1662, 1), (key1349, 1), (key1342, 1), (key1470, -1), (key1460, -1)]

def rawRow312 : Integer.Sparse Key := [(key1783, -2), (key1562, 1), (key1784, 1), (key1777, 2), (key1400, -1), (key1784, -1), (key1551, -1), (key1777, -1), (key1396, 1), (key1783, 1), (key1801, 2), (key1599, -1), (key1802, -1), (key1793, -2), (key1305, 1), (key1802, 1), (key1578, 1), (key1793, 1), (key1301, -1), (key1801, -1), (key1828, -2), (key1450, 1), (key1834, 1), (key1820, 2), (key1332, -1), (key1834, -1), (key1429, -1), (key1820, -1), (key1321, 1), (key1828, 1), (key1670, 1), (key1846, 1), (key1469, -1), (key1849, -1), (key1662, -1), (key1843, -1), (key1348, 1), (key1849, 1), (key1460, 1), (key1843, 1), (key1342, -1), (key1846, -1)]

def rawRow313 : Integer.Sparse Key := [(key1783, -2), (key1784, 1), (key1562, 1), (key1777, 2), (key1784, -1), (key1400, -1), (key1777, -1), (key1551, -1), (key1783, 1), (key1396, 1), (key1801, 2), (key1802, -1), (key1599, -1), (key1793, -2), (key1802, 1), (key1305, 1), (key1793, 1), (key1578, 1), (key1801, -1), (key1301, -1), (key1828, -2), (key1834, 1), (key1450, 1), (key1820, 2), (key1834, -1), (key1332, -1), (key1820, -1), (key1429, -1), (key1828, 1), (key1321, 1), (key1846, 1), (key1670, 1), (key1849, -1), (key1469, -1), (key1843, -1), (key1662, -1), (key1849, 1), (key1348, 1), (key1843, 1), (key1460, 1), (key1846, -1), (key1342, -1)]

def rawRow315 : Integer.Sparse Key := [(key1460, -2), (key1429, 1), (key1460, 1), (key1662, 2), (key1578, -1), (key1662, -1), (key1820, -1), (key1843, -1), (key1793, 1), (key1843, 1), (key1342, 2), (key1321, -1), (key1342, -1), (key1670, -2), (key1551, 1), (key1670, 1), (key1828, 1), (key1846, 1), (key1777, -1), (key1846, -1), (key1348, -2), (key1301, 1), (key1348, 1), (key1469, 2), (key1396, -1), (key1469, -1), (key1801, -1), (key1849, -1), (key1783, 1), (key1849, 1), (key1332, 1), (key1349, 1), (key1305, -1), (key1349, -1), (key1450, -1), (key1470, -1), (key1400, 1), (key1470, 1), (key1599, 1), (key1676, 1), (key1562, -1), (key1676, -1)]

def rawRow316 : Integer.Sparse Key := [(key1460, -2), (key1460, 1), (key1429, 1), (key1662, 2), (key1662, -1), (key1578, -1), (key1843, -1), (key1820, -1), (key1843, 1), (key1793, 1), (key1342, 2), (key1342, -1), (key1321, -1), (key1670, -2), (key1670, 1), (key1551, 1), (key1846, 1), (key1828, 1), (key1846, -1), (key1777, -1), (key1348, -2), (key1348, 1), (key1301, 1), (key1469, 2), (key1469, -1), (key1396, -1), (key1849, -1), (key1801, -1), (key1849, 1), (key1783, 1), (key1349, 1), (key1332, 1), (key1349, -1), (key1305, -1), (key1470, -1), (key1450, -1), (key1470, 1), (key1400, 1), (key1676, 1), (key1599, 1), (key1676, -1), (key1562, -1)]

def rawRow318 : Integer.Sparse Key := [(key1793, -2), (key1578, 1), (key1793, 1), (key1820, 2), (key1429, -1), (key1820, -1), (key1662, -1), (key1843, -1), (key1460, 1), (key1843, 1), (key1777, 2), (key1551, -1), (key1777, -1), (key1828, -2), (key1321, 1), (key1828, 1), (key1670, 1), (key1846, 1), (key1342, -1), (key1846, -1), (key1783, -2), (key1396, 1), (key1783, 1), (key1801, 2), (key1301, -1), (key1801, -1), (key1469, -1), (key1849, -1), (key1348, 1), (key1849, 1), (key1562, 1), (key1784, 1), (key1400, -1), (key1784, -1), (key1599, -1), (key1802, -1), (key1305, 1), (key1802, 1), (key1450, 1), (key1834, 1), (key1332, -1), (key1834, -1)]

def rawRow319 : Integer.Sparse Key := [(key1793, -2), (key1793, 1), (key1578, 1), (key1820, 2), (key1820, -1), (key1429, -1), (key1843, -1), (key1662, -1), (key1843, 1), (key1460, 1), (key1777, 2), (key1777, -1), (key1551, -1), (key1828, -2), (key1828, 1), (key1321, 1), (key1846, 1), (key1670, 1), (key1846, -1), (key1342, -1), (key1783, -2), (key1783, 1), (key1396, 1), (key1801, 2), (key1801, -1), (key1301, -1), (key1849, -1), (key1469, -1), (key1849, 1), (key1348, 1), (key1784, 1), (key1562, 1), (key1784, -1), (key1400, -1), (key1802, -1), (key1599, -1), (key1802, 1), (key1305, 1), (key1834, 1), (key1450, 1), (key1834, -1), (key1332, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow320 : Integer.Sparse Key := [(key1662, -2), (key1820, 1), (key1843, 1), (key1460, 2), (key1793, -1), (key1843, -1), (key1429, -1), (key1460, -1), (key1578, 1), (key1662, 1), (key1670, 2), (key1828, -1), (key1846, -1), (key1342, -2), (key1777, 1), (key1846, 1), (key1321, 1), (key1342, 1), (key1551, -1), (key1670, -1), (key1469, -2), (key1801, 1), (key1849, 1), (key1348, 2), (key1783, -1), (key1849, -1), (key1301, -1), (key1348, -1), (key1396, 1), (key1469, 1), (key1450, 1), (key1470, 1), (key1599, -1), (key1676, -1), (key1332, -1), (key1349, -1), (key1562, 1), (key1676, 1), (key1305, 1), (key1349, 1), (key1400, -1), (key1470, -1)]

def rawRow321 : Integer.Sparse Key := [(key1662, -2), (key1843, 1), (key1820, 1), (key1460, 2), (key1843, -1), (key1793, -1), (key1460, -1), (key1429, -1), (key1662, 1), (key1578, 1), (key1670, 2), (key1846, -1), (key1828, -1), (key1342, -2), (key1846, 1), (key1777, 1), (key1342, 1), (key1321, 1), (key1670, -1), (key1551, -1), (key1469, -2), (key1849, 1), (key1801, 1), (key1348, 2), (key1849, -1), (key1783, -1), (key1348, -1), (key1301, -1), (key1469, 1), (key1396, 1), (key1470, 1), (key1450, 1), (key1676, -1), (key1599, -1), (key1349, -1), (key1332, -1), (key1676, 1), (key1562, 1), (key1349, 1), (key1305, 1), (key1470, -1), (key1400, -1)]

def rawRow322 : Integer.Sparse Key := [(key1820, -2), (key1662, 1), (key1843, 1), (key1793, 2), (key1460, -1), (key1843, -1), (key1578, -1), (key1793, -1), (key1429, 1), (key1820, 1), (key1828, 2), (key1670, -1), (key1846, -1), (key1777, -2), (key1342, 1), (key1846, 1), (key1551, 1), (key1777, 1), (key1321, -1), (key1828, -1), (key1801, -2), (key1469, 1), (key1849, 1), (key1783, 2), (key1348, -1), (key1849, -1), (key1396, -1), (key1783, -1), (key1301, 1), (key1801, 1), (key1599, 1), (key1802, 1), (key1450, -1), (key1834, -1), (key1562, -1), (key1784, -1), (key1332, 1), (key1834, 1), (key1400, 1), (key1784, 1), (key1305, -1), (key1802, -1)]

def rawRow323 : Integer.Sparse Key := [(key1820, -2), (key1843, 1), (key1662, 1), (key1793, 2), (key1843, -1), (key1460, -1), (key1793, -1), (key1578, -1), (key1820, 1), (key1429, 1), (key1828, 2), (key1846, -1), (key1670, -1), (key1777, -2), (key1846, 1), (key1342, 1), (key1777, 1), (key1551, 1), (key1828, -1), (key1321, -1), (key1801, -2), (key1849, 1), (key1469, 1), (key1783, 2), (key1849, -1), (key1348, -1), (key1783, -1), (key1396, -1), (key1801, 1), (key1301, 1), (key1802, 1), (key1599, 1), (key1834, -1), (key1450, -1), (key1784, -1), (key1562, -1), (key1834, 1), (key1332, 1), (key1784, 1), (key1400, 1), (key1802, -1), (key1305, -1)]

def rawRow324 : Integer.Sparse Key := [(key1450, -2), (key1469, 1), (key1470, 1), (key1599, 2), (key1670, -1), (key1676, -1), (key1801, -1), (key1802, -1), (key1828, 1), (key1834, 1), (key1332, 2), (key1348, -1), (key1349, -1), (key1562, -2), (key1662, 1), (key1676, 1), (key1783, 1), (key1784, 1), (key1820, -1), (key1834, -1), (key1305, -2), (key1342, 1), (key1349, 1), (key1400, 2), (key1460, -1), (key1470, -1), (key1777, -1), (key1784, -1), (key1793, 1), (key1802, 1), (key1301, 1), (key1305, 1), (key1321, -1), (key1332, -1), (key1396, -1), (key1400, -1), (key1429, 1), (key1450, 1), (key1551, 1), (key1562, 1), (key1578, -1), (key1599, -1)]

def rawRow325 : Integer.Sparse Key := [(key1450, -2), (key1470, 1), (key1469, 1), (key1599, 2), (key1676, -1), (key1670, -1), (key1802, -1), (key1801, -1), (key1834, 1), (key1828, 1), (key1332, 2), (key1349, -1), (key1348, -1), (key1562, -2), (key1676, 1), (key1662, 1), (key1784, 1), (key1783, 1), (key1834, -1), (key1820, -1), (key1305, -2), (key1349, 1), (key1342, 1), (key1400, 2), (key1470, -1), (key1460, -1), (key1784, -1), (key1777, -1), (key1802, 1), (key1793, 1), (key1305, 1), (key1301, 1), (key1332, -1), (key1321, -1), (key1400, -1), (key1396, -1), (key1450, 1), (key1429, 1), (key1562, 1), (key1551, 1), (key1599, -1), (key1578, -1)]

def rawRow326 : Integer.Sparse Key := [(key1469, -2), (key1450, 1), (key1470, 1), (key1670, 2), (key1599, -1), (key1676, -1), (key1828, -1), (key1846, -1), (key1801, 1), (key1849, 1), (key1348, 2), (key1332, -1), (key1349, -1), (key1662, -2), (key1562, 1), (key1676, 1), (key1820, 1), (key1843, 1), (key1783, -1), (key1849, -1), (key1342, -2), (key1305, 1), (key1349, 1), (key1460, 2), (key1400, -1), (key1470, -1), (key1793, -1), (key1843, -1), (key1777, 1), (key1846, 1), (key1321, 1), (key1342, 1), (key1301, -1), (key1348, -1), (key1429, -1), (key1460, -1), (key1396, 1), (key1469, 1), (key1578, 1), (key1662, 1), (key1551, -1), (key1670, -1)]

def rawRow327 : Integer.Sparse Key := [(key1469, -2), (key1470, 1), (key1450, 1), (key1670, 2), (key1676, -1), (key1599, -1), (key1846, -1), (key1828, -1), (key1849, 1), (key1801, 1), (key1348, 2), (key1349, -1), (key1332, -1), (key1662, -2), (key1676, 1), (key1562, 1), (key1843, 1), (key1820, 1), (key1849, -1), (key1783, -1), (key1342, -2), (key1349, 1), (key1305, 1), (key1460, 2), (key1470, -1), (key1400, -1), (key1843, -1), (key1793, -1), (key1846, 1), (key1777, 1), (key1342, 1), (key1321, 1), (key1348, -1), (key1301, -1), (key1460, -1), (key1429, -1), (key1469, 1), (key1396, 1), (key1662, 1), (key1578, 1), (key1670, -1), (key1551, -1)]

def rawRow328 : Integer.Sparse Key := [(key1599, -2), (key1801, 1), (key1802, 1), (key1450, 2), (key1828, -1), (key1834, -1), (key1469, -1), (key1470, -1), (key1670, 1), (key1676, 1), (key1562, 2), (key1783, -1), (key1784, -1), (key1332, -2), (key1820, 1), (key1834, 1), (key1348, 1), (key1349, 1), (key1662, -1), (key1676, -1), (key1400, -2), (key1777, 1), (key1784, 1), (key1305, 2), (key1793, -1), (key1802, -1), (key1342, -1), (key1349, -1), (key1460, 1), (key1470, 1), (key1396, 1), (key1400, 1), (key1551, -1), (key1562, -1), (key1301, -1), (key1305, -1), (key1578, 1), (key1599, 1), (key1321, 1), (key1332, 1), (key1429, -1), (key1450, -1)]

def rawRow329 : Integer.Sparse Key := [(key1599, -2), (key1802, 1), (key1801, 1), (key1450, 2), (key1834, -1), (key1828, -1), (key1470, -1), (key1469, -1), (key1676, 1), (key1670, 1), (key1562, 2), (key1784, -1), (key1783, -1), (key1332, -2), (key1834, 1), (key1820, 1), (key1349, 1), (key1348, 1), (key1676, -1), (key1662, -1), (key1400, -2), (key1784, 1), (key1777, 1), (key1305, 2), (key1802, -1), (key1793, -1), (key1349, -1), (key1342, -1), (key1470, 1), (key1460, 1), (key1400, 1), (key1396, 1), (key1562, -1), (key1551, -1), (key1305, -1), (key1301, -1), (key1599, 1), (key1578, 1), (key1332, 1), (key1321, 1), (key1450, -1), (key1429, -1)]

def rawRow330 : Integer.Sparse Key := [(key1801, -2), (key1599, 1), (key1802, 1), (key1828, 2), (key1450, -1), (key1834, -1), (key1670, -1), (key1846, -1), (key1469, 1), (key1849, 1), (key1783, 2), (key1562, -1), (key1784, -1), (key1820, -2), (key1332, 1), (key1834, 1), (key1662, 1), (key1843, 1), (key1348, -1), (key1849, -1), (key1777, -2), (key1400, 1), (key1784, 1), (key1793, 2), (key1305, -1), (key1802, -1), (key1460, -1), (key1843, -1), (key1342, 1), (key1846, 1), (key1551, 1), (key1777, 1), (key1396, -1), (key1783, -1), (key1578, -1), (key1793, -1), (key1301, 1), (key1801, 1), (key1429, 1), (key1820, 1), (key1321, -1), (key1828, -1)]

def rawRow331 : Integer.Sparse Key := [(key1801, -2), (key1802, 1), (key1599, 1), (key1828, 2), (key1834, -1), (key1450, -1), (key1846, -1), (key1670, -1), (key1849, 1), (key1469, 1), (key1783, 2), (key1784, -1), (key1562, -1), (key1820, -2), (key1834, 1), (key1332, 1), (key1843, 1), (key1662, 1), (key1849, -1), (key1348, -1), (key1777, -2), (key1784, 1), (key1400, 1), (key1793, 2), (key1802, -1), (key1305, -1), (key1843, -1), (key1460, -1), (key1846, 1), (key1342, 1), (key1777, 1), (key1551, 1), (key1783, -1), (key1396, -1), (key1793, -1), (key1578, -1), (key1801, 1), (key1301, 1), (key1820, 1), (key1429, 1), (key1828, -1), (key1321, -1)]

def rawRow332 : Integer.Sparse Key := [(key1670, -2), (key1828, 1), (key1846, 1), (key1469, 2), (key1801, -1), (key1849, -1), (key1450, -1), (key1470, -1), (key1599, 1), (key1676, 1), (key1662, 2), (key1820, -1), (key1843, -1), (key1348, -2), (key1783, 1), (key1849, 1), (key1332, 1), (key1349, 1), (key1562, -1), (key1676, -1), (key1460, -2), (key1793, 1), (key1843, 1), (key1342, 2), (key1777, -1), (key1846, -1), (key1305, -1), (key1349, -1), (key1400, 1), (key1470, 1), (key1429, 1), (key1460, 1), (key1578, -1), (key1662, -1), (key1321, -1), (key1342, -1), (key1551, 1), (key1670, 1), (key1301, 1), (key1348, 1), (key1396, -1), (key1469, -1)]

def rawRow333 : Integer.Sparse Key := [(key1670, -2), (key1846, 1), (key1828, 1), (key1469, 2), (key1849, -1), (key1801, -1), (key1470, -1), (key1450, -1), (key1676, 1), (key1599, 1), (key1662, 2), (key1843, -1), (key1820, -1), (key1348, -2), (key1849, 1), (key1783, 1), (key1349, 1), (key1332, 1), (key1676, -1), (key1562, -1), (key1460, -2), (key1843, 1), (key1793, 1), (key1342, 2), (key1846, -1), (key1777, -1), (key1349, -1), (key1305, -1), (key1470, 1), (key1400, 1), (key1460, 1), (key1429, 1), (key1662, -1), (key1578, -1), (key1342, -1), (key1321, -1), (key1670, 1), (key1551, 1), (key1348, 1), (key1301, 1), (key1469, -1), (key1396, -1)]

def rawRow334 : Integer.Sparse Key := [(key1828, -2), (key1670, 1), (key1846, 1), (key1801, 2), (key1469, -1), (key1849, -1), (key1599, -1), (key1802, -1), (key1450, 1), (key1834, 1), (key1820, 2), (key1662, -1), (key1843, -1), (key1783, -2), (key1348, 1), (key1849, 1), (key1562, 1), (key1784, 1), (key1332, -1), (key1834, -1), (key1793, -2), (key1460, 1), (key1843, 1), (key1777, 2), (key1342, -1), (key1846, -1), (key1400, -1), (key1784, -1), (key1305, 1), (key1802, 1), (key1578, 1), (key1793, 1), (key1429, -1), (key1820, -1), (key1551, -1), (key1777, -1), (key1321, 1), (key1828, 1), (key1396, 1), (key1783, 1), (key1301, -1), (key1801, -1)]

def rawRow335 : Integer.Sparse Key := [(key1828, -2), (key1846, 1), (key1670, 1), (key1801, 2), (key1849, -1), (key1469, -1), (key1802, -1), (key1599, -1), (key1834, 1), (key1450, 1), (key1820, 2), (key1843, -1), (key1662, -1), (key1783, -2), (key1849, 1), (key1348, 1), (key1784, 1), (key1562, 1), (key1834, -1), (key1332, -1), (key1793, -2), (key1843, 1), (key1460, 1), (key1777, 2), (key1846, -1), (key1342, -1), (key1784, -1), (key1400, -1), (key1802, 1), (key1305, 1), (key1793, 1), (key1578, 1), (key1820, -1), (key1429, -1), (key1777, -1), (key1551, -1), (key1828, 1), (key1321, 1), (key1783, 1), (key1396, 1), (key1801, -1), (key1301, -1)]

def rawRow337 : Integer.Sparse Key := [(key1300, -1), (key1306, -1), (key1300, 2), (key1328, 1), (key1333, 1), (key1320, -1), (key1328, -1), (key1356, -2), (key1353, 1), (key1356, 1), (key1395, 1), (key1401, 1), (key1395, -2), (key1446, -1), (key1451, -1), (key1428, 1), (key1446, 1), (key1482, 2), (key1474, -1), (key1482, -1), (key1558, -1), (key1563, -1), (key1550, 1), (key1558, 1), (key1595, 1), (key1600, 1), (key1577, -1), (key1595, -1), (key1691, -1), (key1694, -1), (key1685, 1), (key1694, 1), (key1901, 2), (key1898, -1), (key1901, -1), (key1913, -2), (key1905, 1), (key1913, 1), (key1928, 1), (key1931, 1), (key1922, -1), (key1931, -1)]

def rawRow338 : Integer.Sparse Key := [(key1306, -1), (key1300, -1), (key1300, 2), (key1333, 1), (key1328, 1), (key1328, -1), (key1320, -1), (key1356, -2), (key1356, 1), (key1353, 1), (key1401, 1), (key1395, 1), (key1395, -2), (key1451, -1), (key1446, -1), (key1446, 1), (key1428, 1), (key1482, 2), (key1482, -1), (key1474, -1), (key1563, -1), (key1558, -1), (key1558, 1), (key1550, 1), (key1600, 1), (key1595, 1), (key1595, -1), (key1577, -1), (key1694, -1), (key1691, -1), (key1694, 1), (key1685, 1), (key1901, 2), (key1901, -1), (key1898, -1), (key1913, -2), (key1913, 1), (key1905, 1), (key1931, 1), (key1928, 1), (key1931, -1), (key1922, -1)]

def rawRow340 : Integer.Sparse Key := [(key1320, -1), (key1353, -1), (key1320, 2), (key1328, 1), (key1356, 1), (key1300, -1), (key1328, -1), (key1333, -2), (key1306, 1), (key1333, 1), (key1428, 1), (key1474, 1), (key1428, -2), (key1446, -1), (key1482, -1), (key1395, 1), (key1446, 1), (key1451, 2), (key1401, -1), (key1451, -1), (key1626, -1), (key1685, -1), (key1577, 1), (key1626, 1), (key1635, 1), (key1691, 1), (key1550, -1), (key1635, -1), (key1600, -1), (key1644, -1), (key1563, 1), (key1644, 1), (key1922, 2), (key1905, -1), (key1922, -1), (key1928, -2), (key1898, 1), (key1928, 1), (key1913, 1), (key1931, 1), (key1901, -1), (key1931, -1)]

def rawRow341 : Integer.Sparse Key := [(key1353, -1), (key1320, -1), (key1320, 2), (key1356, 1), (key1328, 1), (key1328, -1), (key1300, -1), (key1333, -2), (key1333, 1), (key1306, 1), (key1474, 1), (key1428, 1), (key1428, -2), (key1482, -1), (key1446, -1), (key1446, 1), (key1395, 1), (key1451, 2), (key1451, -1), (key1401, -1), (key1685, -1), (key1626, -1), (key1626, 1), (key1577, 1), (key1691, 1), (key1635, 1), (key1635, -1), (key1550, -1), (key1644, -1), (key1600, -1), (key1644, 1), (key1563, 1), (key1922, 2), (key1922, -1), (key1905, -1), (key1928, -2), (key1928, 1), (key1898, 1), (key1931, 1), (key1913, 1), (key1931, -1), (key1901, -1)]

def rawRow342 : Integer.Sparse Key := [(key1328, -1), (key1333, -1), (key1356, 2), (key1300, 1), (key1306, 1), (key1353, -1), (key1356, -1), (key1300, -2), (key1320, 1), (key1328, 1), (key1446, 1), (key1451, 1), (key1482, -2), (key1395, -1), (key1401, -1), (key1474, 1), (key1482, 1), (key1395, 2), (key1428, -1), (key1446, -1), (key1595, -1), (key1600, -1), (key1691, 1), (key1694, 1), (key1558, 1), (key1563, 1), (key1685, -1), (key1694, -1), (key1550, -1), (key1558, -1), (key1577, 1), (key1595, 1), (key1913, 2), (key1928, -1), (key1931, -1), (key1901, -2), (key1922, 1), (key1931, 1), (key1898, 1), (key1901, 1), (key1905, -1), (key1913, -1)]

def rawRow343 : Integer.Sparse Key := [(key1333, -1), (key1328, -1), (key1356, 2), (key1306, 1), (key1300, 1), (key1356, -1), (key1353, -1), (key1300, -2), (key1328, 1), (key1320, 1), (key1451, 1), (key1446, 1), (key1482, -2), (key1401, -1), (key1395, -1), (key1482, 1), (key1474, 1), (key1395, 2), (key1446, -1), (key1428, -1), (key1600, -1), (key1595, -1), (key1694, 1), (key1691, 1), (key1563, 1), (key1558, 1), (key1694, -1), (key1685, -1), (key1558, -1), (key1550, -1), (key1595, 1), (key1577, 1), (key1913, 2), (key1931, -1), (key1928, -1), (key1901, -2), (key1931, 1), (key1922, 1), (key1901, 1), (key1898, 1), (key1913, -1), (key1905, -1)]

def rawRow344 : Integer.Sparse Key := [(key1328, -1), (key1356, -1), (key1333, 2), (key1320, 1), (key1353, 1), (key1306, -1), (key1333, -1), (key1320, -2), (key1300, 1), (key1328, 1), (key1446, 1), (key1482, 1), (key1451, -2), (key1428, -1), (key1474, -1), (key1401, 1), (key1451, 1), (key1428, 2), (key1395, -1), (key1446, -1), (key1635, -1), (key1691, -1), (key1600, 1), (key1644, 1), (key1626, 1), (key1685, 1), (key1563, -1), (key1644, -1), (key1577, -1), (key1626, -1), (key1550, 1), (key1635, 1), (key1928, 2), (key1913, -1), (key1931, -1), (key1922, -2), (key1901, 1), (key1931, 1), (key1905, 1), (key1922, 1), (key1898, -1), (key1928, -1)]

def rawRow345 : Integer.Sparse Key := [(key1356, -1), (key1328, -1), (key1333, 2), (key1353, 1), (key1320, 1), (key1333, -1), (key1306, -1), (key1320, -2), (key1328, 1), (key1300, 1), (key1482, 1), (key1446, 1), (key1451, -2), (key1474, -1), (key1428, -1), (key1451, 1), (key1401, 1), (key1428, 2), (key1446, -1), (key1395, -1), (key1691, -1), (key1635, -1), (key1644, 1), (key1600, 1), (key1685, 1), (key1626, 1), (key1644, -1), (key1563, -1), (key1626, -1), (key1577, -1), (key1635, 1), (key1550, 1), (key1928, 2), (key1931, -1), (key1913, -1), (key1922, -2), (key1931, 1), (key1901, 1), (key1922, 1), (key1905, 1), (key1928, -1), (key1898, -1)]

def rawRow347 : Integer.Sparse Key := [(key1395, -1), (key1401, -1), (key1395, 2), (key1558, 1), (key1563, 1), (key1550, -1), (key1558, -1), (key1901, -2), (key1898, 1), (key1901, 1), (key1300, 1), (key1306, 1), (key1300, -2), (key1595, -1), (key1600, -1), (key1577, 1), (key1595, 1), (key1913, 2), (key1905, -1), (key1913, -1), (key1328, -1), (key1333, -1), (key1320, 1), (key1328, 1), (key1446, 1), (key1451, 1), (key1428, -1), (key1446, -1), (key1928, -1), (key1931, -1), (key1922, 1), (key1931, 1), (key1356, 2), (key1353, -1), (key1356, -1), (key1482, -2), (key1474, 1), (key1482, 1), (key1691, 1), (key1694, 1), (key1685, -1), (key1694, -1)]

def rawRow348 : Integer.Sparse Key := [(key1401, -1), (key1395, -1), (key1395, 2), (key1563, 1), (key1558, 1), (key1558, -1), (key1550, -1), (key1901, -2), (key1901, 1), (key1898, 1), (key1306, 1), (key1300, 1), (key1300, -2), (key1600, -1), (key1595, -1), (key1595, 1), (key1577, 1), (key1913, 2), (key1913, -1), (key1905, -1), (key1333, -1), (key1328, -1), (key1328, 1), (key1320, 1), (key1451, 1), (key1446, 1), (key1446, -1), (key1428, -1), (key1931, -1), (key1928, -1), (key1931, 1), (key1922, 1), (key1356, 2), (key1356, -1), (key1353, -1), (key1482, -2), (key1482, 1), (key1474, 1), (key1694, 1), (key1691, 1), (key1694, -1), (key1685, -1)]

def rawRow350 : Integer.Sparse Key := [(key1550, -1), (key1898, -1), (key1550, 2), (key1558, 1), (key1901, 1), (key1395, -1), (key1558, -1), (key1563, -2), (key1401, 1), (key1563, 1), (key1577, 1), (key1905, 1), (key1577, -2), (key1595, -1), (key1913, -1), (key1300, 1), (key1595, 1), (key1600, 2), (key1306, -1), (key1600, -1), (key1626, -1), (key1922, -1), (key1428, 1), (key1626, 1), (key1635, 1), (key1928, 1), (key1320, -1), (key1635, -1), (key1451, -1), (key1644, -1), (key1333, 1), (key1644, 1), (key1685, 2), (key1474, -1), (key1685, -1), (key1691, -2), (key1353, 1), (key1691, 1), (key1482, 1), (key1694, 1), (key1356, -1), (key1694, -1)]

def rawRow351 : Integer.Sparse Key := [(key1898, -1), (key1550, -1), (key1550, 2), (key1901, 1), (key1558, 1), (key1558, -1), (key1395, -1), (key1563, -2), (key1563, 1), (key1401, 1), (key1905, 1), (key1577, 1), (key1577, -2), (key1913, -1), (key1595, -1), (key1595, 1), (key1300, 1), (key1600, 2), (key1600, -1), (key1306, -1), (key1922, -1), (key1626, -1), (key1626, 1), (key1428, 1), (key1928, 1), (key1635, 1), (key1635, -1), (key1320, -1), (key1644, -1), (key1451, -1), (key1644, 1), (key1333, 1), (key1685, 2), (key1685, -1), (key1474, -1), (key1691, -2), (key1691, 1), (key1353, 1), (key1694, 1), (key1482, 1), (key1694, -1), (key1356, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow352 : Integer.Sparse Key := [(key1558, -1), (key1563, -1), (key1901, 2), (key1395, 1), (key1401, 1), (key1898, -1), (key1901, -1), (key1395, -2), (key1550, 1), (key1558, 1), (key1595, 1), (key1600, 1), (key1913, -2), (key1300, -1), (key1306, -1), (key1905, 1), (key1913, 1), (key1300, 2), (key1577, -1), (key1595, -1), (key1446, -1), (key1451, -1), (key1928, 1), (key1931, 1), (key1328, 1), (key1333, 1), (key1922, -1), (key1931, -1), (key1320, -1), (key1328, -1), (key1428, 1), (key1446, 1), (key1482, 2), (key1691, -1), (key1694, -1), (key1356, -2), (key1685, 1), (key1694, 1), (key1353, 1), (key1356, 1), (key1474, -1), (key1482, -1)]

def rawRow353 : Integer.Sparse Key := [(key1563, -1), (key1558, -1), (key1901, 2), (key1401, 1), (key1395, 1), (key1901, -1), (key1898, -1), (key1395, -2), (key1558, 1), (key1550, 1), (key1600, 1), (key1595, 1), (key1913, -2), (key1306, -1), (key1300, -1), (key1913, 1), (key1905, 1), (key1300, 2), (key1595, -1), (key1577, -1), (key1451, -1), (key1446, -1), (key1931, 1), (key1928, 1), (key1333, 1), (key1328, 1), (key1931, -1), (key1922, -1), (key1328, -1), (key1320, -1), (key1446, 1), (key1428, 1), (key1482, 2), (key1694, -1), (key1691, -1), (key1356, -2), (key1694, 1), (key1685, 1), (key1356, 1), (key1353, 1), (key1482, -1), (key1474, -1)]

def rawRow354 : Integer.Sparse Key := [(key1558, -1), (key1901, -1), (key1563, 2), (key1550, 1), (key1898, 1), (key1401, -1), (key1563, -1), (key1550, -2), (key1395, 1), (key1558, 1), (key1595, 1), (key1913, 1), (key1600, -2), (key1577, -1), (key1905, -1), (key1306, 1), (key1600, 1), (key1577, 2), (key1300, -1), (key1595, -1), (key1635, -1), (key1928, -1), (key1451, 1), (key1644, 1), (key1626, 1), (key1922, 1), (key1333, -1), (key1644, -1), (key1428, -1), (key1626, -1), (key1320, 1), (key1635, 1), (key1691, 2), (key1482, -1), (key1694, -1), (key1685, -2), (key1356, 1), (key1694, 1), (key1474, 1), (key1685, 1), (key1353, -1), (key1691, -1)]

def rawRow355 : Integer.Sparse Key := [(key1901, -1), (key1558, -1), (key1563, 2), (key1898, 1), (key1550, 1), (key1563, -1), (key1401, -1), (key1550, -2), (key1558, 1), (key1395, 1), (key1913, 1), (key1595, 1), (key1600, -2), (key1905, -1), (key1577, -1), (key1600, 1), (key1306, 1), (key1577, 2), (key1595, -1), (key1300, -1), (key1928, -1), (key1635, -1), (key1644, 1), (key1451, 1), (key1922, 1), (key1626, 1), (key1644, -1), (key1333, -1), (key1626, -1), (key1428, -1), (key1635, 1), (key1320, 1), (key1691, 2), (key1694, -1), (key1482, -1), (key1685, -2), (key1694, 1), (key1356, 1), (key1685, 1), (key1474, 1), (key1691, -1), (key1353, -1)]

def rawRow357 : Integer.Sparse Key := [(key1428, -1), (key1474, -1), (key1428, 2), (key1626, 1), (key1685, 1), (key1577, -1), (key1626, -1), (key1922, -2), (key1905, 1), (key1922, 1), (key1320, 1), (key1353, 1), (key1320, -2), (key1635, -1), (key1691, -1), (key1550, 1), (key1635, 1), (key1928, 2), (key1898, -1), (key1928, -1), (key1328, -1), (key1356, -1), (key1300, 1), (key1328, 1), (key1446, 1), (key1482, 1), (key1395, -1), (key1446, -1), (key1913, -1), (key1931, -1), (key1901, 1), (key1931, 1), (key1333, 2), (key1306, -1), (key1333, -1), (key1451, -2), (key1401, 1), (key1451, 1), (key1600, 1), (key1644, 1), (key1563, -1), (key1644, -1)]

def rawRow358 : Integer.Sparse Key := [(key1474, -1), (key1428, -1), (key1428, 2), (key1685, 1), (key1626, 1), (key1626, -1), (key1577, -1), (key1922, -2), (key1922, 1), (key1905, 1), (key1353, 1), (key1320, 1), (key1320, -2), (key1691, -1), (key1635, -1), (key1635, 1), (key1550, 1), (key1928, 2), (key1928, -1), (key1898, -1), (key1356, -1), (key1328, -1), (key1328, 1), (key1300, 1), (key1482, 1), (key1446, 1), (key1446, -1), (key1395, -1), (key1931, -1), (key1913, -1), (key1931, 1), (key1901, 1), (key1333, 2), (key1333, -1), (key1306, -1), (key1451, -2), (key1451, 1), (key1401, 1), (key1644, 1), (key1600, 1), (key1644, -1), (key1563, -1)]

def rawRow360 : Integer.Sparse Key := [(key1577, -1), (key1905, -1), (key1577, 2), (key1626, 1), (key1922, 1), (key1428, -1), (key1626, -1), (key1685, -2), (key1474, 1), (key1685, 1), (key1550, 1), (key1898, 1), (key1550, -2), (key1635, -1), (key1928, -1), (key1320, 1), (key1635, 1), (key1691, 2), (key1353, -1), (key1691, -1), (key1558, -1), (key1901, -1), (key1395, 1), (key1558, 1), (key1595, 1), (key1913, 1), (key1300, -1), (key1595, -1), (key1482, -1), (key1694, -1), (key1356, 1), (key1694, 1), (key1563, 2), (key1401, -1), (key1563, -1), (key1600, -2), (key1306, 1), (key1600, 1), (key1451, 1), (key1644, 1), (key1333, -1), (key1644, -1)]

def rawRow361 : Integer.Sparse Key := [(key1905, -1), (key1577, -1), (key1577, 2), (key1922, 1), (key1626, 1), (key1626, -1), (key1428, -1), (key1685, -2), (key1685, 1), (key1474, 1), (key1898, 1), (key1550, 1), (key1550, -2), (key1928, -1), (key1635, -1), (key1635, 1), (key1320, 1), (key1691, 2), (key1691, -1), (key1353, -1), (key1901, -1), (key1558, -1), (key1558, 1), (key1395, 1), (key1913, 1), (key1595, 1), (key1595, -1), (key1300, -1), (key1694, -1), (key1482, -1), (key1694, 1), (key1356, 1), (key1563, 2), (key1563, -1), (key1401, -1), (key1600, -2), (key1600, 1), (key1306, 1), (key1644, 1), (key1451, 1), (key1644, -1), (key1333, -1)]

def rawRow362 : Integer.Sparse Key := [(key1626, -1), (key1685, -1), (key1922, 2), (key1428, 1), (key1474, 1), (key1905, -1), (key1922, -1), (key1428, -2), (key1577, 1), (key1626, 1), (key1635, 1), (key1691, 1), (key1928, -2), (key1320, -1), (key1353, -1), (key1898, 1), (key1928, 1), (key1320, 2), (key1550, -1), (key1635, -1), (key1446, -1), (key1482, -1), (key1913, 1), (key1931, 1), (key1328, 1), (key1356, 1), (key1901, -1), (key1931, -1), (key1300, -1), (key1328, -1), (key1395, 1), (key1446, 1), (key1451, 2), (key1600, -1), (key1644, -1), (key1333, -2), (key1563, 1), (key1644, 1), (key1306, 1), (key1333, 1), (key1401, -1), (key1451, -1)]

def rawRow363 : Integer.Sparse Key := [(key1685, -1), (key1626, -1), (key1922, 2), (key1474, 1), (key1428, 1), (key1922, -1), (key1905, -1), (key1428, -2), (key1626, 1), (key1577, 1), (key1691, 1), (key1635, 1), (key1928, -2), (key1353, -1), (key1320, -1), (key1928, 1), (key1898, 1), (key1320, 2), (key1635, -1), (key1550, -1), (key1482, -1), (key1446, -1), (key1931, 1), (key1913, 1), (key1356, 1), (key1328, 1), (key1931, -1), (key1901, -1), (key1328, -1), (key1300, -1), (key1446, 1), (key1395, 1), (key1451, 2), (key1644, -1), (key1600, -1), (key1333, -2), (key1644, 1), (key1563, 1), (key1333, 1), (key1306, 1), (key1451, -1), (key1401, -1)]

def rawRow364 : Integer.Sparse Key := [(key1626, -1), (key1922, -1), (key1685, 2), (key1577, 1), (key1905, 1), (key1474, -1), (key1685, -1), (key1577, -2), (key1428, 1), (key1626, 1), (key1635, 1), (key1928, 1), (key1691, -2), (key1550, -1), (key1898, -1), (key1353, 1), (key1691, 1), (key1550, 2), (key1320, -1), (key1635, -1), (key1595, -1), (key1913, -1), (key1482, 1), (key1694, 1), (key1558, 1), (key1901, 1), (key1356, -1), (key1694, -1), (key1395, -1), (key1558, -1), (key1300, 1), (key1595, 1), (key1600, 2), (key1451, -1), (key1644, -1), (key1563, -2), (key1333, 1), (key1644, 1), (key1401, 1), (key1563, 1), (key1306, -1), (key1600, -1)]

def rawRow365 : Integer.Sparse Key := [(key1922, -1), (key1626, -1), (key1685, 2), (key1905, 1), (key1577, 1), (key1685, -1), (key1474, -1), (key1577, -2), (key1626, 1), (key1428, 1), (key1928, 1), (key1635, 1), (key1691, -2), (key1898, -1), (key1550, -1), (key1691, 1), (key1353, 1), (key1550, 2), (key1635, -1), (key1320, -1), (key1913, -1), (key1595, -1), (key1694, 1), (key1482, 1), (key1901, 1), (key1558, 1), (key1694, -1), (key1356, -1), (key1558, -1), (key1395, -1), (key1595, 1), (key1300, 1), (key1600, 2), (key1644, -1), (key1451, -1), (key1563, -2), (key1644, 1), (key1333, 1), (key1563, 1), (key1401, 1), (key1600, -1), (key1306, -1)]

def rawRow366 : Integer.Sparse Key := [(key1446, -1), (key1451, -1), (key1482, 2), (key1595, 1), (key1600, 1), (key1691, -1), (key1694, -1), (key1913, -2), (key1928, 1), (key1931, 1), (key1328, 1), (key1333, 1), (key1356, -2), (key1558, -1), (key1563, -1), (key1685, 1), (key1694, 1), (key1901, 2), (key1922, -1), (key1931, -1), (key1300, -1), (key1306, -1), (key1353, 1), (key1356, 1), (key1395, 1), (key1401, 1), (key1474, -1), (key1482, -1), (key1898, -1), (key1901, -1), (key1905, 1), (key1913, 1), (key1300, 2), (key1320, -1), (key1328, -1), (key1395, -2), (key1428, 1), (key1446, 1), (key1550, 1), (key1558, 1), (key1577, -1), (key1595, -1)]

def rawRow367 : Integer.Sparse Key := [(key1451, -1), (key1446, -1), (key1482, 2), (key1600, 1), (key1595, 1), (key1694, -1), (key1691, -1), (key1913, -2), (key1931, 1), (key1928, 1), (key1333, 1), (key1328, 1), (key1356, -2), (key1563, -1), (key1558, -1), (key1694, 1), (key1685, 1), (key1901, 2), (key1931, -1), (key1922, -1), (key1306, -1), (key1300, -1), (key1356, 1), (key1353, 1), (key1401, 1), (key1395, 1), (key1482, -1), (key1474, -1), (key1901, -1), (key1898, -1), (key1913, 1), (key1905, 1), (key1300, 2), (key1328, -1), (key1320, -1), (key1395, -2), (key1446, 1), (key1428, 1), (key1558, 1), (key1550, 1), (key1595, -1), (key1577, -1)]

def rawRow368 : Integer.Sparse Key := [(key1446, -1), (key1482, -1), (key1451, 2), (key1635, 1), (key1691, 1), (key1600, -1), (key1644, -1), (key1928, -2), (key1913, 1), (key1931, 1), (key1328, 1), (key1356, 1), (key1333, -2), (key1626, -1), (key1685, -1), (key1563, 1), (key1644, 1), (key1922, 2), (key1901, -1), (key1931, -1), (key1320, -1), (key1353, -1), (key1306, 1), (key1333, 1), (key1428, 1), (key1474, 1), (key1401, -1), (key1451, -1), (key1905, -1), (key1922, -1), (key1898, 1), (key1928, 1), (key1320, 2), (key1300, -1), (key1328, -1), (key1428, -2), (key1395, 1), (key1446, 1), (key1577, 1), (key1626, 1), (key1550, -1), (key1635, -1)]

def rawRow369 : Integer.Sparse Key := [(key1482, -1), (key1446, -1), (key1451, 2), (key1691, 1), (key1635, 1), (key1644, -1), (key1600, -1), (key1928, -2), (key1931, 1), (key1913, 1), (key1356, 1), (key1328, 1), (key1333, -2), (key1685, -1), (key1626, -1), (key1644, 1), (key1563, 1), (key1922, 2), (key1931, -1), (key1901, -1), (key1353, -1), (key1320, -1), (key1333, 1), (key1306, 1), (key1474, 1), (key1428, 1), (key1451, -1), (key1401, -1), (key1922, -1), (key1905, -1), (key1928, 1), (key1898, 1), (key1320, 2), (key1328, -1), (key1300, -1), (key1428, -2), (key1446, 1), (key1395, 1), (key1626, 1), (key1577, 1), (key1635, -1), (key1550, -1)]

def rawRow370 : Integer.Sparse Key := [(key1595, -1), (key1600, -1), (key1913, 2), (key1446, 1), (key1451, 1), (key1928, -1), (key1931, -1), (key1482, -2), (key1691, 1), (key1694, 1), (key1558, 1), (key1563, 1), (key1901, -2), (key1328, -1), (key1333, -1), (key1922, 1), (key1931, 1), (key1356, 2), (key1685, -1), (key1694, -1), (key1395, -1), (key1401, -1), (key1898, 1), (key1901, 1), (key1300, 1), (key1306, 1), (key1905, -1), (key1913, -1), (key1353, -1), (key1356, -1), (key1474, 1), (key1482, 1), (key1395, 2), (key1550, -1), (key1558, -1), (key1300, -2), (key1577, 1), (key1595, 1), (key1320, 1), (key1328, 1), (key1428, -1), (key1446, -1)]

def rawRow371 : Integer.Sparse Key := [(key1600, -1), (key1595, -1), (key1913, 2), (key1451, 1), (key1446, 1), (key1931, -1), (key1928, -1), (key1482, -2), (key1694, 1), (key1691, 1), (key1563, 1), (key1558, 1), (key1901, -2), (key1333, -1), (key1328, -1), (key1931, 1), (key1922, 1), (key1356, 2), (key1694, -1), (key1685, -1), (key1401, -1), (key1395, -1), (key1901, 1), (key1898, 1), (key1306, 1), (key1300, 1), (key1913, -1), (key1905, -1), (key1356, -1), (key1353, -1), (key1482, 1), (key1474, 1), (key1395, 2), (key1558, -1), (key1550, -1), (key1300, -2), (key1595, 1), (key1577, 1), (key1328, 1), (key1320, 1), (key1446, -1), (key1428, -1)]

def rawRow372 : Integer.Sparse Key := [(key1595, -1), (key1913, -1), (key1600, 2), (key1635, 1), (key1928, 1), (key1451, -1), (key1644, -1), (key1691, -2), (key1482, 1), (key1694, 1), (key1558, 1), (key1901, 1), (key1563, -2), (key1626, -1), (key1922, -1), (key1333, 1), (key1644, 1), (key1685, 2), (key1356, -1), (key1694, -1), (key1550, -1), (key1898, -1), (key1401, 1), (key1563, 1), (key1577, 1), (key1905, 1), (key1306, -1), (key1600, -1), (key1474, -1), (key1685, -1), (key1353, 1), (key1691, 1), (key1550, 2), (key1395, -1), (key1558, -1), (key1577, -2), (key1300, 1), (key1595, 1), (key1428, 1), (key1626, 1), (key1320, -1), (key1635, -1)]

def rawRow373 : Integer.Sparse Key := [(key1913, -1), (key1595, -1), (key1600, 2), (key1928, 1), (key1635, 1), (key1644, -1), (key1451, -1), (key1691, -2), (key1694, 1), (key1482, 1), (key1901, 1), (key1558, 1), (key1563, -2), (key1922, -1), (key1626, -1), (key1644, 1), (key1333, 1), (key1685, 2), (key1694, -1), (key1356, -1), (key1898, -1), (key1550, -1), (key1563, 1), (key1401, 1), (key1905, 1), (key1577, 1), (key1600, -1), (key1306, -1), (key1685, -1), (key1474, -1), (key1691, 1), (key1353, 1), (key1550, 2), (key1558, -1), (key1395, -1), (key1577, -2), (key1595, 1), (key1300, 1), (key1626, 1), (key1428, 1), (key1635, -1), (key1320, -1)]

def rawRow374 : Integer.Sparse Key := [(key1635, -1), (key1691, -1), (key1928, 2), (key1446, 1), (key1482, 1), (key1913, -1), (key1931, -1), (key1451, -2), (key1600, 1), (key1644, 1), (key1626, 1), (key1685, 1), (key1922, -2), (key1328, -1), (key1356, -1), (key1901, 1), (key1931, 1), (key1333, 2), (key1563, -1), (key1644, -1), (key1428, -1), (key1474, -1), (key1905, 1), (key1922, 1), (key1320, 1), (key1353, 1), (key1898, -1), (key1928, -1), (key1306, -1), (key1333, -1), (key1401, 1), (key1451, 1), (key1428, 2), (key1577, -1), (key1626, -1), (key1320, -2), (key1550, 1), (key1635, 1), (key1300, 1), (key1328, 1), (key1395, -1), (key1446, -1)]

def rawRow375 : Integer.Sparse Key := [(key1691, -1), (key1635, -1), (key1928, 2), (key1482, 1), (key1446, 1), (key1931, -1), (key1913, -1), (key1451, -2), (key1644, 1), (key1600, 1), (key1685, 1), (key1626, 1), (key1922, -2), (key1356, -1), (key1328, -1), (key1931, 1), (key1901, 1), (key1333, 2), (key1644, -1), (key1563, -1), (key1474, -1), (key1428, -1), (key1922, 1), (key1905, 1), (key1353, 1), (key1320, 1), (key1928, -1), (key1898, -1), (key1333, -1), (key1306, -1), (key1451, 1), (key1401, 1), (key1428, 2), (key1626, -1), (key1577, -1), (key1320, -2), (key1635, 1), (key1550, 1), (key1328, 1), (key1300, 1), (key1446, -1), (key1395, -1)]

def rawRow376 : Integer.Sparse Key := [(key1635, -1), (key1928, -1), (key1691, 2), (key1595, 1), (key1913, 1), (key1482, -1), (key1694, -1), (key1600, -2), (key1451, 1), (key1644, 1), (key1626, 1), (key1922, 1), (key1685, -2), (key1558, -1), (key1901, -1), (key1356, 1), (key1694, 1), (key1563, 2), (key1333, -1), (key1644, -1), (key1577, -1), (key1905, -1), (key1474, 1), (key1685, 1), (key1550, 1), (key1898, 1), (key1353, -1), (key1691, -1), (key1401, -1), (key1563, -1), (key1306, 1), (key1600, 1), (key1577, 2), (key1428, -1), (key1626, -1), (key1550, -2), (key1320, 1), (key1635, 1), (key1395, 1), (key1558, 1), (key1300, -1), (key1595, -1)]

def rawRow377 : Integer.Sparse Key := [(key1928, -1), (key1635, -1), (key1691, 2), (key1913, 1), (key1595, 1), (key1694, -1), (key1482, -1), (key1600, -2), (key1644, 1), (key1451, 1), (key1922, 1), (key1626, 1), (key1685, -2), (key1901, -1), (key1558, -1), (key1694, 1), (key1356, 1), (key1563, 2), (key1644, -1), (key1333, -1), (key1905, -1), (key1577, -1), (key1685, 1), (key1474, 1), (key1898, 1), (key1550, 1), (key1691, -1), (key1353, -1), (key1563, -1), (key1401, -1), (key1600, 1), (key1306, 1), (key1577, 2), (key1626, -1), (key1428, -1), (key1550, -2), (key1635, 1), (key1320, 1), (key1558, 1), (key1395, 1), (key1595, -1), (key1300, -1)]

def rawRow379 : Integer.Sparse Key := [(key245, -2), (key243, 1), (key245, 1), (key266, 2), (key255, -1), (key266, -1), (key275, -1), (key276, -1), (key270, 1), (key276, 1), (key311, 2), (key309, -1), (key311, -1), (key334, -2), (key323, 1), (key334, 1), (key344, 1), (key345, 1), (key338, -1), (key345, -1), (key403, -2), (key392, 1), (key403, 1), (key424, 2), (key413, -1), (key424, -1), (key479, -1), (key485, -1), (key473, 1), (key485, 1), (key576, 1), (key577, 1), (key571, -1), (key577, -1), (key587, -1), (key588, -1), (key581, 1), (key588, 1), (key605, 1), (key611, 1), (key599, -1), (key611, -1)]

def rawRow380 : Integer.Sparse Key := [(key245, -2), (key245, 1), (key243, 1), (key266, 2), (key266, -1), (key255, -1), (key276, -1), (key275, -1), (key276, 1), (key270, 1), (key311, 2), (key311, -1), (key309, -1), (key334, -2), (key334, 1), (key323, 1), (key345, 1), (key344, 1), (key345, -1), (key338, -1), (key403, -2), (key403, 1), (key392, 1), (key424, 2), (key424, -1), (key413, -1), (key485, -1), (key479, -1), (key485, 1), (key473, 1), (key577, 1), (key576, 1), (key577, -1), (key571, -1), (key588, -1), (key587, -1), (key588, 1), (key581, 1), (key611, 1), (key605, 1), (key611, -1), (key599, -1)]

def rawRow382 : Integer.Sparse Key := [(key266, -2), (key255, 1), (key266, 1), (key275, 2), (key243, -1), (key275, -1), (key266, -1), (key276, -1), (key245, 1), (key276, 1), (key338, 2), (key323, -1), (key338, -1), (key344, -2), (key309, 1), (key344, 1), (key334, 1), (key345, 1), (key311, -1), (key345, -1), (key473, -2), (key413, 1), (key473, 1), (key479, 2), (key392, -1), (key479, -1), (key424, -1), (key485, -1), (key403, 1), (key485, 1), (key599, 1), (key613, 1), (key581, -1), (key613, -1), (key605, -1), (key614, -1), (key571, 1), (key614, 1), (key587, 1), (key616, 1), (key576, -1), (key616, -1)]

def rawRow383 : Integer.Sparse Key := [(key266, -2), (key266, 1), (key255, 1), (key275, 2), (key275, -1), (key243, -1), (key276, -1), (key266, -1), (key276, 1), (key245, 1), (key338, 2), (key338, -1), (key323, -1), (key344, -2), (key344, 1), (key309, 1), (key345, 1), (key334, 1), (key345, -1), (key311, -1), (key473, -2), (key473, 1), (key413, 1), (key479, 2), (key479, -1), (key392, -1), (key485, -1), (key424, -1), (key485, 1), (key403, 1), (key613, 1), (key599, 1), (key613, -1), (key581, -1), (key614, -1), (key605, -1), (key614, 1), (key571, 1), (key616, 1), (key587, 1), (key616, -1), (key576, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow384 : Integer.Sparse Key := [(key270, -2), (key275, 1), (key276, 1), (key245, 2), (key266, -1), (key276, -1), (key243, -1), (key245, -1), (key255, 1), (key266, 1), (key334, 2), (key344, -1), (key345, -1), (key311, -2), (key338, 1), (key345, 1), (key309, 1), (key311, 1), (key323, -1), (key334, -1), (key424, -2), (key479, 1), (key485, 1), (key403, 2), (key473, -1), (key485, -1), (key392, -1), (key403, -1), (key413, 1), (key424, 1), (key587, 1), (key588, 1), (key605, -1), (key611, -1), (key576, -1), (key577, -1), (key599, 1), (key611, 1), (key571, 1), (key577, 1), (key581, -1), (key588, -1)]

def rawRow385 : Integer.Sparse Key := [(key270, -2), (key276, 1), (key275, 1), (key245, 2), (key276, -1), (key266, -1), (key245, -1), (key243, -1), (key266, 1), (key255, 1), (key334, 2), (key345, -1), (key344, -1), (key311, -2), (key345, 1), (key338, 1), (key311, 1), (key309, 1), (key334, -1), (key323, -1), (key424, -2), (key485, 1), (key479, 1), (key403, 2), (key485, -1), (key473, -1), (key403, -1), (key392, -1), (key424, 1), (key413, 1), (key588, 1), (key587, 1), (key611, -1), (key605, -1), (key577, -1), (key576, -1), (key611, 1), (key599, 1), (key577, 1), (key571, 1), (key588, -1), (key581, -1)]

end MUB6.Certificate.GramRows

end OAI
end


