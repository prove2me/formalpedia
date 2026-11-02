-- Prove2me | Definitions.Def_OAIQ106D101
-- name    : OAIQ106D101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:02:03.024437+00:00
-- url     : https://prove2.me/theorems/5137df64-a522-4488-adda-ea59ae56e776
-- title:
--   Definitions bundle OAIQ106D101 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 482 declarations of OpenAI's Lean: 482 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow3361`, `OAI.MUB6.Certificate.GramRows.rawRow3362`, `OAI.MUB6.Certificate.GramRows.rawRow3363`, `OAI.MUB6.Certificate.GramRows.rawRow3364`, `OAI.MUB6.Certificate.GramRows.rawRow3365`, `OAI.MUB6.Certificate.GramRows.rawRow3366`, `OAI.MUB6.Certificate.GramRows.rawRow3367`, `OAI.MUB6.Certificate.GramRows.rawRow3368`, `OAI.MUB6.Certificate.GramRows.rawRow3369`, `OAI.MUB6.Certificate.GramRows.rawRow3370`, `OAI.MUB6.Certificate.GramRows.rawRow3371`, `OAI.MUB6.Certificate.GramRows.rawRow3372`, `OAI.MUB6.Certificate.GramRows.rawRow3373`, `OAI.MUB6.Certificate.GramRows.rawRow3374`, `OAI.MUB6.Certificate.GramRows.rawRow3375`, `OAI.MUB6.Certificate.GramRows.rawRow3376`, `OAI.MUB6.Certificate.GramRows.rawRow3377`, `OAI.MUB6.Certificate.GramRows.rawRow3378`, `OAI.MUB6.Certificate.GramRows.rawRow3379`, `OAI.MUB6.Certificate.GramRows.rawRow3380`, `OAI.MUB6.Certificate.GramRows.rawRow3381`, `OAI.MUB6.Certificate.GramRows.rawRow3382`, `OAI.MUB6.Certificate.GramRows.rawRow3383`, `OAI.MUB6.Certificate.GramRows.rawRow3384`, `OAI.MUB6.Certificate.GramRows.rawRow3385`, `OAI.MUB6.Certificate.GramRows.rawRow339`, `OAI.MUB6.Certificate.GramRows.rawRow3416`, `OAI.MUB6.Certificate.GramRows.rawRow3417`, `OAI.MUB6.Certificate.GramRows.rawRow3418`, `OAI.MUB6.Certificate.GramRows.rawRow3419`, `OAI.MUB6.Certificate.GramRows.rawRow3420`, `OAI.MUB6.Certificate.GramRows.rawRow3421`, `OAI.MUB6.Certificate.GramRows.rawRow3422`, `OAI.MUB6.Certificate.GramRows.rawRow3423`, `OAI.MUB6.Certificate.GramRows.rawRow3424`, `OAI.MUB6.Certificate.GramRows.rawRow3425`, `OAI.MUB6.Certificate.GramRows.rawRow3426`, `OAI.MUB6.Certificate.GramRows.rawRow3427`, `OAI.MUB6.Certificate.GramRows.rawRow3428`, `OAI.MUB6.Certificate.GramRows.rawRow3429` and 442 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block10`, `MutuallyUnbiased_GramRows_Block50`, `MutuallyUnbiased_GramRows_Block51`, `MutuallyUnbiased_GramRows_Block52`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block54`, `MutuallyUnbiased_GramRows_Block55`, `MutuallyUnbiased_GramRows_Block56`, `MutuallyUnbiased_GramRows_Block57`, `MutuallyUnbiased_GramRows_Block58`, `MutuallyUnbiased_GramRows_Block7`, `MutuallyUnbiased_GramRows_Block8`, `MutuallyUnbiased_GramRows_Block9`, `MutuallyUnbiased_MixedData_Source0`, `MutuallyUnbiased_MixedSemantics_Values15`.
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

def rawRow35 : Integer.Sparse Key := [(key578, -1), (key578, -1), (key583, 2), (key568, 1), (key568, 1), (key601, -1), (key601, -1), (key572, -2), (key595, 1), (key595, 1), (key335, 1), (key335, 1), (key340, -2), (key267, -1), (key267, -1), (key475, 1), (key475, 1), (key271, 2), (key469, -1), (key469, -1), (key305, -1), (key305, -1), (key328, 1), (key328, 1), (key239, 1), (key239, 1), (key418, -1), (key418, -1), (key260, -1), (key260, -1), (key397, 1), (key397, 1), (key302, 2), (key316, -1), (key316, -1), (key236, -2), (key406, 1), (key406, 1), (key248, 1), (key248, 1), (key316, -1), (key316, -1)]

def rawRow36 : Integer.Sparse Key := [(key578, -1), (key583, -1), (key578, 2), (key593, 1), (key601, 1), (key568, -1), (key593, -1), (key595, -2), (key572, 1), (key595, 1), (key335, 1), (key340, 1), (key335, -2), (key467, -1), (key475, -1), (key267, 1), (key467, 1), (key469, 2), (key271, -1), (key469, -1), (key319, -1), (key328, -1), (key305, 1), (key319, 1), (key409, 1), (key418, 1), (key239, -1), (key409, -1), (key397, -1), (key442, -1), (key260, 1), (key442, 1), (key316, 2), (key302, -1), (key316, -1), (key406, -2), (key236, 1), (key406, 1), (key316, 1), (key435, 1), (key248, -1), (key435, -1)]

def rawRow37 : Integer.Sparse Key := [(key583, -1), (key578, -1), (key578, 2), (key601, 1), (key593, 1), (key593, -1), (key568, -1), (key595, -2), (key595, 1), (key572, 1), (key340, 1), (key335, 1), (key335, -2), (key475, -1), (key467, -1), (key467, 1), (key267, 1), (key469, 2), (key469, -1), (key271, -1), (key328, -1), (key319, -1), (key319, 1), (key305, 1), (key418, 1), (key409, 1), (key409, -1), (key239, -1), (key442, -1), (key397, -1), (key442, 1), (key260, 1), (key316, 2), (key316, -1), (key302, -1), (key406, -2), (key406, 1), (key236, 1), (key435, 1), (key316, 1), (key435, -1), (key248, -1)]

def rawRow40 : Integer.Sparse Key := [(key593, -1), (key601, -1), (key595, 2), (key578, 1), (key583, 1), (key572, -1), (key595, -1), (key578, -2), (key568, 1), (key593, 1), (key467, 1), (key475, 1), (key469, -2), (key335, -1), (key340, -1), (key271, 1), (key469, 1), (key335, 2), (key267, -1), (key467, -1), (key409, -1), (key418, -1), (key397, 1), (key442, 1), (key319, 1), (key328, 1), (key260, -1), (key442, -1), (key305, -1), (key319, -1), (key239, 1), (key409, 1), (key406, 2), (key385, -1), (key435, -1), (key316, -2), (key248, 1), (key435, 1), (key302, 1), (key316, 1), (key236, -1), (key406, -1)]

def rawRow41 : Integer.Sparse Key := [(key601, -1), (key593, -1), (key595, 2), (key583, 1), (key578, 1), (key595, -1), (key572, -1), (key578, -2), (key593, 1), (key568, 1), (key475, 1), (key467, 1), (key469, -2), (key340, -1), (key335, -1), (key469, 1), (key271, 1), (key335, 2), (key467, -1), (key267, -1), (key418, -1), (key409, -1), (key442, 1), (key397, 1), (key328, 1), (key319, 1), (key442, -1), (key260, -1), (key319, -1), (key305, -1), (key409, 1), (key239, 1), (key406, 2), (key435, -1), (key385, -1), (key316, -2), (key435, 1), (key248, 1), (key316, 1), (key302, 1), (key406, -1), (key236, -1)]

def rawRow42 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1302, 2), (key1316, 1), (key1316, 1), (key1339, -1), (key1339, -1), (key1329, -2), (key1345, 1), (key1345, 1), (key1391, 1), (key1391, 1), (key1397, -2), (key1546, -1), (key1546, -1), (key1774, 1), (key1774, 1), (key1559, 2), (key1780, -1), (key1780, -1), (key1424, -1), (key1424, -1), (key1457, 1), (key1457, 1), (key1573, 1), (key1573, 1), (key1790, -1), (key1790, -1), (key1659, -1), (key1659, -1), (key1817, 1), (key1817, 1), (key1447, 2), (key1466, -1), (key1466, -1), (key1596, -2), (key1798, 1), (key1798, 1), (key1667, 1), (key1667, 1), (key1825, -1), (key1825, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow422 : Integer.Sparse Key := [(key1295, -1), (key1295, -1), (key1291, 2), (key1336, 1), (key1336, 1), (key1311, -1), (key1311, -1), (key1343, -2), (key1324, 1), (key1324, 1), (key1390, 1), (key1390, 1), (key1386, -2), (key1771, -1), (key1771, -1), (key1541, 1), (key1541, 1), (key1778, 2), (key1554, -1), (key1554, -1), (key1454, -1), (key1454, -1), (key1419, 1), (key1419, 1), (key1787, 1), (key1787, 1), (key1568, -1), (key1568, -1), (key1815, -1), (key1815, -1), (key1657, 1), (key1657, 1), (key1464, 2), (key1442, -1), (key1442, -1), (key1796, -2), (key1591, 1), (key1591, 1), (key1823, 1), (key1823, 1), (key1665, -1), (key1665, -1)]

def rawRow427 : Integer.Sparse Key := [(key1336, -1), (key1336, -1), (key1343, 2), (key1295, 1), (key1295, 1), (key1324, -1), (key1324, -1), (key1291, -2), (key1311, 1), (key1311, 1), (key1771, 1), (key1771, 1), (key1778, -2), (key1390, -1), (key1390, -1), (key1554, 1), (key1554, 1), (key1386, 2), (key1541, -1), (key1541, -1), (key1787, -1), (key1787, -1), (key1815, 1), (key1815, 1), (key1454, 1), (key1454, 1), (key1657, -1), (key1657, -1), (key1419, -1), (key1419, -1), (key1568, 1), (key1568, 1), (key1796, 2), (key1823, -1), (key1823, -1), (key1464, -2), (key1665, 1), (key1665, 1), (key1442, 1), (key1442, 1), (key1591, -1), (key1591, -1)]

def rawRow432 : Integer.Sparse Key := [(key1390, -1), (key1390, -1), (key1386, 2), (key1454, 1), (key1454, 1), (key1419, -1), (key1419, -1), (key1464, -2), (key1442, 1), (key1442, 1), (key1295, 1), (key1295, 1), (key1291, -2), (key1787, -1), (key1787, -1), (key1568, 1), (key1568, 1), (key1796, 2), (key1591, -1), (key1591, -1), (key1336, -1), (key1336, -1), (key1311, 1), (key1311, 1), (key1771, 1), (key1771, 1), (key1541, -1), (key1541, -1), (key1823, -1), (key1823, -1), (key1665, 1), (key1665, 1), (key1343, 2), (key1324, -1), (key1324, -1), (key1778, -2), (key1554, 1), (key1554, 1), (key1815, 1), (key1815, 1), (key1657, -1), (key1657, -1)]

def rawRow437 : Integer.Sparse Key := [(key1454, -1), (key1454, -1), (key1464, 2), (key1390, 1), (key1390, 1), (key1442, -1), (key1442, -1), (key1386, -2), (key1419, 1), (key1419, 1), (key1787, 1), (key1787, 1), (key1796, -2), (key1295, -1), (key1295, -1), (key1591, 1), (key1591, 1), (key1291, 2), (key1568, -1), (key1568, -1), (key1771, -1), (key1771, -1), (key1823, 1), (key1823, 1), (key1336, 1), (key1336, 1), (key1665, -1), (key1665, -1), (key1311, -1), (key1311, -1), (key1541, 1), (key1541, 1), (key1778, 2), (key1815, -1), (key1815, -1), (key1343, -2), (key1657, 1), (key1657, 1), (key1324, 1), (key1324, 1), (key1554, -1), (key1554, -1)]

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

def rawRow3361 : Integer.Sparse Key := [(key2937, -2), (key2783, -2), (key2779, -2), (key2942, 1), (key2791, 1), (key2937, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2949, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2826, -1), (key2949, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2975, -1), (key2857, -1), (key2973, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2982, 1), (key2867, 1), (key2973, 1), (key2629, 1), (key2852, 1), (key2625, 1)]

def rawRow3362 : Integer.Sparse Key := [(key2791, -2), (key2791, -2), (key2942, -2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2937, 1), (key2937, 1), (key2826, 2), (key2826, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2723, -1), (key2723, -1), (key2867, -1), (key2867, -1), (key2982, -1), (key2982, -1), (key2637, 1), (key2637, 1), (key2857, 1), (key2857, 1), (key2975, 1), (key2975, 1)]

def rawRow3363 : Integer.Sparse Key := [(key2791, -2), (key2942, -2), (key2791, -2), (key2783, 1), (key2937, 1), (key2668, 1), (key2937, 1), (key2668, 1), (key2783, 1), (key2826, 2), (key2959, 2), (key2826, 2), (key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2867, -1), (key2982, -1), (key2723, -1), (key2982, -1), (key2723, -1), (key2867, -1), (key2857, 1), (key2975, 1), (key2637, 1), (key2975, 1), (key2637, 1), (key2857, 1)]

def rawRow3364 : Integer.Sparse Key := [(key2942, -2), (key2791, -2), (key2791, -2), (key2937, 1), (key2783, 1), (key2937, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2959, 2), (key2826, 2), (key2826, 2), (key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2867, -1), (key2982, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2975, 1), (key2857, 1), (key2975, 1), (key2637, 1), (key2857, 1), (key2637, 1)]

def rawRow3365 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2949, -2), (key2699, 1), (key2703, 1), (key2852, 1), (key2857, 1), (key2973, 1), (key2975, 1), (key2779, 2), (key2783, 2), (key2937, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2867, -1), (key2973, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2779, -1), (key2791, -1), (key2937, -1), (key2942, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2826, 1), (key2949, 1), (key2959, 1)]

def rawRow3366 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2949, -2), (key2703, 1), (key2699, 1), (key2857, 1), (key2852, 1), (key2975, 1), (key2973, 1), (key2783, 2), (key2779, 2), (key2937, 2), (key2629, -1), (key2625, -1), (key2867, -1), (key2852, -1), (key2982, -1), (key2973, -1), (key2668, -1), (key2664, -1), (key2791, -1), (key2779, -1), (key2942, -1), (key2937, -1), (key2613, 1), (key2609, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2949, 1)]

def rawRow3367 : Integer.Sparse Key := [(key2802, -2), (key2949, -2), (key2806, -2), (key2852, 1), (key2973, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2779, 2), (key2937, 2), (key2783, 2), (key2852, -1), (key2973, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2779, -1), (key2937, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2802, 1), (key2949, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2826, 1)]

def rawRow3368 : Integer.Sparse Key := [(key2949, -2), (key2802, -2), (key2806, -2), (key2973, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2857, 1), (key2703, 1), (key2937, 2), (key2779, 2), (key2783, 2), (key2973, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2867, -1), (key2629, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2791, -1), (key2668, -1), (key2949, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2826, 1), (key2613, 1)]

def rawRow3369 : Integer.Sparse Key := [(key2806, -2), (key2949, -2), (key2802, -2), (key2857, 1), (key2975, 1), (key2703, 1), (key2973, 1), (key2699, 1), (key2852, 1), (key2783, 2), (key2937, 2), (key2779, 2), (key2867, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2625, -1), (key2852, -1), (key2791, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2664, -1), (key2779, -1), (key2826, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2609, 1), (key2802, 1)]

def rawRow3370 : Integer.Sparse Key := [(key2949, -2), (key2806, -2), (key2802, -2), (key2975, 1), (key2857, 1), (key2973, 1), (key2703, 1), (key2852, 1), (key2699, 1), (key2937, 2), (key2783, 2), (key2779, 2), (key2982, -1), (key2867, -1), (key2973, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2942, -1), (key2791, -1), (key2937, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2959, 1), (key2826, 1), (key2949, 1), (key2613, 1), (key2802, 1), (key2609, 1)]

def rawRow3371 : Integer.Sparse Key := [(key2857, -2), (key2896, -2), (key2975, -2), (key2703, 1), (key2736, 1), (key2806, 1), (key2894, 1), (key2949, 1), (key2973, 1), (key2867, 2), (key2903, 2), (key2982, 2), (key2629, -1), (key2647, -1), (key2783, -1), (key2894, -1), (key2937, -1), (key2973, -1), (key2723, -1), (key2746, -1), (key2826, -1), (key2903, -1), (key2959, -1), (key2982, -1), (key2637, 1), (key2652, 1), (key2791, 1), (key2896, 1), (key2942, 1), (key2975, 1)]

def rawRow3372 : Integer.Sparse Key := [(key2896, -2), (key2857, -2), (key2975, -2), (key2736, 1), (key2703, 1), (key2894, 1), (key2806, 1), (key2973, 1), (key2949, 1), (key2903, 2), (key2867, 2), (key2982, 2), (key2647, -1), (key2629, -1), (key2894, -1), (key2783, -1), (key2973, -1), (key2937, -1), (key2746, -1), (key2723, -1), (key2903, -1), (key2826, -1), (key2982, -1), (key2959, -1), (key2652, 1), (key2637, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2942, 1)]

def rawRow3373 : Integer.Sparse Key := [(key2857, -2), (key2975, -2), (key2896, -2), (key2806, 1), (key2949, 1), (key2703, 1), (key2973, 1), (key2736, 1), (key2894, 1), (key2867, 2), (key2982, 2), (key2903, 2), (key2783, -1), (key2937, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2826, -1), (key2959, -1), (key2723, -1), (key2982, -1), (key2746, -1), (key2903, -1), (key2791, 1), (key2942, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2896, 1)]

def rawRow3374 : Integer.Sparse Key := [(key2975, -2), (key2857, -2), (key2896, -2), (key2949, 1), (key2806, 1), (key2973, 1), (key2703, 1), (key2894, 1), (key2736, 1), (key2982, 2), (key2867, 2), (key2903, 2), (key2937, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2894, -1), (key2647, -1), (key2959, -1), (key2826, -1), (key2982, -1), (key2723, -1), (key2903, -1), (key2746, -1), (key2942, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2896, 1), (key2652, 1)]

def rawRow3375 : Integer.Sparse Key := [(key2896, -2), (key2975, -2), (key2857, -2), (key2894, 1), (key2973, 1), (key2736, 1), (key2949, 1), (key2703, 1), (key2806, 1), (key2903, 2), (key2982, 2), (key2867, 2), (key2894, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2629, -1), (key2783, -1), (key2903, -1), (key2982, -1), (key2746, -1), (key2959, -1), (key2723, -1), (key2826, -1), (key2896, 1), (key2975, 1), (key2652, 1), (key2942, 1), (key2637, 1), (key2791, 1)]

def rawRow3376 : Integer.Sparse Key := [(key2975, -2), (key2896, -2), (key2857, -2), (key2973, 1), (key2894, 1), (key2949, 1), (key2736, 1), (key2806, 1), (key2703, 1), (key2982, 2), (key2903, 2), (key2867, 2), (key2973, -1), (key2894, -1), (key2937, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2982, -1), (key2903, -1), (key2959, -1), (key2746, -1), (key2826, -1), (key2723, -1), (key2975, 1), (key2896, 1), (key2942, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

def rawRow3377 : Integer.Sparse Key := [(key2826, -2), (key2826, -2), (key2959, -2), (key2723, 1), (key2723, 1), (key2867, 1), (key2867, 1), (key2982, 1), (key2982, 1), (key2791, 2), (key2791, 2), (key2942, 2), (key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2937, -1), (key2937, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2949, 1), (key2949, 1)]

def rawRow3378 : Integer.Sparse Key := [(key2826, -2), (key2959, -2), (key2826, -2), (key2867, 1), (key2982, 1), (key2723, 1), (key2982, 1), (key2723, 1), (key2867, 1), (key2791, 2), (key2942, 2), (key2791, 2), (key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2783, -1), (key2937, -1), (key2668, -1), (key2937, -1), (key2668, -1), (key2783, -1), (key2806, 1), (key2949, 1), (key2613, 1), (key2949, 1), (key2613, 1), (key2806, 1)]

def rawRow3379 : Integer.Sparse Key := [(key2959, -2), (key2826, -2), (key2826, -2), (key2982, 1), (key2867, 1), (key2982, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2942, 2), (key2791, 2), (key2791, 2), (key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2949, 1), (key2806, 1), (key2949, 1), (key2613, 1), (key2806, 1), (key2613, 1)]

def rawRow3380 : Integer.Sparse Key := [(key2867, -2), (key2903, -2), (key2982, -2), (key2723, 1), (key2746, 1), (key2826, 1), (key2903, 1), (key2959, 1), (key2982, 1), (key2857, 2), (key2896, 2), (key2975, 2), (key2637, -1), (key2652, -1), (key2791, -1), (key2896, -1), (key2942, -1), (key2975, -1), (key2703, -1), (key2736, -1), (key2806, -1), (key2894, -1), (key2949, -1), (key2973, -1), (key2629, 1), (key2647, 1), (key2783, 1), (key2894, 1), (key2937, 1), (key2973, 1)]

def rawRow3381 : Integer.Sparse Key := [(key2903, -2), (key2867, -2), (key2982, -2), (key2746, 1), (key2723, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2959, 1), (key2896, 2), (key2857, 2), (key2975, 2), (key2652, -1), (key2637, -1), (key2896, -1), (key2791, -1), (key2975, -1), (key2942, -1), (key2736, -1), (key2703, -1), (key2894, -1), (key2806, -1), (key2973, -1), (key2949, -1), (key2647, 1), (key2629, 1), (key2894, 1), (key2783, 1), (key2973, 1), (key2937, 1)]

def rawRow3382 : Integer.Sparse Key := [(key2867, -2), (key2982, -2), (key2903, -2), (key2826, 1), (key2959, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2857, 2), (key2975, 2), (key2896, 2), (key2791, -1), (key2942, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2806, -1), (key2949, -1), (key2703, -1), (key2973, -1), (key2736, -1), (key2894, -1), (key2783, 1), (key2937, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2894, 1)]

def rawRow3383 : Integer.Sparse Key := [(key2982, -2), (key2867, -2), (key2903, -2), (key2959, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2903, 1), (key2746, 1), (key2975, 2), (key2857, 2), (key2896, 2), (key2942, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2896, -1), (key2652, -1), (key2949, -1), (key2806, -1), (key2973, -1), (key2703, -1), (key2894, -1), (key2736, -1), (key2937, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2894, 1), (key2647, 1)]

def rawRow3384 : Integer.Sparse Key := [(key2903, -2), (key2982, -2), (key2867, -2), (key2903, 1), (key2982, 1), (key2746, 1), (key2959, 1), (key2723, 1), (key2826, 1), (key2896, 2), (key2975, 2), (key2857, 2), (key2896, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2637, -1), (key2791, -1), (key2894, -1), (key2973, -1), (key2736, -1), (key2949, -1), (key2703, -1), (key2806, -1), (key2894, 1), (key2973, 1), (key2647, 1), (key2937, 1), (key2629, 1), (key2783, 1)]

def rawRow3385 : Integer.Sparse Key := [(key2982, -2), (key2903, -2), (key2867, -2), (key2982, 1), (key2903, 1), (key2959, 1), (key2746, 1), (key2826, 1), (key2723, 1), (key2975, 2), (key2896, 2), (key2857, 2), (key2975, -1), (key2896, -1), (key2942, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2973, -1), (key2894, -1), (key2949, -1), (key2736, -1), (key2806, -1), (key2703, -1), (key2973, 1), (key2894, 1), (key2937, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

def rawRow3416 : Integer.Sparse Key := [(key2406, -2), (key2437, -2), (key2443, -2), (key2406, 2), (key2411, 2), (key2443, 2), (key2843, 2), (key2966, 2), (key2968, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2880, -1), (key2968, -1), (key2989, -1), (key2887, -2), (key2889, -2), (key2995, -2), (key2598, 1), (key2600, 1), (key2887, 1), (key2910, 1), (key2995, 1), (key3002, 1)]

def rawRow3417 : Integer.Sparse Key := [(key2406, -2), (key2443, -2), (key2437, -2), (key2411, 2), (key2406, 2), (key2443, 2), (key2843, 2), (key2968, 2), (key2966, 2), (key2593, -1), (key2587, -1), (key2880, -1), (key2843, -1), (key2989, -1), (key2968, -1), (key2889, -2), (key2887, -2), (key2995, -2), (key2600, 1), (key2598, 1), (key2910, 1), (key2887, 1), (key3002, 1), (key2995, 1)]

def rawRow3418 : Integer.Sparse Key := [(key2437, -2), (key2406, -2), (key2443, -2), (key2406, 2), (key2443, 2), (key2411, 2), (key2966, 2), (key2843, 2), (key2968, 2), (key2843, -1), (key2968, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2887, -2), (key2995, -2), (key2889, -2), (key2887, 1), (key2995, 1), (key2598, 1), (key3002, 1), (key2600, 1), (key2910, 1)]

def rawRow3419 : Integer.Sparse Key := [(key2437, -2), (key2443, -2), (key2406, -2), (key2443, 2), (key2406, 2), (key2411, 2), (key2966, 2), (key2968, 2), (key2843, 2), (key2968, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2880, -1), (key2593, -1), (key2995, -2), (key2887, -2), (key2889, -2), (key2995, 1), (key2887, 1), (key3002, 1), (key2598, 1), (key2910, 1), (key2600, 1)]

def rawRow3420 : Integer.Sparse Key := [(key2443, -2), (key2406, -2), (key2437, -2), (key2411, 2), (key2443, 2), (key2406, 2), (key2968, 2), (key2843, 2), (key2966, 2), (key2880, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2587, -1), (key2843, -1), (key2889, -2), (key2995, -2), (key2887, -2), (key2910, 1), (key3002, 1), (key2600, 1), (key2995, 1), (key2598, 1), (key2887, 1)]

def rawRow3421 : Integer.Sparse Key := [(key2443, -2), (key2437, -2), (key2406, -2), (key2443, 2), (key2411, 2), (key2406, 2), (key2968, 2), (key2966, 2), (key2843, 2), (key2989, -1), (key2880, -1), (key2968, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2995, -2), (key2889, -2), (key2887, -2), (key3002, 1), (key2910, 1), (key2995, 1), (key2600, 1), (key2887, 1), (key2598, 1)]

def rawRow3422 : Integer.Sparse Key := [(key2411, -2), (key2443, -2), (key2443, -2), (key2406, 2), (key2406, 2), (key2437, 2), (key2880, 2), (key2989, 2), (key2989, 2), (key2587, -1), (key2587, -1), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, 1), (key2600, 1), (key2889, 1), (key2889, 1), (key2995, 1), (key2995, 1)]

def rawRow3423 : Integer.Sparse Key := [(key2443, -2), (key2411, -2), (key2443, -2), (key2406, 2), (key2437, 2), (key2406, 2), (key2989, 2), (key2880, 2), (key2989, 2), (key2843, -1), (key2966, -1), (key2587, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, 1), (key2995, 1), (key2600, 1), (key2995, 1), (key2600, 1), (key2889, 1)]

def rawRow3424 : Integer.Sparse Key := [(key2443, -2), (key2443, -2), (key2411, -2), (key2437, 2), (key2406, 2), (key2406, 2), (key2989, 2), (key2989, 2), (key2880, 2), (key2966, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, 1), (key2889, 1), (key2995, 1), (key2600, 1), (key2889, 1), (key2600, 1)]

def rawRow3425 : Integer.Sparse Key := [(key2472, -2), (key2503, -2), (key2509, -2), (key2480, 2), (key2484, 2), (key2524, 2), (key2406, 2), (key2437, 2), (key2443, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2910, -1), (key2995, -1), (key3002, -1), (key2766, -2), (key2772, -2), (key2931, -2), (key2587, 1), (key2593, 1), (key2843, 1), (key2880, 1), (key2968, 1), (key2989, 1)]

def rawRow3426 : Integer.Sparse Key := [(key2472, -2), (key2509, -2), (key2503, -2), (key2484, 2), (key2480, 2), (key2524, 2), (key2406, 2), (key2443, 2), (key2437, 2), (key2600, -1), (key2598, -1), (key2910, -1), (key2887, -1), (key3002, -1), (key2995, -1), (key2772, -2), (key2766, -2), (key2931, -2), (key2593, 1), (key2587, 1), (key2880, 1), (key2843, 1), (key2989, 1), (key2968, 1)]

def rawRow3427 : Integer.Sparse Key := [(key2503, -2), (key2472, -2), (key2509, -2), (key2480, 2), (key2524, 2), (key2484, 2), (key2437, 2), (key2406, 2), (key2443, 2), (key2887, -1), (key2995, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2766, -2), (key2931, -2), (key2772, -2), (key2843, 1), (key2968, 1), (key2587, 1), (key2989, 1), (key2593, 1), (key2880, 1)]

def rawRow3428 : Integer.Sparse Key := [(key2503, -2), (key2509, -2), (key2472, -2), (key2524, 2), (key2480, 2), (key2484, 2), (key2437, 2), (key2443, 2), (key2406, 2), (key2995, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2910, -1), (key2600, -1), (key2931, -2), (key2766, -2), (key2772, -2), (key2968, 1), (key2843, 1), (key2989, 1), (key2587, 1), (key2880, 1), (key2593, 1)]

def rawRow3429 : Integer.Sparse Key := [(key2509, -2), (key2472, -2), (key2503, -2), (key2484, 2), (key2524, 2), (key2480, 2), (key2443, 2), (key2406, 2), (key2437, 2), (key2910, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2598, -1), (key2887, -1), (key2772, -2), (key2931, -2), (key2766, -2), (key2880, 1), (key2989, 1), (key2593, 1), (key2968, 1), (key2587, 1), (key2843, 1)]

def rawRow3430 : Integer.Sparse Key := [(key2509, -2), (key2503, -2), (key2472, -2), (key2524, 2), (key2484, 2), (key2480, 2), (key2443, 2), (key2437, 2), (key2406, 2), (key3002, -1), (key2910, -1), (key2995, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2931, -2), (key2772, -2), (key2766, -2), (key2989, 1), (key2880, 1), (key2968, 1), (key2593, 1), (key2843, 1), (key2587, 1)]

def rawRow3431 : Integer.Sparse Key := [(key2484, -2), (key2509, -2), (key2524, -2), (key2472, 2), (key2480, 2), (key2503, 2), (key2571, 2), (key2576, 2), (key2580, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2480, -1), (key2437, -1), (key2503, -1), (key2880, -2), (key2910, -2), (key2989, -2), (key2593, 1), (key2600, 1), (key2772, 1), (key2889, 1), (key2931, 1), (key2968, 1)]

def rawRow3432 : Integer.Sparse Key := [(key2484, -2), (key2524, -2), (key2509, -2), (key2480, 2), (key2472, 2), (key2503, 2), (key2571, 2), (key2580, 2), (key2576, 2), (key2390, -1), (key2378, -1), (key2480, -1), (key2406, -1), (key2503, -1), (key2437, -1), (key2910, -2), (key2880, -2), (key2989, -2), (key2600, 1), (key2593, 1), (key2889, 1), (key2772, 1), (key2968, 1), (key2931, 1)]

def rawRow3433 : Integer.Sparse Key := [(key2509, -2), (key2484, -2), (key2524, -2), (key2472, 2), (key2503, 2), (key2480, 2), (key2576, 2), (key2571, 2), (key2580, 2), (key2406, -1), (key2437, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2880, -2), (key2989, -2), (key2910, -2), (key2772, 1), (key2931, 1), (key2593, 1), (key2968, 1), (key2600, 1), (key2889, 1)]

def rawRow3434 : Integer.Sparse Key := [(key2509, -2), (key2524, -2), (key2484, -2), (key2503, 2), (key2472, 2), (key2480, 2), (key2576, 2), (key2580, 2), (key2571, 2), (key2437, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2480, -1), (key2390, -1), (key2989, -2), (key2880, -2), (key2910, -2), (key2931, 1), (key2772, 1), (key2968, 1), (key2593, 1), (key2889, 1), (key2600, 1)]

def rawRow3435 : Integer.Sparse Key := [(key2524, -2), (key2484, -2), (key2509, -2), (key2480, 2), (key2503, 2), (key2472, 2), (key2580, 2), (key2571, 2), (key2576, 2), (key2480, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2378, -1), (key2406, -1), (key2910, -2), (key2989, -2), (key2880, -2), (key2889, 1), (key2968, 1), (key2600, 1), (key2931, 1), (key2593, 1), (key2772, 1)]

def rawRow3436 : Integer.Sparse Key := [(key2524, -2), (key2509, -2), (key2484, -2), (key2503, 2), (key2480, 2), (key2472, 2), (key2580, 2), (key2576, 2), (key2571, 2), (key2503, -1), (key2480, -1), (key2437, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2989, -2), (key2910, -2), (key2880, -2), (key2968, 1), (key2889, 1), (key2931, 1), (key2600, 1), (key2772, 1), (key2593, 1)]

def rawRow3437 : Integer.Sparse Key := [(key2569, -2), (key2576, -2), (key2576, -2), (key2571, 2), (key2571, 2), (key2580, 2), (key2411, 2), (key2443, 2), (key2443, 2), (key2394, -1), (key2394, -1), (key2484, -1), (key2484, -1), (key2524, -1), (key2524, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, 1), (key2378, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1)]

def rawRow3438 : Integer.Sparse Key := [(key2576, -2), (key2569, -2), (key2576, -2), (key2571, 2), (key2580, 2), (key2571, 2), (key2443, 2), (key2411, 2), (key2443, 2), (key2484, -1), (key2524, -1), (key2394, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, 1), (key2503, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2472, 1)]

def rawRow3439 : Integer.Sparse Key := [(key2576, -2), (key2576, -2), (key2569, -2), (key2580, 2), (key2571, 2), (key2571, 2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2394, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, 1), (key2472, 1), (key2503, 1), (key2378, 1), (key2472, 1), (key2378, 1)]

def rawRow3440 : Integer.Sparse Key := [(key2571, -2), (key2576, -2), (key2580, -2), (key2569, 2), (key2571, 2), (key2576, 2), (key2484, 2), (key2509, 2), (key2524, 2), (key2383, -1), (key2394, -1), (key2411, -1), (key2484, -1), (key2443, -1), (key2509, -1), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, 1), (key2390, 1), (key2406, 1), (key2480, 1), (key2437, 1), (key2503, 1)]

def rawRow3441 : Integer.Sparse Key := [(key2571, -2), (key2580, -2), (key2576, -2), (key2571, 2), (key2569, 2), (key2576, 2), (key2484, 2), (key2524, 2), (key2509, 2), (key2394, -1), (key2383, -1), (key2484, -1), (key2411, -1), (key2509, -1), (key2443, -1), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, 1), (key2378, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2437, 1)]

def rawRow3442 : Integer.Sparse Key := [(key2576, -2), (key2571, -2), (key2580, -2), (key2569, 2), (key2576, 2), (key2571, 2), (key2509, 2), (key2484, 2), (key2524, 2), (key2411, -1), (key2443, -1), (key2383, -1), (key2509, -1), (key2394, -1), (key2484, -1), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, 1), (key2437, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2480, 1)]

def rawRow3443 : Integer.Sparse Key := [(key2576, -2), (key2580, -2), (key2571, -2), (key2576, 2), (key2569, 2), (key2571, 2), (key2509, 2), (key2524, 2), (key2484, 2), (key2443, -1), (key2411, -1), (key2509, -1), (key2383, -1), (key2484, -1), (key2394, -1), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2480, 1), (key2390, 1)]

def rawRow3444 : Integer.Sparse Key := [(key2580, -2), (key2571, -2), (key2576, -2), (key2571, 2), (key2576, 2), (key2569, 2), (key2524, 2), (key2484, 2), (key2509, 2), (key2484, -1), (key2509, -1), (key2394, -1), (key2443, -1), (key2383, -1), (key2411, -1), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2378, 1), (key2406, 1)]

def rawRow3445 : Integer.Sparse Key := [(key2580, -2), (key2576, -2), (key2571, -2), (key2576, 2), (key2571, 2), (key2569, 2), (key2524, 2), (key2509, 2), (key2484, 2), (key2509, -1), (key2484, -1), (key2443, -1), (key2394, -1), (key2411, -1), (key2383, -1), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, 1), (key2480, 1), (key2437, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

def rawRow3446 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2801, -1), (key2827, -1), (key3011, -1), (key3016, -1), (key2614, 2), (key2807, 2), (key2827, 2), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2630, -1), (key2638, -1), (key2704, -1), (key2724, -1), (key2858, -1), (key2868, -1), (key2657, -2), (key2918, -2), (key2922, -2), (key2657, 1), (key2659, 1), (key2752, 1), (key2757, 1), (key2919, 1), (key2922, 1)]

def rawRow3447 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2827, -1), (key2801, -1), (key3016, -1), (key3011, -1), (key2614, 2), (key2827, 2), (key2807, 2), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2638, -1), (key2630, -1), (key2724, -1), (key2704, -1), (key2868, -1), (key2858, -1), (key2657, -2), (key2922, -2), (key2918, -2), (key2659, 1), (key2657, 1), (key2757, 1), (key2752, 1), (key2922, 1), (key2919, 1)]

def rawRow3448 : Integer.Sparse Key := [(key2801, -1), (key2827, -1), (key2608, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2807, 2), (key2614, 2), (key2827, 2), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2704, -1), (key2858, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2918, -2), (key2657, -2), (key2922, -2), (key2752, 1), (key2919, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2757, 1)]

def rawRow3449 : Integer.Sparse Key := [(key2827, -1), (key2801, -1), (key3016, -1), (key2608, -1), (key2827, -1), (key2614, -1), (key2807, 2), (key2827, 2), (key2614, 2), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key2858, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2724, -1), (key2638, -1), (key2918, -2), (key2922, -2), (key2657, -2), (key2919, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2757, 1), (key2659, 1)]

def rawRow3450 : Integer.Sparse Key := [(key3011, -1), (key3016, -1), (key2614, -1), (key2827, -1), (key2608, -1), (key2801, -1), (key2827, 2), (key2614, 2), (key2807, 2), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2724, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2630, -1), (key2704, -1), (key2922, -2), (key2657, -2), (key2918, -2), (key2757, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2657, 1), (key2752, 1)]

def rawRow3451 : Integer.Sparse Key := [(key3016, -1), (key3011, -1), (key2827, -1), (key2614, -1), (key2801, -1), (key2608, -1), (key2827, 2), (key2807, 2), (key2614, 2), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key2868, -1), (key2724, -1), (key2858, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2922, -2), (key2918, -2), (key2657, -2), (key2922, 1), (key2757, 1), (key2919, 1), (key2659, 1), (key2752, 1), (key2657, 1)]

def rawRow3452 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2659, -2), (key2919, -2), (key2919, -2), (key2657, 1), (key2657, 1), (key2752, 1), (key2752, 1), (key2918, 1), (key2918, 1)]

def rawRow3453 : Integer.Sparse Key := [(key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2919, -2), (key2659, -2), (key2919, -2), (key2752, 1), (key2918, 1), (key2657, 1), (key2918, 1), (key2657, 1), (key2752, 1)]

def rawRow3454 : Integer.Sparse Key := [(key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2919, -2), (key2919, -2), (key2659, -2), (key2918, 1), (key2752, 1), (key2918, 1), (key2657, 1), (key2752, 1), (key2657, 1)]

def rawRow3455 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2851, -1), (key3021, -1), (key2868, -1), (key3025, -1), (key2638, 2), (key2858, 2), (key3022, 2), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2657, -1), (key2659, -1), (key2752, -1), (key2757, -1), (key2919, -1), (key2922, -1), (key2614, -2), (key2807, -2), (key2827, -2), (key2630, 1), (key2638, 1), (key2704, 1), (key2724, 1), (key2858, 1), (key2868, 1)]

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

def rawRow3456 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key3021, -1), (key2851, -1), (key3025, -1), (key2868, -1), (key2638, 2), (key3022, 2), (key2858, 2), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2659, -1), (key2657, -1), (key2757, -1), (key2752, -1), (key2922, -1), (key2919, -1), (key2614, -2), (key2827, -2), (key2807, -2), (key2638, 1), (key2630, 1), (key2724, 1), (key2704, 1), (key2868, 1), (key2858, 1)]

def rawRow3457 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2624, -1), (key3025, -1), (key2630, -1), (key3021, -1), (key2858, 2), (key2638, 2), (key3022, 2), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2752, -1), (key2919, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2807, -2), (key2614, -2), (key2827, -2), (key2704, 1), (key2858, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2724, 1)]

def rawRow3458 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key3025, -1), (key2624, -1), (key3021, -1), (key2630, -1), (key2858, 2), (key3022, 2), (key2638, 2), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2919, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2757, -1), (key2659, -1), (key2807, -2), (key2827, -2), (key2614, -2), (key2858, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2724, 1), (key2638, 1)]

def rawRow3459 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key2630, -1), (key2868, -1), (key2624, -1), (key2851, -1), (key3022, 2), (key2638, 2), (key2858, 2), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2757, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2657, -1), (key2752, -1), (key2827, -2), (key2614, -2), (key2807, -2), (key2724, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2630, 1), (key2704, 1)]

def rawRow3460 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key2868, -1), (key2630, -1), (key2851, -1), (key2624, -1), (key3022, 2), (key2858, 2), (key2638, 2), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2922, -1), (key2757, -1), (key2919, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2827, -2), (key2807, -2), (key2614, -2), (key2868, 1), (key2724, 1), (key2858, 1), (key2638, 1), (key2704, 1), (key2630, 1)]

def rawRow3461 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2704, -1), (key2858, -1), (key2724, -1), (key2868, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2657, 1), (key2659, 1), (key2752, 1), (key2919, 1), (key2757, 1), (key2922, 1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2638, -2), (key2792, -2), (key2858, -2), (key2614, 1), (key2630, 1), (key2669, 1), (key2704, 1), (key2784, 1), (key2807, 1)]

def rawRow3462 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2858, -1), (key2704, -1), (key2868, -1), (key2724, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2659, 1), (key2657, 1), (key2919, 1), (key2752, 1), (key2922, 1), (key2757, 1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2638, -2), (key2858, -2), (key2792, -2), (key2630, 1), (key2614, 1), (key2704, 1), (key2669, 1), (key2807, 1), (key2784, 1)]

def rawRow3463 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2630, -1), (key2868, -1), (key2638, -1), (key2858, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2752, 1), (key2757, 1), (key2657, 1), (key2922, 1), (key2659, 1), (key2919, 1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2792, -2), (key2638, -2), (key2858, -2), (key2669, 1), (key2784, 1), (key2614, 1), (key2807, 1), (key2630, 1), (key2704, 1)]

def rawRow3464 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2868, -1), (key2630, -1), (key2858, -1), (key2638, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2757, 1), (key2752, 1), (key2922, 1), (key2657, 1), (key2919, 1), (key2659, 1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2792, -2), (key2858, -2), (key2638, -2), (key2784, 1), (key2669, 1), (key2807, 1), (key2614, 1), (key2704, 1), (key2630, 1)]

def rawRow3465 : Integer.Sparse Key := [(key2858, -1), (key2868, -1), (key2638, -1), (key2724, -1), (key2630, -1), (key2704, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2919, 1), (key2922, 1), (key2659, 1), (key2757, 1), (key2657, 1), (key2752, 1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2858, -2), (key2638, -2), (key2792, -2), (key2704, 1), (key2807, 1), (key2630, 1), (key2784, 1), (key2614, 1), (key2669, 1)]

def rawRow3466 : Integer.Sparse Key := [(key2868, -1), (key2858, -1), (key2724, -1), (key2638, -1), (key2704, -1), (key2630, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2922, 1), (key2919, 1), (key2757, 1), (key2659, 1), (key2752, 1), (key2657, 1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2858, -2), (key2792, -2), (key2638, -2), (key2807, 1), (key2704, 1), (key2784, 1), (key2630, 1), (key2669, 1), (key2614, 1)]

def rawRow3467 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2659, 2), (key2919, 2), (key2919, 2), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2638, -1), (key2638, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

def rawRow3468 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2919, 2), (key2659, 2), (key2919, 2), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2792, -1), (key2858, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

def rawRow3469 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2919, 2), (key2919, 2), (key2659, 2), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2858, -1), (key2792, -1), (key2858, -1), (key2638, -1), (key2792, -1), (key2638, -1), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

def rawRow3470 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2752, -1), (key2919, -1), (key2757, -1), (key2922, -1), (key2657, 2), (key2752, 2), (key2918, 2), (key2630, 1), (key2638, 1), (key2704, 1), (key2858, 1), (key2724, 1), (key2868, 1), (key2614, -1), (key2630, -1), (key2669, -1), (key2784, -1), (key2704, -1), (key2807, -1), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

def rawRow3471 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2919, -1), (key2752, -1), (key2922, -1), (key2757, -1), (key2657, 2), (key2918, 2), (key2752, 2), (key2638, 1), (key2630, 1), (key2858, 1), (key2704, 1), (key2868, 1), (key2724, 1), (key2630, -1), (key2614, -1), (key2784, -1), (key2669, -1), (key2807, -1), (key2704, -1), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

def rawRow3472 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2657, -1), (key2922, -1), (key2659, -1), (key2919, -1), (key2752, 2), (key2657, 2), (key2918, 2), (key2704, 1), (key2724, 1), (key2630, 1), (key2868, 1), (key2638, 1), (key2858, 1), (key2669, -1), (key2704, -1), (key2614, -1), (key2807, -1), (key2630, -1), (key2784, -1), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

def rawRow3473 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2922, -1), (key2657, -1), (key2919, -1), (key2659, -1), (key2752, 2), (key2918, 2), (key2657, 2), (key2724, 1), (key2704, 1), (key2868, 1), (key2630, 1), (key2858, 1), (key2638, 1), (key2704, -1), (key2669, -1), (key2807, -1), (key2614, -1), (key2784, -1), (key2630, -1), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

def rawRow3474 : Integer.Sparse Key := [(key2919, -1), (key2922, -1), (key2659, -1), (key2757, -1), (key2657, -1), (key2752, -1), (key2918, 2), (key2657, 2), (key2752, 2), (key2858, 1), (key2868, 1), (key2638, 1), (key2724, 1), (key2630, 1), (key2704, 1), (key2784, -1), (key2807, -1), (key2630, -1), (key2704, -1), (key2614, -1), (key2669, -1), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

def rawRow3475 : Integer.Sparse Key := [(key2922, -1), (key2919, -1), (key2757, -1), (key2659, -1), (key2752, -1), (key2657, -1), (key2918, 2), (key2752, 2), (key2657, 2), (key2868, 1), (key2858, 1), (key2724, 1), (key2638, 1), (key2704, 1), (key2630, 1), (key2807, -1), (key2784, -1), (key2704, -1), (key2630, -1), (key2669, -1), (key2614, -1), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

def rawRow3476 : Integer.Sparse Key := [(key2674, -2), (key2796, -2), (key2796, -2), (key2671, 1), (key2671, 1), (key2786, 1), (key2786, 1), (key2794, 1), (key2794, 1), (key2738, 2), (key2898, 2), (key2898, 2), (key2706, -1), (key2706, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2748, -1), (key2748, -1), (key2905, -1), (key2905, -1), (key2913, -1), (key2913, -1), (key2729, 1), (key2729, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

def rawRow3477 : Integer.Sparse Key := [(key2796, -2), (key2674, -2), (key2796, -2), (key2786, 1), (key2794, 1), (key2671, 1), (key2794, 1), (key2671, 1), (key2786, 1), (key2898, 2), (key2738, 2), (key2898, 2), (key2809, -1), (key2860, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2905, -1), (key2913, -1), (key2748, -1), (key2913, -1), (key2748, -1), (key2905, -1), (key2832, 1), (key2883, 1), (key2729, 1), (key2883, 1), (key2729, 1), (key2832, 1)]

def rawRow3478 : Integer.Sparse Key := [(key2796, -2), (key2796, -2), (key2674, -2), (key2794, 1), (key2786, 1), (key2794, 1), (key2671, 1), (key2786, 1), (key2671, 1), (key2898, 2), (key2898, 2), (key2738, 2), (key2860, -1), (key2809, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2706, -1), (key2913, -1), (key2905, -1), (key2913, -1), (key2748, -1), (key2905, -1), (key2748, -1), (key2883, 1), (key2832, 1), (key2883, 1), (key2729, 1), (key2832, 1), (key2729, 1)]

def rawRow3479 : Integer.Sparse Key := [(key2619, -2), (key2832, -2), (key2832, -2), (key2616, 1), (key2616, 1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2649, 2), (key2905, 2), (key2905, 2), (key2632, -1), (key2632, -1), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2654, -1), (key2654, -1), (key2898, -1), (key2898, -1), (key2913, -1), (key2913, -1), (key2642, 1), (key2642, 1), (key2796, 1), (key2796, 1), (key2883, 1), (key2883, 1)]

def rawRow3480 : Integer.Sparse Key := [(key2832, -2), (key2619, -2), (key2832, -2), (key2809, 1), (key2829, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2905, 2), (key2649, 2), (key2905, 2), (key2786, -1), (key2870, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2898, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2898, -1), (key2796, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2796, 1)]

def rawRow3481 : Integer.Sparse Key := [(key2832, -2), (key2832, -2), (key2619, -2), (key2829, 1), (key2809, 1), (key2829, 1), (key2616, 1), (key2809, 1), (key2616, 1), (key2905, 2), (key2905, 2), (key2649, 2), (key2870, -1), (key2786, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2632, -1), (key2913, -1), (key2898, -1), (key2913, -1), (key2654, -1), (key2898, -1), (key2654, -1), (key2883, 1), (key2796, 1), (key2883, 1), (key2642, 1), (key2796, 1), (key2642, 1)]

def rawRow3482 : Integer.Sparse Key := [(key2738, -2), (key2898, -2), (key2898, -2), (key2748, 1), (key2748, 1), (key2905, 1), (key2905, 1), (key2913, 1), (key2913, 1), (key2674, 2), (key2796, 2), (key2796, 2), (key2729, -1), (key2729, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2671, -1), (key2671, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2706, 1), (key2706, 1), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1)]

def rawRow3483 : Integer.Sparse Key := [(key2898, -2), (key2738, -2), (key2898, -2), (key2905, 1), (key2913, 1), (key2748, 1), (key2913, 1), (key2748, 1), (key2905, 1), (key2796, 2), (key2674, 2), (key2796, 2), (key2832, -1), (key2883, -1), (key2729, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2786, -1), (key2794, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2786, -1), (key2809, 1), (key2860, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2809, 1)]

def rawRow3484 : Integer.Sparse Key := [(key2898, -2), (key2898, -2), (key2738, -2), (key2913, 1), (key2905, 1), (key2913, 1), (key2748, 1), (key2905, 1), (key2748, 1), (key2796, 2), (key2796, 2), (key2674, 2), (key2883, -1), (key2832, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2729, -1), (key2794, -1), (key2786, -1), (key2794, -1), (key2671, -1), (key2786, -1), (key2671, -1), (key2860, 1), (key2809, 1), (key2860, 1), (key2706, 1), (key2809, 1), (key2706, 1)]

def rawRow3485 : Integer.Sparse Key := [(key2649, -2), (key2905, -2), (key2905, -2), (key2654, 1), (key2654, 1), (key2898, 1), (key2898, 1), (key2913, 1), (key2913, 1), (key2619, 2), (key2832, 2), (key2832, 2), (key2642, -1), (key2642, -1), (key2796, -1), (key2796, -1), (key2883, -1), (key2883, -1), (key2616, -1), (key2616, -1), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3486 : Integer.Sparse Key := [(key2905, -2), (key2649, -2), (key2905, -2), (key2898, 1), (key2913, 1), (key2654, 1), (key2913, 1), (key2654, 1), (key2898, 1), (key2832, 2), (key2619, 2), (key2832, 2), (key2796, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3487 : Integer.Sparse Key := [(key2905, -2), (key2905, -2), (key2649, -2), (key2913, 1), (key2898, 1), (key2913, 1), (key2654, 1), (key2898, 1), (key2654, 1), (key2832, 2), (key2832, 2), (key2619, 2), (key2883, -1), (key2796, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2642, -1), (key2829, -1), (key2809, -1), (key2829, -1), (key2616, -1), (key2809, -1), (key2616, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3489 : Integer.Sparse Key := [(key1334, -6), (key1308, 2), (key1288, 2), (key1308, 2), (key1769, 6), (key1538, -2), (key1383, -2), (key1538, -2), (key1810, -2), (key1785, -2), (key1810, -2), (key1652, 2), (key1452, 2), (key1652, 2)]

def rawRow3490 : Integer.Sparse Key := [(key1334, -6), (key1308, 2), (key1308, 2), (key1288, 2), (key1769, 6), (key1538, -2), (key1538, -2), (key1383, -2), (key1810, -2), (key1810, -2), (key1785, -2), (key1652, 2), (key1652, 2), (key1452, 2)]

def rawRow3491 : Integer.Sparse Key := [(key1452, -6), (key1383, 2), (key1416, 2), (key1416, 2), (key1785, 6), (key1288, -2), (key1565, -2), (key1565, -2), (key1769, -2), (key1810, -2), (key1810, -2), (key1334, 2), (key1652, 2), (key1652, 2)]

def rawRow3492 : Integer.Sparse Key := [(key1452, -6), (key1416, 2), (key1383, 2), (key1416, 2), (key1785, 6), (key1565, -2), (key1288, -2), (key1565, -2), (key1810, -2), (key1769, -2), (key1810, -2), (key1652, 2), (key1334, 2), (key1652, 2)]

def rawRow3493 : Integer.Sparse Key := [(key1452, -6), (key1416, 2), (key1416, 2), (key1383, 2), (key1785, 6), (key1565, -2), (key1565, -2), (key1288, -2), (key1810, -2), (key1810, -2), (key1769, -2), (key1652, 2), (key1652, 2), (key1334, 2)]

def rawRow3494 : Integer.Sparse Key := [(key1769, -6), (key1785, 2), (key1810, 2), (key1810, 2), (key1334, 6), (key1452, -2), (key1652, -2), (key1652, -2), (key1288, -2), (key1308, -2), (key1308, -2), (key1383, 2), (key1538, 2), (key1538, 2)]

def rawRow3495 : Integer.Sparse Key := [(key1769, -6), (key1810, 2), (key1785, 2), (key1810, 2), (key1334, 6), (key1652, -2), (key1452, -2), (key1652, -2), (key1308, -2), (key1288, -2), (key1308, -2), (key1538, 2), (key1383, 2), (key1538, 2)]

def rawRow3496 : Integer.Sparse Key := [(key1769, -6), (key1810, 2), (key1810, 2), (key1785, 2), (key1334, 6), (key1652, -2), (key1652, -2), (key1452, -2), (key1308, -2), (key1308, -2), (key1288, -2), (key1538, 2), (key1538, 2), (key1383, 2)]

def rawRow3497 : Integer.Sparse Key := [(key1785, -6), (key1769, 2), (key1810, 2), (key1810, 2), (key1452, 6), (key1334, -2), (key1652, -2), (key1652, -2), (key1383, -2), (key1416, -2), (key1416, -2), (key1288, 2), (key1565, 2), (key1565, 2)]

def rawRow3498 : Integer.Sparse Key := [(key1785, -6), (key1810, 2), (key1769, 2), (key1810, 2), (key1452, 6), (key1652, -2), (key1334, -2), (key1652, -2), (key1416, -2), (key1383, -2), (key1416, -2), (key1565, 2), (key1288, 2), (key1565, 2)]

def rawRow3499 : Integer.Sparse Key := [(key1785, -6), (key1810, 2), (key1810, 2), (key1769, 2), (key1452, 6), (key1652, -2), (key1652, -2), (key1334, -2), (key1416, -2), (key1416, -2), (key1383, -2), (key1565, 2), (key1565, 2), (key1288, 2)]

def rawRow3500 : Integer.Sparse Key := [(key2647, -2), (key2647, -2), (key2652, -2), (key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2937, 2), (key2937, 2), (key2942, 2), (key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2975, -1), (key2975, -1), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1)]

def rawRow3501 : Integer.Sparse Key := [(key2647, -2), (key2652, -2), (key2647, -2), (key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2937, 2), (key2942, 2), (key2937, 2), (key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1)]

def rawRow3502 : Integer.Sparse Key := [(key2652, -2), (key2647, -2), (key2647, -2), (key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2942, 2), (key2937, 2), (key2937, 2), (key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2975, -1), (key2973, -1), (key2975, -1), (key2949, -1), (key2973, -1), (key2949, -1), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1)]

def rawRow3503 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2949, 2), (key2949, 2), (key2959, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2937, -1), (key2937, -1), (key2973, -1), (key2973, -1), (key2982, -1), (key2982, -1), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1)]

def rawRow3504 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2949, 2), (key2959, 2), (key2949, 2), (key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1)]

def rawRow3505 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2959, 2), (key2949, 2), (key2949, 2), (key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2982, -1), (key2973, -1), (key2982, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1)]

def rawRow3506 : Integer.Sparse Key := [(key2937, -2), (key2937, -2), (key2942, -2), (key2949, 1), (key2949, 1), (key2973, 1), (key2973, 1), (key2975, 1), (key2975, 1), (key2647, 2), (key2647, 2), (key2652, 2), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2613, -1), (key2613, -1), (key2629, -1), (key2629, -1), (key2637, -1), (key2637, -1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1)]

def rawRow3507 : Integer.Sparse Key := [(key2937, -2), (key2942, -2), (key2937, -2), (key2973, 1), (key2975, 1), (key2949, 1), (key2975, 1), (key2949, 1), (key2973, 1), (key2647, 2), (key2652, 2), (key2647, 2), (key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1)]

def rawRow3508 : Integer.Sparse Key := [(key2942, -2), (key2937, -2), (key2937, -2), (key2975, 1), (key2973, 1), (key2975, 1), (key2949, 1), (key2973, 1), (key2949, 1), (key2652, 2), (key2647, 2), (key2647, 2), (key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2637, -1), (key2629, -1), (key2637, -1), (key2613, -1), (key2629, -1), (key2613, -1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1)]

def rawRow3509 : Integer.Sparse Key := [(key2949, -2), (key2949, -2), (key2959, -2), (key2937, 1), (key2937, 1), (key2973, 1), (key2973, 1), (key2982, 1), (key2982, 1), (key2736, 2), (key2736, 2), (key2746, 2), (key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2723, -1), (key2723, -1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1)]

def rawRow3510 : Integer.Sparse Key := [(key2949, -2), (key2959, -2), (key2949, -2), (key2973, 1), (key2982, 1), (key2937, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2736, 2), (key2746, 2), (key2736, 2), (key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1)]

def rawRow3511 : Integer.Sparse Key := [(key2959, -2), (key2949, -2), (key2949, -2), (key2982, 1), (key2973, 1), (key2982, 1), (key2937, 1), (key2973, 1), (key2937, 1), (key2746, 2), (key2736, 2), (key2736, 2), (key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2723, -1), (key2703, -1), (key2723, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1)]

def rawRow3512 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key1013, -2), (key994, 6), (key1191, 2), (key1191, 2), (key1197, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1210, -6), (key1069, 2), (key1148, 2), (key1148, 2)]

def rawRow3513 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key999, -2), (key994, 6), (key1191, 2), (key1197, 2), (key1191, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1210, -6), (key1148, 2), (key1069, 2), (key1148, 2)]

def rawRow3514 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key999, -2), (key994, 6), (key1197, 2), (key1191, 2), (key1191, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1210, -6), (key1148, 2), (key1148, 2), (key1069, 2)]

def rawRow3515 : Integer.Sparse Key := [(key1034, -2), (key1034, -2), (key1069, -2), (key1029, 6), (key1191, 2), (key1191, 2), (key1210, 2), (key994, -2), (key1107, -2), (key1107, -2), (key1197, -6), (key1013, 2), (key1121, 2), (key1121, 2)]

def rawRow3516 : Integer.Sparse Key := [(key1034, -2), (key1069, -2), (key1034, -2), (key1029, 6), (key1191, 2), (key1210, 2), (key1191, 2), (key1107, -2), (key994, -2), (key1107, -2), (key1197, -6), (key1121, 2), (key1013, 2), (key1121, 2)]

def rawRow3517 : Integer.Sparse Key := [(key1069, -2), (key1034, -2), (key1034, -2), (key1029, 6), (key1210, 2), (key1191, 2), (key1191, 2), (key1107, -2), (key1107, -2), (key994, -2), (key1197, -6), (key1121, 2), (key1121, 2), (key1013, 2)]

def rawRow3518 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1197, -2), (key1210, 6), (key999, 2), (key999, 2), (key1013, 2), (key1069, -2), (key1148, -2), (key1148, -2), (key994, -6), (key1029, 2), (key1107, 2), (key1107, 2)]

def rawRow3519 : Integer.Sparse Key := [(key1191, -2), (key1197, -2), (key1191, -2), (key1210, 6), (key999, 2), (key1013, 2), (key999, 2), (key1148, -2), (key1069, -2), (key1148, -2), (key994, -6), (key1107, 2), (key1029, 2), (key1107, 2)]

def rawRow3520 : Integer.Sparse Key := [(key1197, -2), (key1191, -2), (key1191, -2), (key1210, 6), (key1013, 2), (key999, 2), (key999, 2), (key1148, -2), (key1148, -2), (key1069, -2), (key994, -6), (key1107, 2), (key1107, 2), (key1029, 2)]

def rawRow3521 : Integer.Sparse Key := [(key1191, -2), (key1191, -2), (key1210, -2), (key1197, 6), (key1034, 2), (key1034, 2), (key1069, 2), (key1013, -2), (key1121, -2), (key1121, -2), (key1029, -6), (key994, 2), (key1107, 2), (key1107, 2)]

def rawRow3522 : Integer.Sparse Key := [(key1191, -2), (key1210, -2), (key1191, -2), (key1197, 6), (key1034, 2), (key1069, 2), (key1034, 2), (key1121, -2), (key1013, -2), (key1121, -2), (key1029, -6), (key1107, 2), (key994, 2), (key1107, 2)]

def rawRow3523 : Integer.Sparse Key := [(key1210, -2), (key1191, -2), (key1191, -2), (key1197, 6), (key1069, 2), (key1034, 2), (key1034, 2), (key1121, -2), (key1121, -2), (key1013, -2), (key1029, -6), (key1107, 2), (key1107, 2), (key994, 2)]

def rawRow3524 : Integer.Sparse Key := [(key2634, -6), (key2607, 2), (key2623, 2), (key2623, 2), (key2720, 6), (key2662, -2), (key2697, -2), (key2697, -2), (key2823, -2), (key2864, -2), (key2864, -2), (key2788, 2), (key2854, 2), (key2854, 2)]

def rawRow3525 : Integer.Sparse Key := [(key2634, -6), (key2623, 2), (key2607, 2), (key2623, 2), (key2720, 6), (key2697, -2), (key2662, -2), (key2697, -2), (key2864, -2), (key2823, -2), (key2864, -2), (key2854, 2), (key2788, 2), (key2854, 2)]

def rawRow3526 : Integer.Sparse Key := [(key2634, -6), (key2623, 2), (key2623, 2), (key2607, 2), (key2720, 6), (key2697, -2), (key2697, -2), (key2662, -2), (key2864, -2), (key2864, -2), (key2823, -2), (key2854, 2), (key2854, 2), (key2788, 2)]

def rawRow3527 : Integer.Sparse Key := [(key2788, -6), (key2662, 2), (key2777, 2), (key2777, 2), (key2823, 6), (key2607, -2), (key2800, -2), (key2800, -2), (key2720, -2), (key2864, -2), (key2864, -2), (key2634, 2), (key2854, 2), (key2854, 2)]

def rawRow3528 : Integer.Sparse Key := [(key2788, -6), (key2777, 2), (key2662, 2), (key2777, 2), (key2823, 6), (key2800, -2), (key2607, -2), (key2800, -2), (key2864, -2), (key2720, -2), (key2864, -2), (key2854, 2), (key2634, 2), (key2854, 2)]

def rawRow3529 : Integer.Sparse Key := [(key2788, -6), (key2777, 2), (key2777, 2), (key2662, 2), (key2823, 6), (key2800, -2), (key2800, -2), (key2607, -2), (key2864, -2), (key2864, -2), (key2720, -2), (key2854, 2), (key2854, 2), (key2634, 2)]

def rawRow3530 : Integer.Sparse Key := [(key2720, -6), (key2823, 2), (key2864, 2), (key2864, 2), (key2634, 6), (key2788, -2), (key2854, -2), (key2854, -2), (key2607, -2), (key2623, -2), (key2623, -2), (key2662, 2), (key2697, 2), (key2697, 2)]

def rawRow3531 : Integer.Sparse Key := [(key2720, -6), (key2864, 2), (key2823, 2), (key2864, 2), (key2634, 6), (key2854, -2), (key2788, -2), (key2854, -2), (key2623, -2), (key2607, -2), (key2623, -2), (key2697, 2), (key2662, 2), (key2697, 2)]

def rawRow3532 : Integer.Sparse Key := [(key2720, -6), (key2864, 2), (key2864, 2), (key2823, 2), (key2634, 6), (key2854, -2), (key2854, -2), (key2788, -2), (key2623, -2), (key2623, -2), (key2607, -2), (key2697, 2), (key2697, 2), (key2662, 2)]

def rawRow3533 : Integer.Sparse Key := [(key2823, -6), (key2720, 2), (key2864, 2), (key2864, 2), (key2788, 6), (key2634, -2), (key2854, -2), (key2854, -2), (key2662, -2), (key2777, -2), (key2777, -2), (key2607, 2), (key2800, 2), (key2800, 2)]

def rawRow3534 : Integer.Sparse Key := [(key2823, -6), (key2864, 2), (key2720, 2), (key2864, 2), (key2788, 6), (key2854, -2), (key2634, -2), (key2854, -2), (key2777, -2), (key2662, -2), (key2777, -2), (key2800, 2), (key2607, 2), (key2800, 2)]

def rawRow3535 : Integer.Sparse Key := [(key2823, -6), (key2864, 2), (key2864, 2), (key2720, 2), (key2788, 6), (key2854, -2), (key2854, -2), (key2634, -2), (key2777, -2), (key2777, -2), (key2662, -2), (key2800, 2), (key2800, 2), (key2607, 2)]

def rawRow3536 : Integer.Sparse Key := [(key1392, -1), (key1392, -1), (key1547, -1), (key1547, -1), (key1555, -1), (key1555, -1), (key1387, 2), (key1542, 2), (key1542, 2), (key1456, 1), (key1456, 1), (key1656, 1), (key1656, 1), (key1658, 1), (key1658, 1), (key1420, -1), (key1420, -1), (key1569, -1), (key1569, -1), (key1618, -1), (key1618, -1), (key1465, -2), (key1666, -2), (key1666, -2), (key1443, 1), (key1443, 1), (key1592, 1), (key1592, 1), (key1632, 1), (key1632, 1)]

def rawRow3537 : Integer.Sparse Key := [(key1547, -1), (key1555, -1), (key1392, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1542, 2), (key1387, 2), (key1542, 2), (key1656, 1), (key1658, 1), (key1456, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1569, -1), (key1618, -1), (key1420, -1), (key1618, -1), (key1420, -1), (key1569, -1), (key1666, -2), (key1465, -2), (key1666, -2), (key1592, 1), (key1632, 1), (key1443, 1), (key1632, 1), (key1443, 1), (key1592, 1)]

def rawRow3538 : Integer.Sparse Key := [(key1555, -1), (key1547, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1392, -1), (key1542, 2), (key1542, 2), (key1387, 2), (key1658, 1), (key1656, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1456, 1), (key1618, -1), (key1569, -1), (key1618, -1), (key1420, -1), (key1569, -1), (key1420, -1), (key1666, -2), (key1666, -2), (key1465, -2), (key1632, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1592, 1), (key1443, 1)]

def rawRow3539 : Integer.Sparse Key := [(key1297, -1), (key1297, -1), (key1574, -1), (key1574, -1), (key1592, -1), (key1592, -1), (key1292, 2), (key1569, 2), (key1569, 2), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1), (key1312, -1), (key1312, -1), (key1542, -1), (key1542, -1), (key1618, -1), (key1618, -1), (key1344, -2), (key1658, -2), (key1658, -2), (key1325, 1), (key1325, 1), (key1555, 1), (key1555, 1), (key1623, 1), (key1623, 1)]

def rawRow3540 : Integer.Sparse Key := [(key1574, -1), (key1592, -1), (key1297, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1569, 2), (key1292, 2), (key1569, 2), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1542, -1), (key1618, -1), (key1312, -1), (key1618, -1), (key1312, -1), (key1542, -1), (key1658, -2), (key1344, -2), (key1658, -2), (key1555, 1), (key1623, 1), (key1325, 1), (key1623, 1), (key1325, 1), (key1555, 1)]

def rawRow3541 : Integer.Sparse Key := [(key1592, -1), (key1574, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1297, -1), (key1569, 2), (key1569, 2), (key1292, 2), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1), (key1618, -1), (key1542, -1), (key1618, -1), (key1312, -1), (key1542, -1), (key1312, -1), (key1658, -2), (key1658, -2), (key1344, -2), (key1623, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1555, 1), (key1325, 1)]

def rawRow3542 : Integer.Sparse Key := [(key1456, -1), (key1456, -1), (key1656, -1), (key1656, -1), (key1658, -1), (key1658, -1), (key1465, 2), (key1666, 2), (key1666, 2), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1), (key1443, -1), (key1443, -1), (key1592, -1), (key1592, -1), (key1632, -1), (key1632, -1), (key1387, -2), (key1542, -2), (key1542, -2), (key1420, 1), (key1420, 1), (key1569, 1), (key1569, 1), (key1618, 1), (key1618, 1)]

def rawRow3543 : Integer.Sparse Key := [(key1656, -1), (key1658, -1), (key1456, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1666, 2), (key1465, 2), (key1666, 2), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1592, -1), (key1632, -1), (key1443, -1), (key1632, -1), (key1443, -1), (key1592, -1), (key1542, -2), (key1387, -2), (key1542, -2), (key1569, 1), (key1618, 1), (key1420, 1), (key1618, 1), (key1420, 1), (key1569, 1)]

def rawRow3544 : Integer.Sparse Key := [(key1658, -1), (key1656, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1456, -1), (key1666, 2), (key1666, 2), (key1465, 2), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1), (key1632, -1), (key1592, -1), (key1632, -1), (key1443, -1), (key1592, -1), (key1443, -1), (key1542, -2), (key1542, -2), (key1387, -2), (key1618, 1), (key1569, 1), (key1618, 1), (key1420, 1), (key1569, 1), (key1420, 1)]

def rawRow3545 : Integer.Sparse Key := [(key1338, -1), (key1338, -1), (key1656, -1), (key1656, -1), (key1666, -1), (key1666, -1), (key1344, 2), (key1658, 2), (key1658, 2), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1), (key1325, -1), (key1325, -1), (key1555, -1), (key1555, -1), (key1623, -1), (key1623, -1), (key1292, -2), (key1569, -2), (key1569, -2), (key1312, 1), (key1312, 1), (key1542, 1), (key1542, 1), (key1618, 1), (key1618, 1)]

def rawRow3546 : Integer.Sparse Key := [(key1656, -1), (key1666, -1), (key1338, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1658, 2), (key1344, 2), (key1658, 2), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1555, -1), (key1623, -1), (key1325, -1), (key1623, -1), (key1325, -1), (key1555, -1), (key1569, -2), (key1292, -2), (key1569, -2), (key1542, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1542, 1)]

def rawRow3547 : Integer.Sparse Key := [(key1666, -1), (key1656, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1338, -1), (key1658, 2), (key1658, 2), (key1344, 2), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1), (key1623, -1), (key1555, -1), (key1623, -1), (key1325, -1), (key1555, -1), (key1325, -1), (key1569, -2), (key1569, -2), (key1292, -2), (key1618, 1), (key1542, 1), (key1618, 1), (key1312, 1), (key1542, 1), (key1312, 1)]

def rawRow3548 : Integer.Sparse Key := [(key3052, -2), (key3052, -2), (key3067, -2), (key3048, 2), (key3048, 2), (key3062, 2), (key3108, 2), (key3108, 2), (key3135, 2), (key3097, -6), (key3111, -2), (key3111, -2), (key3137, -2), (key3104, 6)]

def rawRow3549 : Integer.Sparse Key := [(key3052, -2), (key3067, -2), (key3052, -2), (key3048, 2), (key3062, 2), (key3048, 2), (key3108, 2), (key3135, 2), (key3108, 2), (key3097, -6), (key3111, -2), (key3137, -2), (key3111, -2), (key3104, 6)]

def rawRow3550 : Integer.Sparse Key := [(key3067, -2), (key3052, -2), (key3052, -2), (key3062, 2), (key3048, 2), (key3048, 2), (key3135, 2), (key3108, 2), (key3108, 2), (key3097, -6), (key3137, -2), (key3111, -2), (key3111, -2), (key3104, 6)]

def rawRow3551 : Integer.Sparse Key := [(key3052, -2), (key3052, -2), (key3104, -2), (key3048, 2), (key3048, 2), (key3097, 2), (key3071, 2), (key3071, 2), (key3137, 2), (key3062, -6), (key3073, -2), (key3073, -2), (key3135, -2), (key3067, 6)]

def rawRow3552 : Integer.Sparse Key := [(key3052, -2), (key3104, -2), (key3052, -2), (key3048, 2), (key3097, 2), (key3048, 2), (key3071, 2), (key3137, 2), (key3071, 2), (key3062, -6), (key3073, -2), (key3135, -2), (key3073, -2), (key3067, 6)]

def rawRow3553 : Integer.Sparse Key := [(key3104, -2), (key3052, -2), (key3052, -2), (key3097, 2), (key3048, 2), (key3048, 2), (key3137, 2), (key3071, 2), (key3071, 2), (key3062, -6), (key3135, -2), (key3073, -2), (key3073, -2), (key3067, 6)]

def rawRow3554 : Integer.Sparse Key := [(key3108, -2), (key3108, -2), (key3135, -2), (key3111, 2), (key3111, 2), (key3137, 2), (key3052, 2), (key3052, 2), (key3067, 2), (key3104, -6), (key3048, -2), (key3048, -2), (key3062, -2), (key3097, 6)]

def rawRow3555 : Integer.Sparse Key := [(key3108, -2), (key3135, -2), (key3108, -2), (key3111, 2), (key3137, 2), (key3111, 2), (key3052, 2), (key3067, 2), (key3052, 2), (key3104, -6), (key3048, -2), (key3062, -2), (key3048, -2), (key3097, 6)]

def rawRow3556 : Integer.Sparse Key := [(key3135, -2), (key3108, -2), (key3108, -2), (key3137, 2), (key3111, 2), (key3111, 2), (key3067, 2), (key3052, 2), (key3052, 2), (key3104, -6), (key3062, -2), (key3048, -2), (key3048, -2), (key3097, 6)]

def rawRow3557 : Integer.Sparse Key := [(key3071, -2), (key3071, -2), (key3137, -2), (key3073, 2), (key3073, 2), (key3135, 2), (key3052, 2), (key3052, 2), (key3104, 2), (key3067, -6), (key3048, -2), (key3048, -2), (key3097, -2), (key3062, 6)]

def rawRow3558 : Integer.Sparse Key := [(key3071, -2), (key3137, -2), (key3071, -2), (key3073, 2), (key3135, 2), (key3073, 2), (key3052, 2), (key3104, 2), (key3052, 2), (key3067, -6), (key3048, -2), (key3097, -2), (key3048, -2), (key3062, 6)]

def rawRow3559 : Integer.Sparse Key := [(key3137, -2), (key3071, -2), (key3071, -2), (key3135, 2), (key3073, 2), (key3073, 2), (key3104, 2), (key3052, 2), (key3052, 2), (key3067, -6), (key3097, -2), (key3048, -2), (key3048, -2), (key3062, 6)]

def rawRow3560 : Integer.Sparse Key := [(key1338, -2), (key1338, -2), (key1344, -2), (key1297, 1), (key1297, 1), (key1317, 1), (key1317, 1), (key1325, 1), (key1325, 1), (key1773, 2), (key1773, 2), (key1779, 2), (key1392, -1), (key1392, -1), (key1547, -1), (key1547, -1), (key1555, -1), (key1555, -1), (key1789, -1), (key1789, -1), (key1814, -1), (key1814, -1), (key1816, -1), (key1816, -1), (key1456, 1), (key1456, 1), (key1656, 1), (key1656, 1), (key1658, 1), (key1658, 1)]

def rawRow3561 : Integer.Sparse Key := [(key1338, -2), (key1344, -2), (key1338, -2), (key1317, 1), (key1325, 1), (key1297, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1773, 2), (key1779, 2), (key1773, 2), (key1547, -1), (key1555, -1), (key1392, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1814, -1), (key1816, -1), (key1789, -1), (key1816, -1), (key1789, -1), (key1814, -1), (key1656, 1), (key1658, 1), (key1456, 1), (key1658, 1), (key1456, 1), (key1656, 1)]

def rawRow3562 : Integer.Sparse Key := [(key1344, -2), (key1338, -2), (key1338, -2), (key1325, 1), (key1317, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1297, 1), (key1779, 2), (key1773, 2), (key1773, 2), (key1555, -1), (key1547, -1), (key1555, -1), (key1392, -1), (key1547, -1), (key1392, -1), (key1816, -1), (key1814, -1), (key1816, -1), (key1789, -1), (key1814, -1), (key1789, -1), (key1658, 1), (key1656, 1), (key1658, 1), (key1456, 1), (key1656, 1), (key1456, 1)]

def rawRow3563 : Integer.Sparse Key := [(key1456, -2), (key1456, -2), (key1465, -2), (key1392, 1), (key1392, 1), (key1425, 1), (key1425, 1), (key1443, 1), (key1443, 1), (key1789, 2), (key1789, 2), (key1797, 2), (key1297, -1), (key1297, -1), (key1574, -1), (key1574, -1), (key1592, -1), (key1592, -1), (key1773, -1), (key1773, -1), (key1814, -1), (key1814, -1), (key1824, -1), (key1824, -1), (key1338, 1), (key1338, 1), (key1656, 1), (key1656, 1), (key1666, 1), (key1666, 1)]

def rawRow3564 : Integer.Sparse Key := [(key1456, -2), (key1465, -2), (key1456, -2), (key1425, 1), (key1443, 1), (key1392, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1789, 2), (key1797, 2), (key1789, 2), (key1574, -1), (key1592, -1), (key1297, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1814, -1), (key1824, -1), (key1773, -1), (key1824, -1), (key1773, -1), (key1814, -1), (key1656, 1), (key1666, 1), (key1338, 1), (key1666, 1), (key1338, 1), (key1656, 1)]

def rawRow3565 : Integer.Sparse Key := [(key1465, -2), (key1456, -2), (key1456, -2), (key1443, 1), (key1425, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1392, 1), (key1797, 2), (key1789, 2), (key1789, 2), (key1592, -1), (key1574, -1), (key1592, -1), (key1297, -1), (key1574, -1), (key1297, -1), (key1824, -1), (key1814, -1), (key1824, -1), (key1773, -1), (key1814, -1), (key1773, -1), (key1666, 1), (key1656, 1), (key1666, 1), (key1338, 1), (key1656, 1), (key1338, 1)]

def rawRow3566 : Integer.Sparse Key := [(key1773, -2), (key1773, -2), (key1779, -2), (key1789, 1), (key1789, 1), (key1814, 1), (key1814, 1), (key1816, 1), (key1816, 1), (key1338, 2), (key1338, 2), (key1344, 2), (key1456, -1), (key1456, -1), (key1656, -1), (key1656, -1), (key1658, -1), (key1658, -1), (key1297, -1), (key1297, -1), (key1317, -1), (key1317, -1), (key1325, -1), (key1325, -1), (key1392, 1), (key1392, 1), (key1547, 1), (key1547, 1), (key1555, 1), (key1555, 1)]

def rawRow3567 : Integer.Sparse Key := [(key1773, -2), (key1779, -2), (key1773, -2), (key1814, 1), (key1816, 1), (key1789, 1), (key1816, 1), (key1789, 1), (key1814, 1), (key1338, 2), (key1344, 2), (key1338, 2), (key1656, -1), (key1658, -1), (key1456, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1317, -1), (key1325, -1), (key1297, -1), (key1325, -1), (key1297, -1), (key1317, -1), (key1547, 1), (key1555, 1), (key1392, 1), (key1555, 1), (key1392, 1), (key1547, 1)]

def rawRow3568 : Integer.Sparse Key := [(key1779, -2), (key1773, -2), (key1773, -2), (key1816, 1), (key1814, 1), (key1816, 1), (key1789, 1), (key1814, 1), (key1789, 1), (key1344, 2), (key1338, 2), (key1338, 2), (key1658, -1), (key1656, -1), (key1658, -1), (key1456, -1), (key1656, -1), (key1456, -1), (key1325, -1), (key1317, -1), (key1325, -1), (key1297, -1), (key1317, -1), (key1297, -1), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1)]

def rawRow3569 : Integer.Sparse Key := [(key1789, -2), (key1789, -2), (key1797, -2), (key1773, 1), (key1773, 1), (key1814, 1), (key1814, 1), (key1824, 1), (key1824, 1), (key1456, 2), (key1456, 2), (key1465, 2), (key1338, -1), (key1338, -1), (key1656, -1), (key1656, -1), (key1666, -1), (key1666, -1), (key1392, -1), (key1392, -1), (key1425, -1), (key1425, -1), (key1443, -1), (key1443, -1), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1)]

def rawRow3570 : Integer.Sparse Key := [(key1789, -2), (key1797, -2), (key1789, -2), (key1814, 1), (key1824, 1), (key1773, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1456, 2), (key1465, 2), (key1456, 2), (key1656, -1), (key1666, -1), (key1338, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1425, -1), (key1443, -1), (key1392, -1), (key1443, -1), (key1392, -1), (key1425, -1), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1)]

def rawRow3571 : Integer.Sparse Key := [(key1797, -2), (key1789, -2), (key1789, -2), (key1824, 1), (key1814, 1), (key1824, 1), (key1773, 1), (key1814, 1), (key1773, 1), (key1465, 2), (key1456, 2), (key1456, 2), (key1666, -1), (key1656, -1), (key1666, -1), (key1338, -1), (key1656, -1), (key1338, -1), (key1443, -1), (key1425, -1), (key1443, -1), (key1392, -1), (key1425, -1), (key1392, -1), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1)]

def rawRow3572 : Integer.Sparse Key := [(key997, -2), (key997, -2), (key1012, -2), (key993, 6), (key1189, 2), (key1189, 2), (key1196, 2), (key1028, -2), (key1106, -2), (key1106, -2), (key1209, -6), (key1068, 2), (key1147, 2), (key1147, 2)]

def rawRow3573 : Integer.Sparse Key := [(key997, -2), (key1012, -2), (key997, -2), (key993, 6), (key1189, 2), (key1196, 2), (key1189, 2), (key1106, -2), (key1028, -2), (key1106, -2), (key1209, -6), (key1147, 2), (key1068, 2), (key1147, 2)]

def rawRow3574 : Integer.Sparse Key := [(key1012, -2), (key997, -2), (key997, -2), (key993, 6), (key1196, 2), (key1189, 2), (key1189, 2), (key1106, -2), (key1106, -2), (key1028, -2), (key1209, -6), (key1147, 2), (key1147, 2), (key1068, 2)]

def rawRow3575 : Integer.Sparse Key := [(key1032, -2), (key1032, -2), (key1068, -2), (key1028, 6), (key1189, 2), (key1189, 2), (key1209, 2), (key993, -2), (key1106, -2), (key1106, -2), (key1196, -6), (key1012, 2), (key1120, 2), (key1120, 2)]

def rawRow3576 : Integer.Sparse Key := [(key1032, -2), (key1068, -2), (key1032, -2), (key1028, 6), (key1189, 2), (key1209, 2), (key1189, 2), (key1106, -2), (key993, -2), (key1106, -2), (key1196, -6), (key1120, 2), (key1012, 2), (key1120, 2)]

def rawRow3577 : Integer.Sparse Key := [(key1068, -2), (key1032, -2), (key1032, -2), (key1028, 6), (key1209, 2), (key1189, 2), (key1189, 2), (key1106, -2), (key1106, -2), (key993, -2), (key1196, -6), (key1120, 2), (key1120, 2), (key1012, 2)]

def rawRow3578 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1196, -2), (key1209, 6), (key997, 2), (key997, 2), (key1012, 2), (key1068, -2), (key1147, -2), (key1147, -2), (key993, -6), (key1028, 2), (key1106, 2), (key1106, 2)]

def rawRow3579 : Integer.Sparse Key := [(key1189, -2), (key1196, -2), (key1189, -2), (key1209, 6), (key997, 2), (key1012, 2), (key997, 2), (key1147, -2), (key1068, -2), (key1147, -2), (key993, -6), (key1106, 2), (key1028, 2), (key1106, 2)]

def rawRow3580 : Integer.Sparse Key := [(key1196, -2), (key1189, -2), (key1189, -2), (key1209, 6), (key1012, 2), (key997, 2), (key997, 2), (key1147, -2), (key1147, -2), (key1068, -2), (key993, -6), (key1106, 2), (key1106, 2), (key1028, 2)]

def rawRow3581 : Integer.Sparse Key := [(key1189, -2), (key1189, -2), (key1209, -2), (key1196, 6), (key1032, 2), (key1032, 2), (key1068, 2), (key1012, -2), (key1120, -2), (key1120, -2), (key1028, -6), (key993, 2), (key1106, 2), (key1106, 2)]

def rawRow3582 : Integer.Sparse Key := [(key1189, -2), (key1209, -2), (key1189, -2), (key1196, 6), (key1032, 2), (key1068, 2), (key1032, 2), (key1120, -2), (key1012, -2), (key1120, -2), (key1028, -6), (key1106, 2), (key993, 2), (key1106, 2)]

def rawRow3583 : Integer.Sparse Key := [(key1209, -2), (key1189, -2), (key1189, -2), (key1196, 6), (key1068, 2), (key1032, 2), (key1032, 2), (key1120, -2), (key1120, -2), (key1012, -2), (key1028, -6), (key1106, 2), (key1106, 2), (key993, 2)]

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

def rawRow3584 : Integer.Sparse Key := [(key2619, -2), (key2642, -2), (key2642, -2), (key2616, 1), (key2616, 1), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2951, 2), (key2977, 2), (key2977, 2), (key2706, -1), (key2706, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2961, -1), (key2961, -1), (key2984, -1), (key2984, -1), (key2992, -1), (key2992, -1), (key2729, 1), (key2729, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

def rawRow3585 : Integer.Sparse Key := [(key2642, -2), (key2619, -2), (key2642, -2), (key2632, 1), (key2640, 1), (key2616, 1), (key2640, 1), (key2616, 1), (key2632, 1), (key2977, 2), (key2951, 2), (key2977, 2), (key2809, -1), (key2860, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2984, -1), (key2992, -1), (key2961, -1), (key2992, -1), (key2961, -1), (key2984, -1), (key2832, 1), (key2883, 1), (key2729, 1), (key2883, 1), (key2729, 1), (key2832, 1)]

def rawRow3586 : Integer.Sparse Key := [(key2642, -2), (key2642, -2), (key2619, -2), (key2640, 1), (key2632, 1), (key2640, 1), (key2616, 1), (key2632, 1), (key2616, 1), (key2977, 2), (key2977, 2), (key2951, 2), (key2860, -1), (key2809, -1), (key2860, -1), (key2706, -1), (key2809, -1), (key2706, -1), (key2992, -1), (key2984, -1), (key2992, -1), (key2961, -1), (key2984, -1), (key2961, -1), (key2883, 1), (key2832, 1), (key2883, 1), (key2729, 1), (key2832, 1), (key2729, 1)]

def rawRow3587 : Integer.Sparse Key := [(key2674, -2), (key2729, -2), (key2729, -2), (key2671, 1), (key2671, 1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2939, 2), (key2984, 2), (key2984, 2), (key2632, -1), (key2632, -1), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2944, -1), (key2944, -1), (key2977, -1), (key2977, -1), (key2992, -1), (key2992, -1), (key2642, 1), (key2642, 1), (key2796, 1), (key2796, 1), (key2883, 1), (key2883, 1)]

def rawRow3588 : Integer.Sparse Key := [(key2729, -2), (key2674, -2), (key2729, -2), (key2706, 1), (key2726, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2984, 2), (key2939, 2), (key2984, 2), (key2786, -1), (key2870, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2977, -1), (key2992, -1), (key2944, -1), (key2992, -1), (key2944, -1), (key2977, -1), (key2796, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2796, 1)]

def rawRow3589 : Integer.Sparse Key := [(key2729, -2), (key2729, -2), (key2674, -2), (key2726, 1), (key2706, 1), (key2726, 1), (key2671, 1), (key2706, 1), (key2671, 1), (key2984, 2), (key2984, 2), (key2939, 2), (key2870, -1), (key2786, -1), (key2870, -1), (key2632, -1), (key2786, -1), (key2632, -1), (key2992, -1), (key2977, -1), (key2992, -1), (key2944, -1), (key2977, -1), (key2944, -1), (key2883, 1), (key2796, 1), (key2883, 1), (key2642, 1), (key2796, 1), (key2642, 1)]

def rawRow3590 : Integer.Sparse Key := [(key2951, -2), (key2977, -2), (key2977, -2), (key2961, 1), (key2961, 1), (key2984, 1), (key2984, 1), (key2992, 1), (key2992, 1), (key2619, 2), (key2642, 2), (key2642, 2), (key2729, -1), (key2729, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2616, -1), (key2616, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2706, 1), (key2706, 1), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1)]

def rawRow3591 : Integer.Sparse Key := [(key2977, -2), (key2951, -2), (key2977, -2), (key2984, 1), (key2992, 1), (key2961, 1), (key2992, 1), (key2961, 1), (key2984, 1), (key2642, 2), (key2619, 2), (key2642, 2), (key2832, -1), (key2883, -1), (key2729, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2632, -1), (key2640, -1), (key2616, -1), (key2640, -1), (key2616, -1), (key2632, -1), (key2809, 1), (key2860, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2809, 1)]

def rawRow3592 : Integer.Sparse Key := [(key2977, -2), (key2977, -2), (key2951, -2), (key2992, 1), (key2984, 1), (key2992, 1), (key2961, 1), (key2984, 1), (key2961, 1), (key2642, 2), (key2642, 2), (key2619, 2), (key2883, -1), (key2832, -1), (key2883, -1), (key2729, -1), (key2832, -1), (key2729, -1), (key2640, -1), (key2632, -1), (key2640, -1), (key2616, -1), (key2632, -1), (key2616, -1), (key2860, 1), (key2809, 1), (key2860, 1), (key2706, 1), (key2809, 1), (key2706, 1)]

def rawRow3593 : Integer.Sparse Key := [(key2939, -2), (key2984, -2), (key2984, -2), (key2944, 1), (key2944, 1), (key2977, 1), (key2977, 1), (key2992, 1), (key2992, 1), (key2674, 2), (key2729, 2), (key2729, 2), (key2642, -1), (key2642, -1), (key2796, -1), (key2796, -1), (key2883, -1), (key2883, -1), (key2671, -1), (key2671, -1), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2632, 1), (key2632, 1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1)]

def rawRow3594 : Integer.Sparse Key := [(key2984, -2), (key2939, -2), (key2984, -2), (key2977, 1), (key2992, 1), (key2944, 1), (key2992, 1), (key2944, 1), (key2977, 1), (key2729, 2), (key2674, 2), (key2729, 2), (key2796, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2786, 1), (key2870, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2786, 1)]

def rawRow3595 : Integer.Sparse Key := [(key2984, -2), (key2984, -2), (key2939, -2), (key2992, 1), (key2977, 1), (key2992, 1), (key2944, 1), (key2977, 1), (key2944, 1), (key2729, 2), (key2729, 2), (key2674, 2), (key2883, -1), (key2796, -1), (key2883, -1), (key2642, -1), (key2796, -1), (key2642, -1), (key2726, -1), (key2706, -1), (key2726, -1), (key2671, -1), (key2706, -1), (key2671, -1), (key2870, 1), (key2786, 1), (key2870, 1), (key2632, 1), (key2786, 1), (key2632, 1)]

def rawRow3596 : Integer.Sparse Key := [(key2375, -2), (key2375, -2), (key2387, -2), (key2371, 6), (key2536, 2), (key2536, 2), (key2541, 2), (key2399, -2), (key2465, -2), (key2465, -2), (key2552, -6), (key2434, 2), (key2500, 2), (key2500, 2)]

def rawRow3597 : Integer.Sparse Key := [(key2375, -2), (key2387, -2), (key2375, -2), (key2371, 6), (key2536, 2), (key2541, 2), (key2536, 2), (key2465, -2), (key2399, -2), (key2465, -2), (key2552, -6), (key2500, 2), (key2434, 2), (key2500, 2)]

def rawRow3598 : Integer.Sparse Key := [(key2387, -2), (key2375, -2), (key2375, -2), (key2371, 6), (key2541, 2), (key2536, 2), (key2536, 2), (key2465, -2), (key2465, -2), (key2399, -2), (key2552, -6), (key2500, 2), (key2500, 2), (key2434, 2)]

def rawRow3599 : Integer.Sparse Key := [(key2403, -2), (key2403, -2), (key2434, -2), (key2399, 6), (key2536, 2), (key2536, 2), (key2552, 2), (key2371, -2), (key2465, -2), (key2465, -2), (key2541, -6), (key2387, 2), (key2477, 2), (key2477, 2)]

def rawRow3600 : Integer.Sparse Key := [(key2403, -2), (key2434, -2), (key2403, -2), (key2399, 6), (key2536, 2), (key2552, 2), (key2536, 2), (key2465, -2), (key2371, -2), (key2465, -2), (key2541, -6), (key2477, 2), (key2387, 2), (key2477, 2)]

def rawRow3601 : Integer.Sparse Key := [(key2434, -2), (key2403, -2), (key2403, -2), (key2399, 6), (key2552, 2), (key2536, 2), (key2536, 2), (key2465, -2), (key2465, -2), (key2371, -2), (key2541, -6), (key2477, 2), (key2477, 2), (key2387, 2)]

def rawRow3602 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2541, -2), (key2552, 6), (key2375, 2), (key2375, 2), (key2387, 2), (key2434, -2), (key2500, -2), (key2500, -2), (key2371, -6), (key2399, 2), (key2465, 2), (key2465, 2)]

def rawRow3603 : Integer.Sparse Key := [(key2536, -2), (key2541, -2), (key2536, -2), (key2552, 6), (key2375, 2), (key2387, 2), (key2375, 2), (key2500, -2), (key2434, -2), (key2500, -2), (key2371, -6), (key2465, 2), (key2399, 2), (key2465, 2)]

def rawRow3604 : Integer.Sparse Key := [(key2541, -2), (key2536, -2), (key2536, -2), (key2552, 6), (key2387, 2), (key2375, 2), (key2375, 2), (key2500, -2), (key2500, -2), (key2434, -2), (key2371, -6), (key2465, 2), (key2465, 2), (key2399, 2)]

def rawRow3605 : Integer.Sparse Key := [(key2536, -2), (key2536, -2), (key2552, -2), (key2541, 6), (key2403, 2), (key2403, 2), (key2434, 2), (key2387, -2), (key2477, -2), (key2477, -2), (key2399, -6), (key2371, 2), (key2465, 2), (key2465, 2)]

def rawRow3606 : Integer.Sparse Key := [(key2536, -2), (key2552, -2), (key2536, -2), (key2541, 6), (key2403, 2), (key2434, 2), (key2403, 2), (key2477, -2), (key2387, -2), (key2477, -2), (key2399, -6), (key2465, 2), (key2371, 2), (key2465, 2)]

def rawRow3607 : Integer.Sparse Key := [(key2552, -2), (key2536, -2), (key2536, -2), (key2541, 6), (key2434, 2), (key2403, 2), (key2403, 2), (key2477, -2), (key2477, -2), (key2387, -2), (key2399, -6), (key2465, 2), (key2465, 2), (key2371, 2)]

def rawRow3608 : Integer.Sparse Key := [(key2373, -2), (key2373, -2), (key2386, -2), (key2370, 6), (key2874, 2), (key2874, 2), (key2908, 2), (key2762, -2), (key2839, -2), (key2839, -2), (key2987, -6), (key2928, 2), (key2965, 2), (key2965, 2)]

def rawRow3609 : Integer.Sparse Key := [(key2373, -2), (key2386, -2), (key2373, -2), (key2370, 6), (key2874, 2), (key2908, 2), (key2874, 2), (key2839, -2), (key2762, -2), (key2839, -2), (key2987, -6), (key2965, 2), (key2928, 2), (key2965, 2)]

def rawRow3610 : Integer.Sparse Key := [(key2386, -2), (key2373, -2), (key2373, -2), (key2370, 6), (key2908, 2), (key2874, 2), (key2874, 2), (key2839, -2), (key2839, -2), (key2762, -2), (key2987, -6), (key2965, 2), (key2965, 2), (key2928, 2)]

def rawRow3611 : Integer.Sparse Key := [(key2401, -2), (key2401, -2), (key2433, -2), (key2398, 6), (key2874, 2), (key2874, 2), (key2987, 2), (key2583, -2), (key2839, -2), (key2839, -2), (key2908, -6), (key2597, 2), (key2886, 2), (key2886, 2)]

def rawRow3612 : Integer.Sparse Key := [(key2401, -2), (key2433, -2), (key2401, -2), (key2398, 6), (key2874, 2), (key2987, 2), (key2874, 2), (key2839, -2), (key2583, -2), (key2839, -2), (key2908, -6), (key2886, 2), (key2597, 2), (key2886, 2)]

def rawRow3613 : Integer.Sparse Key := [(key2433, -2), (key2401, -2), (key2401, -2), (key2398, 6), (key2987, 2), (key2874, 2), (key2874, 2), (key2839, -2), (key2839, -2), (key2583, -2), (key2908, -6), (key2886, 2), (key2886, 2), (key2597, 2)]

def rawRow3614 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2540, -2), (key2551, 6), (key2373, 2), (key2373, 2), (key2386, 2), (key2433, -2), (key2499, -2), (key2499, -2), (key2370, -6), (key2762, 2), (key2839, 2), (key2839, 2)]

def rawRow3615 : Integer.Sparse Key := [(key2534, -2), (key2540, -2), (key2534, -2), (key2551, 6), (key2373, 2), (key2386, 2), (key2373, 2), (key2499, -2), (key2433, -2), (key2499, -2), (key2370, -6), (key2839, 2), (key2762, 2), (key2839, 2)]

def rawRow3616 : Integer.Sparse Key := [(key2540, -2), (key2534, -2), (key2534, -2), (key2551, 6), (key2386, 2), (key2373, 2), (key2373, 2), (key2499, -2), (key2499, -2), (key2433, -2), (key2370, -6), (key2839, 2), (key2839, 2), (key2762, 2)]

def rawRow3617 : Integer.Sparse Key := [(key2534, -2), (key2534, -2), (key2551, -2), (key2540, 6), (key2401, 2), (key2401, 2), (key2433, 2), (key2386, -2), (key2476, -2), (key2476, -2), (key2398, -6), (key2583, 2), (key2839, 2), (key2839, 2)]

def rawRow3618 : Integer.Sparse Key := [(key2534, -2), (key2551, -2), (key2534, -2), (key2540, 6), (key2401, 2), (key2433, 2), (key2401, 2), (key2476, -2), (key2386, -2), (key2476, -2), (key2398, -6), (key2839, 2), (key2583, 2), (key2839, 2)]

def rawRow3619 : Integer.Sparse Key := [(key2551, -2), (key2534, -2), (key2534, -2), (key2540, 6), (key2433, 2), (key2401, 2), (key2401, 2), (key2476, -2), (key2476, -2), (key2386, -2), (key2398, -6), (key2839, 2), (key2839, 2), (key2583, 2)]

def rawRow3620 : Integer.Sparse Key := [(key2645, -2), (key2645, -2), (key2651, -2), (key2611, 1), (key2611, 1), (key2627, 1), (key2627, 1), (key2636, 1), (key2636, 1), (key2722, 2), (key2722, 2), (key2745, 2), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2734, -1), (key2734, -1), (key2825, -1), (key2825, -1), (key2866, -1), (key2866, -1), (key2902, -1), (key2902, -1), (key2790, 1), (key2790, 1), (key2856, 1), (key2856, 1), (key2895, 1), (key2895, 1)]

def rawRow3621 : Integer.Sparse Key := [(key2645, -2), (key2651, -2), (key2645, -2), (key2627, 1), (key2636, 1), (key2611, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2722, 2), (key2745, 2), (key2722, 2), (key2701, -1), (key2734, -1), (key2666, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2856, 1), (key2895, 1), (key2790, 1), (key2895, 1), (key2790, 1), (key2856, 1)]

def rawRow3622 : Integer.Sparse Key := [(key2651, -2), (key2645, -2), (key2645, -2), (key2636, 1), (key2627, 1), (key2636, 1), (key2611, 1), (key2627, 1), (key2611, 1), (key2745, 2), (key2722, 2), (key2722, 2), (key2734, -1), (key2701, -1), (key2734, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2902, -1), (key2866, -1), (key2902, -1), (key2825, -1), (key2866, -1), (key2825, -1), (key2895, 1), (key2856, 1), (key2895, 1), (key2790, 1), (key2856, 1), (key2790, 1)]

def rawRow3623 : Integer.Sparse Key := [(key2734, -2), (key2734, -2), (key2745, -2), (key2666, 1), (key2666, 1), (key2701, 1), (key2701, 1), (key2722, 1), (key2722, 1), (key2947, 2), (key2947, 2), (key2958, 2), (key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2722, -1), (key2722, -1), (key2866, -1), (key2866, -1), (key2981, -1), (key2981, -1), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1)]

def rawRow3624 : Integer.Sparse Key := [(key2734, -2), (key2745, -2), (key2734, -2), (key2701, 1), (key2722, 1), (key2666, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2947, 2), (key2958, 2), (key2947, 2), (key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1)]

def rawRow3625 : Integer.Sparse Key := [(key2745, -2), (key2734, -2), (key2734, -2), (key2722, 1), (key2701, 1), (key2722, 1), (key2666, 1), (key2701, 1), (key2666, 1), (key2958, 2), (key2947, 2), (key2947, 2), (key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2981, -1), (key2866, -1), (key2981, -1), (key2722, -1), (key2866, -1), (key2722, -1), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1)]

def rawRow3626 : Integer.Sparse Key := [(key2935, -2), (key2935, -2), (key2941, -2), (key2947, 1), (key2947, 1), (key2971, 1), (key2971, 1), (key2974, 1), (key2974, 1), (key2645, 2), (key2645, 2), (key2651, 2), (key2734, -1), (key2734, -1), (key2892, -1), (key2892, -1), (key2895, -1), (key2895, -1), (key2611, -1), (key2611, -1), (key2627, -1), (key2627, -1), (key2636, -1), (key2636, -1), (key2666, 1), (key2666, 1), (key2781, 1), (key2781, 1), (key2790, 1), (key2790, 1)]

def rawRow3627 : Integer.Sparse Key := [(key2935, -2), (key2941, -2), (key2935, -2), (key2971, 1), (key2974, 1), (key2947, 1), (key2974, 1), (key2947, 1), (key2971, 1), (key2645, 2), (key2651, 2), (key2645, 2), (key2892, -1), (key2895, -1), (key2734, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2781, 1), (key2790, 1), (key2666, 1), (key2790, 1), (key2666, 1), (key2781, 1)]

def rawRow3628 : Integer.Sparse Key := [(key2941, -2), (key2935, -2), (key2935, -2), (key2974, 1), (key2971, 1), (key2974, 1), (key2947, 1), (key2971, 1), (key2947, 1), (key2651, 2), (key2645, 2), (key2645, 2), (key2895, -1), (key2892, -1), (key2895, -1), (key2734, -1), (key2892, -1), (key2734, -1), (key2636, -1), (key2627, -1), (key2636, -1), (key2611, -1), (key2627, -1), (key2611, -1), (key2790, 1), (key2781, 1), (key2790, 1), (key2666, 1), (key2781, 1), (key2666, 1)]

def rawRow3629 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2935, 1), (key2935, 1), (key2971, 1), (key2971, 1), (key2981, 1), (key2981, 1), (key2734, 2), (key2734, 2), (key2745, 2), (key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2666, -1), (key2666, -1), (key2701, -1), (key2701, -1), (key2722, -1), (key2722, -1), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1)]

def rawRow3630 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2971, 1), (key2981, 1), (key2935, 1), (key2981, 1), (key2935, 1), (key2971, 1), (key2734, 2), (key2745, 2), (key2734, 2), (key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1)]

def rawRow3631 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2981, 1), (key2971, 1), (key2981, 1), (key2935, 1), (key2971, 1), (key2935, 1), (key2745, 2), (key2734, 2), (key2734, 2), (key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2722, -1), (key2701, -1), (key2722, -1), (key2666, -1), (key2701, -1), (key2666, -1), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1)]

def rawRow3632 : Integer.Sparse Key := [(key2091, -2), (key2092, -2), (key2092, -2), (key2095, 6), (key2193, 2), (key2194, 2), (key2194, 2), (key2305, -2), (key2305, -2), (key2343, -2), (key2200, -6), (key2310, 2), (key2310, 2), (key2347, 2)]

def rawRow3633 : Integer.Sparse Key := [(key2092, -2), (key2091, -2), (key2092, -2), (key2095, 6), (key2194, 2), (key2193, 2), (key2194, 2), (key2305, -2), (key2343, -2), (key2305, -2), (key2200, -6), (key2310, 2), (key2347, 2), (key2310, 2)]

def rawRow3634 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2091, -2), (key2095, 6), (key2194, 2), (key2194, 2), (key2193, 2), (key2343, -2), (key2305, -2), (key2305, -2), (key2200, -6), (key2347, 2), (key2310, 2), (key2310, 2)]

def rawRow3635 : Integer.Sparse Key := [(key2092, -2), (key2092, -2), (key2095, -2), (key2091, 6), (key2341, 2), (key2341, 2), (key2343, 2), (key2193, -2), (key2302, -2), (key2302, -2), (key2347, -6), (key2200, 2), (key2310, 2), (key2310, 2)]

def rawRow3636 : Integer.Sparse Key := [(key2092, -2), (key2095, -2), (key2092, -2), (key2091, 6), (key2341, 2), (key2343, 2), (key2341, 2), (key2302, -2), (key2193, -2), (key2302, -2), (key2347, -6), (key2310, 2), (key2200, 2), (key2310, 2)]

def rawRow3637 : Integer.Sparse Key := [(key2095, -2), (key2092, -2), (key2092, -2), (key2091, 6), (key2343, 2), (key2341, 2), (key2341, 2), (key2302, -2), (key2302, -2), (key2193, -2), (key2347, -6), (key2310, 2), (key2310, 2), (key2200, 2)]

def rawRow3638 : Integer.Sparse Key := [(key2193, -2), (key2194, -2), (key2194, -2), (key2200, 6), (key2091, 2), (key2092, 2), (key2092, 2), (key2310, -2), (key2310, -2), (key2347, -2), (key2095, -6), (key2305, 2), (key2305, 2), (key2343, 2)]

def rawRow3639 : Integer.Sparse Key := [(key2194, -2), (key2193, -2), (key2194, -2), (key2200, 6), (key2092, 2), (key2091, 2), (key2092, 2), (key2310, -2), (key2347, -2), (key2310, -2), (key2095, -6), (key2305, 2), (key2343, 2), (key2305, 2)]

def rawRow3640 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2193, -2), (key2200, 6), (key2092, 2), (key2092, 2), (key2091, 2), (key2347, -2), (key2310, -2), (key2310, -2), (key2095, -6), (key2343, 2), (key2305, 2), (key2305, 2)]

def rawRow3641 : Integer.Sparse Key := [(key2194, -2), (key2194, -2), (key2200, -2), (key2193, 6), (key2341, 2), (key2341, 2), (key2347, 2), (key2091, -2), (key2302, -2), (key2302, -2), (key2343, -6), (key2095, 2), (key2305, 2), (key2305, 2)]

def rawRow3642 : Integer.Sparse Key := [(key2194, -2), (key2200, -2), (key2194, -2), (key2193, 6), (key2341, 2), (key2347, 2), (key2341, 2), (key2302, -2), (key2091, -2), (key2302, -2), (key2343, -6), (key2305, 2), (key2095, 2), (key2305, 2)]

def rawRow3643 : Integer.Sparse Key := [(key2200, -2), (key2194, -2), (key2194, -2), (key2193, 6), (key2347, 2), (key2341, 2), (key2341, 2), (key2302, -2), (key2302, -2), (key2091, -2), (key2343, -6), (key2305, 2), (key2305, 2), (key2095, 2)]

def rawRow3644 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2343, -2), (key2347, 6), (key2092, 2), (key2092, 2), (key2095, 2), (key2200, -2), (key2310, -2), (key2310, -2), (key2091, -6), (key2193, 2), (key2302, 2), (key2302, 2)]

def rawRow3645 : Integer.Sparse Key := [(key2341, -2), (key2343, -2), (key2341, -2), (key2347, 6), (key2092, 2), (key2095, 2), (key2092, 2), (key2310, -2), (key2200, -2), (key2310, -2), (key2091, -6), (key2302, 2), (key2193, 2), (key2302, 2)]

def rawRow3646 : Integer.Sparse Key := [(key2343, -2), (key2341, -2), (key2341, -2), (key2347, 6), (key2095, 2), (key2092, 2), (key2092, 2), (key2310, -2), (key2310, -2), (key2200, -2), (key2091, -6), (key2302, 2), (key2302, 2), (key2193, 2)]

def rawRow3647 : Integer.Sparse Key := [(key2341, -2), (key2341, -2), (key2347, -2), (key2343, 6), (key2194, 2), (key2194, 2), (key2200, 2), (key2095, -2), (key2305, -2), (key2305, -2), (key2193, -6), (key2091, 2), (key2302, 2), (key2302, 2)]

def rawRow3648 : Integer.Sparse Key := [(key2341, -2), (key2347, -2), (key2341, -2), (key2343, 6), (key2194, 2), (key2200, 2), (key2194, 2), (key2305, -2), (key2095, -2), (key2305, -2), (key2193, -6), (key2302, 2), (key2091, 2), (key2302, 2)]

def rawRow3649 : Integer.Sparse Key := [(key2347, -2), (key2341, -2), (key2341, -2), (key2343, 6), (key2200, 2), (key2194, 2), (key2194, 2), (key2305, -2), (key2305, -2), (key2095, -2), (key2193, -6), (key2302, 2), (key2302, 2), (key2091, 2)]

def rawRow3650 : Integer.Sparse Key := [(key2378, -2), (key2378, -2), (key2381, -2), (key2390, 2), (key2392, 2), (key2392, 2), (key2406, 2), (key2406, 2), (key2409, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2543, -1), (key2482, -1), (key2543, -1), (key2437, -2), (key2440, -2), (key2440, -2), (key2503, 1), (key2506, 1), (key2503, 1), (key2554, 1), (key2506, 1), (key2554, 1)]

def rawRow3651 : Integer.Sparse Key := [(key2378, -2), (key2381, -2), (key2378, -2), (key2392, 2), (key2390, 2), (key2392, 2), (key2406, 2), (key2409, 2), (key2406, 2), (key2482, -1), (key2480, -1), (key2543, -1), (key2480, -1), (key2543, -1), (key2482, -1), (key2440, -2), (key2437, -2), (key2440, -2), (key2506, 1), (key2503, 1), (key2554, 1), (key2503, 1), (key2554, 1), (key2506, 1)]

def rawRow3652 : Integer.Sparse Key := [(key2381, -2), (key2378, -2), (key2378, -2), (key2392, 2), (key2392, 2), (key2390, 2), (key2409, 2), (key2406, 2), (key2406, 2), (key2543, -1), (key2543, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2440, -2), (key2440, -2), (key2437, -2), (key2554, 1), (key2554, 1), (key2506, 1), (key2506, 1), (key2503, 1), (key2503, 1)]

def rawRow3653 : Integer.Sparse Key := [(key2381, -2), (key2392, -2), (key2392, -2), (key2378, 2), (key2378, 2), (key2390, 2), (key2538, 2), (key2543, 2), (key2543, 2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2554, -2), (key2554, -2), (key2563, -2), (key2440, 1), (key2440, 1), (key2506, 1), (key2506, 1), (key2522, 1), (key2522, 1)]

def rawRow3654 : Integer.Sparse Key := [(key2392, -2), (key2381, -2), (key2392, -2), (key2378, 2), (key2390, 2), (key2378, 2), (key2543, 2), (key2538, 2), (key2543, 2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2554, -2), (key2563, -2), (key2554, -2), (key2506, 1), (key2522, 1), (key2440, 1), (key2522, 1), (key2440, 1), (key2506, 1)]

def rawRow3655 : Integer.Sparse Key := [(key2392, -2), (key2392, -2), (key2381, -2), (key2390, 2), (key2378, 2), (key2378, 2), (key2543, 2), (key2543, 2), (key2538, 2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2563, -2), (key2554, -2), (key2554, -2), (key2522, 1), (key2506, 1), (key2522, 1), (key2440, 1), (key2506, 1), (key2440, 1)]

def rawRow3656 : Integer.Sparse Key := [(key2406, -2), (key2406, -2), (key2409, -2), (key2437, 2), (key2440, 2), (key2440, 2), (key2378, 2), (key2378, 2), (key2381, 2), (key2503, -1), (key2506, -1), (key2503, -1), (key2554, -1), (key2506, -1), (key2554, -1), (key2390, -2), (key2392, -2), (key2392, -2), (key2480, 1), (key2482, 1), (key2480, 1), (key2543, 1), (key2482, 1), (key2543, 1)]

def rawRow3657 : Integer.Sparse Key := [(key2406, -2), (key2409, -2), (key2406, -2), (key2440, 2), (key2437, 2), (key2440, 2), (key2378, 2), (key2381, 2), (key2378, 2), (key2506, -1), (key2503, -1), (key2554, -1), (key2503, -1), (key2554, -1), (key2506, -1), (key2392, -2), (key2390, -2), (key2392, -2), (key2482, 1), (key2480, 1), (key2543, 1), (key2480, 1), (key2543, 1), (key2482, 1)]

def rawRow3658 : Integer.Sparse Key := [(key2409, -2), (key2406, -2), (key2406, -2), (key2440, 2), (key2440, 2), (key2437, 2), (key2381, 2), (key2378, 2), (key2378, 2), (key2554, -1), (key2554, -1), (key2506, -1), (key2506, -1), (key2503, -1), (key2503, -1), (key2392, -2), (key2392, -2), (key2390, -2), (key2543, 1), (key2543, 1), (key2482, 1), (key2482, 1), (key2480, 1), (key2480, 1)]

def rawRow3659 : Integer.Sparse Key := [(key2409, -2), (key2440, -2), (key2440, -2), (key2406, 2), (key2406, 2), (key2437, 2), (key2538, 2), (key2554, 2), (key2554, 2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2543, -2), (key2543, -2), (key2563, -2), (key2392, 1), (key2392, 1), (key2482, 1), (key2482, 1), (key2522, 1), (key2522, 1)]

def rawRow3660 : Integer.Sparse Key := [(key2440, -2), (key2409, -2), (key2440, -2), (key2406, 2), (key2437, 2), (key2406, 2), (key2554, 2), (key2538, 2), (key2554, 2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2543, -2), (key2563, -2), (key2543, -2), (key2482, 1), (key2522, 1), (key2392, 1), (key2522, 1), (key2392, 1), (key2482, 1)]

def rawRow3661 : Integer.Sparse Key := [(key2440, -2), (key2440, -2), (key2409, -2), (key2437, 2), (key2406, 2), (key2406, 2), (key2554, 2), (key2554, 2), (key2538, 2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2563, -2), (key2543, -2), (key2543, -2), (key2522, 1), (key2482, 1), (key2522, 1), (key2392, 1), (key2482, 1), (key2392, 1)]

def rawRow3662 : Integer.Sparse Key := [(key2538, -2), (key2543, -2), (key2543, -2), (key2554, 2), (key2554, 2), (key2563, 2), (key2381, 2), (key2392, 2), (key2392, 2), (key2440, -1), (key2440, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, 1), (key2406, 1), (key2472, 1), (key2472, 1), (key2480, 1), (key2480, 1)]

def rawRow3663 : Integer.Sparse Key := [(key2543, -2), (key2538, -2), (key2543, -2), (key2554, 2), (key2563, 2), (key2554, 2), (key2392, 2), (key2381, 2), (key2392, 2), (key2506, -1), (key2522, -1), (key2440, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, 1), (key2480, 1), (key2406, 1), (key2480, 1), (key2406, 1), (key2472, 1)]

def rawRow3664 : Integer.Sparse Key := [(key2543, -2), (key2543, -2), (key2538, -2), (key2563, 2), (key2554, 2), (key2554, 2), (key2392, 2), (key2392, 2), (key2381, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2440, -1), (key2506, -1), (key2440, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, 1), (key2472, 1), (key2480, 1), (key2406, 1), (key2472, 1), (key2406, 1)]

def rawRow3665 : Integer.Sparse Key := [(key2538, -2), (key2554, -2), (key2554, -2), (key2543, 2), (key2543, 2), (key2563, 2), (key2409, 2), (key2440, 2), (key2440, 2), (key2392, -1), (key2392, -1), (key2482, -1), (key2482, -1), (key2522, -1), (key2522, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, 1), (key2378, 1), (key2472, 1), (key2472, 1), (key2503, 1), (key2503, 1)]

def rawRow3666 : Integer.Sparse Key := [(key2554, -2), (key2538, -2), (key2554, -2), (key2543, 2), (key2563, 2), (key2543, 2), (key2440, 2), (key2409, 2), (key2440, 2), (key2482, -1), (key2522, -1), (key2392, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, 1), (key2503, 1), (key2378, 1), (key2503, 1), (key2378, 1), (key2472, 1)]

def rawRow3667 : Integer.Sparse Key := [(key2554, -2), (key2554, -2), (key2538, -2), (key2563, 2), (key2543, 2), (key2543, 2), (key2440, 2), (key2440, 2), (key2409, 2), (key2522, -1), (key2482, -1), (key2522, -1), (key2392, -1), (key2482, -1), (key2392, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, 1), (key2472, 1), (key2503, 1), (key2378, 1), (key2472, 1), (key2378, 1)]

def rawRow3668 : Integer.Sparse Key := [(key2779, -1), (key2783, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2791, 2), (key2791, 2), (key2942, 2), (key2802, 1), (key2806, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2949, 1), (key2857, -1), (key2896, -1), (key2857, -1), (key2975, -1), (key2896, -1), (key2975, -1), (key2826, -2), (key2826, -2), (key2959, -2), (key2867, 1), (key2903, 1), (key2867, 1), (key2982, 1), (key2903, 1), (key2982, 1)]

def rawRow3669 : Integer.Sparse Key := [(key2783, -1), (key2779, -1), (key2937, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2791, 2), (key2942, 2), (key2791, 2), (key2806, 1), (key2802, 1), (key2949, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2896, -1), (key2857, -1), (key2975, -1), (key2857, -1), (key2975, -1), (key2896, -1), (key2826, -2), (key2959, -2), (key2826, -2), (key2903, 1), (key2867, 1), (key2982, 1), (key2867, 1), (key2982, 1), (key2903, 1)]

def rawRow3670 : Integer.Sparse Key := [(key2937, -1), (key2937, -1), (key2783, -1), (key2783, -1), (key2779, -1), (key2779, -1), (key2942, 2), (key2791, 2), (key2791, 2), (key2949, 1), (key2949, 1), (key2806, 1), (key2806, 1), (key2802, 1), (key2802, 1), (key2975, -1), (key2975, -1), (key2896, -1), (key2896, -1), (key2857, -1), (key2857, -1), (key2959, -2), (key2826, -2), (key2826, -2), (key2982, 1), (key2982, 1), (key2903, 1), (key2903, 1), (key2867, 1), (key2867, 1)]

def rawRow3671 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2783, -1), (key2783, -1), (key2791, -1), (key2791, -1), (key2664, 2), (key2779, 2), (key2779, 2), (key2736, 1), (key2736, 1), (key2894, 1), (key2894, 1), (key2896, 1), (key2896, 1), (key2699, -1), (key2699, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2746, -2), (key2903, -2), (key2903, -2), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1)]

def rawRow3672 : Integer.Sparse Key := [(key2783, -1), (key2791, -1), (key2668, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2779, 2), (key2664, 2), (key2779, 2), (key2894, 1), (key2896, 1), (key2736, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2802, -1), (key2852, -1), (key2699, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2903, -2), (key2746, -2), (key2903, -2), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1)]

def rawRow3673 : Integer.Sparse Key := [(key2791, -1), (key2783, -1), (key2791, -1), (key2668, -1), (key2783, -1), (key2668, -1), (key2779, 2), (key2779, 2), (key2664, 2), (key2896, 1), (key2894, 1), (key2896, 1), (key2736, 1), (key2894, 1), (key2736, 1), (key2852, -1), (key2802, -1), (key2852, -1), (key2699, -1), (key2802, -1), (key2699, -1), (key2903, -2), (key2903, -2), (key2746, -2), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1)]

def rawRow3674 : Integer.Sparse Key := [(key2802, -1), (key2806, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2949, -1), (key2826, 2), (key2826, 2), (key2959, 2), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1), (key2867, -1), (key2903, -1), (key2867, -1), (key2982, -1), (key2903, -1), (key2982, -1), (key2791, -2), (key2791, -2), (key2942, -2), (key2857, 1), (key2896, 1), (key2857, 1), (key2975, 1), (key2896, 1), (key2975, 1)]

def rawRow3675 : Integer.Sparse Key := [(key2806, -1), (key2802, -1), (key2949, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2826, 2), (key2959, 2), (key2826, 2), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2903, -1), (key2867, -1), (key2982, -1), (key2867, -1), (key2982, -1), (key2903, -1), (key2791, -2), (key2942, -2), (key2791, -2), (key2896, 1), (key2857, 1), (key2975, 1), (key2857, 1), (key2975, 1), (key2896, 1)]

def rawRow3676 : Integer.Sparse Key := [(key2949, -1), (key2949, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2959, 2), (key2826, 2), (key2826, 2), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1), (key2982, -1), (key2982, -1), (key2903, -1), (key2903, -1), (key2867, -1), (key2867, -1), (key2942, -2), (key2791, -2), (key2791, -2), (key2975, 1), (key2975, 1), (key2896, 1), (key2896, 1), (key2857, 1), (key2857, 1)]

def rawRow3677 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2826, -1), (key2826, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2647, 1), (key2647, 1), (key2894, 1), (key2894, 1), (key2903, 1), (key2903, 1), (key2625, -1), (key2625, -1), (key2779, -1), (key2779, -1), (key2852, -1), (key2852, -1), (key2652, -2), (key2896, -2), (key2896, -2), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1)]

def rawRow3678 : Integer.Sparse Key := [(key2806, -1), (key2826, -1), (key2613, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2894, 1), (key2903, 1), (key2647, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2779, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2896, -2), (key2652, -2), (key2896, -2), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1)]

def rawRow3679 : Integer.Sparse Key := [(key2826, -1), (key2806, -1), (key2826, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2903, 1), (key2894, 1), (key2903, 1), (key2647, 1), (key2894, 1), (key2647, 1), (key2852, -1), (key2779, -1), (key2852, -1), (key2625, -1), (key2779, -1), (key2625, -1), (key2896, -2), (key2896, -2), (key2652, -2), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1)]

def rawRow3680 : Integer.Sparse Key := [(key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2896, -1), (key2896, -1), (key2746, 2), (key2903, 2), (key2903, 2), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2723, -1), (key2723, -1), (key2826, -1), (key2826, -1), (key2867, -1), (key2867, -1), (key2664, -2), (key2779, -2), (key2779, -2), (key2699, 1), (key2699, 1), (key2802, 1), (key2802, 1), (key2852, 1), (key2852, 1)]

def rawRow3681 : Integer.Sparse Key := [(key2894, -1), (key2896, -1), (key2736, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2903, 2), (key2746, 2), (key2903, 2), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2826, -1), (key2867, -1), (key2723, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2779, -2), (key2664, -2), (key2779, -2), (key2802, 1), (key2852, 1), (key2699, 1), (key2852, 1), (key2699, 1), (key2802, 1)]

def rawRow3682 : Integer.Sparse Key := [(key2896, -1), (key2894, -1), (key2896, -1), (key2736, -1), (key2894, -1), (key2736, -1), (key2903, 2), (key2903, 2), (key2746, 2), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2867, -1), (key2826, -1), (key2867, -1), (key2723, -1), (key2826, -1), (key2723, -1), (key2779, -2), (key2779, -2), (key2664, -2), (key2852, 1), (key2802, 1), (key2852, 1), (key2699, 1), (key2802, 1), (key2699, 1)]

def rawRow3683 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2894, -1), (key2894, -1), (key2903, -1), (key2903, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2637, -1), (key2637, -1), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2609, -2), (key2802, -2), (key2802, -2), (key2625, 1), (key2625, 1), (key2779, 1), (key2779, 1), (key2852, 1), (key2852, 1)]

def rawRow3684 : Integer.Sparse Key := [(key2894, -1), (key2903, -1), (key2647, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2791, -1), (key2857, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2802, -2), (key2609, -2), (key2802, -2), (key2779, 1), (key2852, 1), (key2625, 1), (key2852, 1), (key2625, 1), (key2779, 1)]

def rawRow3685 : Integer.Sparse Key := [(key2903, -1), (key2894, -1), (key2903, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2857, -1), (key2791, -1), (key2857, -1), (key2637, -1), (key2791, -1), (key2637, -1), (key2802, -2), (key2802, -2), (key2609, -2), (key2852, 1), (key2779, 1), (key2852, 1), (key2625, 1), (key2779, 1), (key2625, 1)]

def rawRow3686 : Integer.Sparse Key := [(key2608, -2), (key2611, -2), (key2611, -2), (key2645, 2), (key2645, 2), (key2651, 2), (key2663, 2), (key2666, 2), (key2666, 2), (key2734, -2), (key2734, -2), (key2745, -2), (key2935, -2), (key2935, -2), (key2941, -2), (key2947, 2), (key2947, 2), (key2958, 2)]

def rawRow3687 : Integer.Sparse Key := [(key2611, -2), (key2608, -2), (key2611, -2), (key2645, 2), (key2651, 2), (key2645, 2), (key2666, 2), (key2663, 2), (key2666, 2), (key2734, -2), (key2745, -2), (key2734, -2), (key2935, -2), (key2941, -2), (key2935, -2), (key2947, 2), (key2958, 2), (key2947, 2)]

def rawRow3688 : Integer.Sparse Key := [(key2611, -2), (key2611, -2), (key2608, -2), (key2651, 2), (key2645, 2), (key2645, 2), (key2666, 2), (key2666, 2), (key2663, 2), (key2745, -2), (key2734, -2), (key2734, -2), (key2941, -2), (key2935, -2), (key2935, -2), (key2958, 2), (key2947, 2), (key2947, 2)]

def rawRow3689 : Integer.Sparse Key := [(key2645, -2), (key2645, -2), (key2651, -2), (key2608, 2), (key2624, 2), (key2624, 2), (key2722, 2), (key2722, 2), (key2745, 2), (key2663, -2), (key2698, -2), (key2698, -2), (key2958, -2), (key2981, -2), (key2981, -2), (key2941, 2), (key2974, 2), (key2974, 2)]

def rawRow3690 : Integer.Sparse Key := [(key2645, -2), (key2651, -2), (key2645, -2), (key2624, 2), (key2608, 2), (key2624, 2), (key2722, 2), (key2745, 2), (key2722, 2), (key2698, -2), (key2663, -2), (key2698, -2), (key2981, -2), (key2958, -2), (key2981, -2), (key2974, 2), (key2941, 2), (key2974, 2)]

def rawRow3691 : Integer.Sparse Key := [(key2651, -2), (key2645, -2), (key2645, -2), (key2624, 2), (key2624, 2), (key2608, 2), (key2745, 2), (key2722, 2), (key2722, 2), (key2698, -2), (key2698, -2), (key2663, -2), (key2981, -2), (key2981, -2), (key2958, -2), (key2974, 2), (key2974, 2), (key2941, 2)]

def rawRow3692 : Integer.Sparse Key := [(key2663, -2), (key2666, -2), (key2666, -2), (key2722, 2), (key2722, 2), (key2745, 2), (key2608, 2), (key2611, 2), (key2611, 2), (key2947, -2), (key2947, -2), (key2958, -2), (key2645, -2), (key2645, -2), (key2651, -2), (key2734, 2), (key2734, 2), (key2745, 2)]

def rawRow3693 : Integer.Sparse Key := [(key2666, -2), (key2663, -2), (key2666, -2), (key2722, 2), (key2745, 2), (key2722, 2), (key2611, 2), (key2608, 2), (key2611, 2), (key2947, -2), (key2958, -2), (key2947, -2), (key2645, -2), (key2651, -2), (key2645, -2), (key2734, 2), (key2745, 2), (key2734, 2)]

def rawRow3694 : Integer.Sparse Key := [(key2666, -2), (key2666, -2), (key2663, -2), (key2745, 2), (key2722, 2), (key2722, 2), (key2611, 2), (key2611, 2), (key2608, 2), (key2958, -2), (key2947, -2), (key2947, -2), (key2651, -2), (key2645, -2), (key2645, -2), (key2745, 2), (key2734, 2), (key2734, 2)]

def rawRow3695 : Integer.Sparse Key := [(key2734, -2), (key2734, -2), (key2745, -2), (key2663, 2), (key2698, 2), (key2698, 2), (key2947, 2), (key2947, 2), (key2958, 2), (key2608, -2), (key2801, -2), (key2801, -2), (key2745, -2), (key2902, -2), (key2902, -2), (key2651, 2), (key2895, 2), (key2895, 2)]

def rawRow3696 : Integer.Sparse Key := [(key2734, -2), (key2745, -2), (key2734, -2), (key2698, 2), (key2663, 2), (key2698, 2), (key2947, 2), (key2958, 2), (key2947, 2), (key2801, -2), (key2608, -2), (key2801, -2), (key2902, -2), (key2745, -2), (key2902, -2), (key2895, 2), (key2651, 2), (key2895, 2)]

def rawRow3697 : Integer.Sparse Key := [(key2745, -2), (key2734, -2), (key2734, -2), (key2698, 2), (key2698, 2), (key2663, 2), (key2958, 2), (key2947, 2), (key2947, 2), (key2801, -2), (key2801, -2), (key2608, -2), (key2902, -2), (key2902, -2), (key2745, -2), (key2895, 2), (key2895, 2), (key2651, 2)]

def rawRow3698 : Integer.Sparse Key := [(key2935, -2), (key2935, -2), (key2941, -2), (key2958, 2), (key2981, 2), (key2981, 2), (key2645, 2), (key2645, 2), (key2651, 2), (key2745, -2), (key2902, -2), (key2902, -2), (key2608, -2), (key2624, -2), (key2624, -2), (key2663, 2), (key2698, 2), (key2698, 2)]

def rawRow3699 : Integer.Sparse Key := [(key2935, -2), (key2941, -2), (key2935, -2), (key2981, 2), (key2958, 2), (key2981, 2), (key2645, 2), (key2651, 2), (key2645, 2), (key2902, -2), (key2745, -2), (key2902, -2), (key2624, -2), (key2608, -2), (key2624, -2), (key2698, 2), (key2663, 2), (key2698, 2)]

def rawRow3700 : Integer.Sparse Key := [(key2941, -2), (key2935, -2), (key2935, -2), (key2981, 2), (key2981, 2), (key2958, 2), (key2651, 2), (key2645, 2), (key2645, 2), (key2902, -2), (key2902, -2), (key2745, -2), (key2624, -2), (key2624, -2), (key2608, -2), (key2698, 2), (key2698, 2), (key2663, 2)]

def rawRow3701 : Integer.Sparse Key := [(key2947, -2), (key2947, -2), (key2958, -2), (key2941, 2), (key2974, 2), (key2974, 2), (key2734, 2), (key2734, 2), (key2745, 2), (key2651, -2), (key2895, -2), (key2895, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key2608, 2), (key2801, 2), (key2801, 2)]

def rawRow3702 : Integer.Sparse Key := [(key2947, -2), (key2958, -2), (key2947, -2), (key2974, 2), (key2941, 2), (key2974, 2), (key2734, 2), (key2745, 2), (key2734, 2), (key2895, -2), (key2651, -2), (key2895, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key2801, 2), (key2608, 2), (key2801, 2)]

def rawRow3703 : Integer.Sparse Key := [(key2958, -2), (key2947, -2), (key2947, -2), (key2974, 2), (key2974, 2), (key2941, 2), (key2745, 2), (key2734, 2), (key2734, 2), (key2895, -2), (key2895, -2), (key2651, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key2801, 2), (key2801, 2), (key2608, 2)]

def rawRow3710 : Integer.Sparse Key := [(key1302, -2), (key1790, -2), (key1790, -2), (key1296, 1), (key1296, 1), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1329, 2), (key1817, 2), (key1817, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1345, -1), (key1345, -1), (key1659, -1), (key1659, -1), (key1841, -1), (key1841, -1), (key1339, 1), (key1339, 1), (key1457, 1), (key1457, 1), (key1839, 1), (key1839, 1)]

def rawRow3711 : Integer.Sparse Key := [(key1790, -2), (key1302, -2), (key1790, -2), (key1573, 1), (key1788, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1817, 2), (key1329, 2), (key1817, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1659, -1), (key1841, -1), (key1345, -1), (key1841, -1), (key1345, -1), (key1659, -1), (key1457, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1457, 1)]

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

def rawRow3712 : Integer.Sparse Key := [(key1790, -2), (key1790, -2), (key1302, -2), (key1788, 1), (key1573, 1), (key1788, 1), (key1296, 1), (key1573, 1), (key1296, 1), (key1817, 2), (key1817, 2), (key1329, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1841, -1), (key1659, -1), (key1841, -1), (key1345, -1), (key1659, -1), (key1345, -1), (key1839, 1), (key1457, 1), (key1839, 1), (key1339, 1), (key1457, 1), (key1339, 1)]

def rawRow3725 : Integer.Sparse Key := [(key1329, -2), (key1817, -2), (key1817, -2), (key1345, 1), (key1345, 1), (key1659, 1), (key1659, 1), (key1841, 1), (key1841, 1), (key1302, 2), (key1790, 2), (key1790, 2), (key1339, -1), (key1339, -1), (key1457, -1), (key1457, -1), (key1839, -1), (key1839, -1), (key1296, -1), (key1296, -1), (key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

def rawRow3726 : Integer.Sparse Key := [(key1817, -2), (key1329, -2), (key1817, -2), (key1659, 1), (key1841, 1), (key1345, 1), (key1841, 1), (key1345, 1), (key1659, 1), (key1790, 2), (key1302, 2), (key1790, 2), (key1457, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

def rawRow3727 : Integer.Sparse Key := [(key1817, -2), (key1817, -2), (key1329, -2), (key1841, 1), (key1659, 1), (key1841, 1), (key1345, 1), (key1659, 1), (key1345, 1), (key1790, 2), (key1790, 2), (key1302, 2), (key1839, -1), (key1457, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1339, -1), (key1788, -1), (key1573, -1), (key1788, -1), (key1296, -1), (key1573, -1), (key1296, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

def rawRow3770 : Integer.Sparse Key := [(key1556, -2), (key1556, -2), (key1899, -2), (key1393, 1), (key1393, 1), (key1548, 1), (key1548, 1), (key1896, 1), (key1896, 1), (key1593, 2), (key1593, 2), (key1911, 2), (key1298, -1), (key1298, -1), (key1575, -1), (key1575, -1), (key1903, -1), (key1903, -1), (key1444, -1), (key1444, -1), (key1633, -1), (key1633, -1), (key1926, -1), (key1926, -1), (key1326, 1), (key1326, 1), (key1624, 1), (key1624, 1), (key1920, 1), (key1920, 1)]

def rawRow3771 : Integer.Sparse Key := [(key1556, -2), (key1899, -2), (key1556, -2), (key1548, 1), (key1896, 1), (key1393, 1), (key1896, 1), (key1393, 1), (key1548, 1), (key1593, 2), (key1911, 2), (key1593, 2), (key1575, -1), (key1903, -1), (key1298, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1633, -1), (key1926, -1), (key1444, -1), (key1926, -1), (key1444, -1), (key1633, -1), (key1624, 1), (key1920, 1), (key1326, 1), (key1920, 1), (key1326, 1), (key1624, 1)]

def rawRow3772 : Integer.Sparse Key := [(key1899, -2), (key1556, -2), (key1556, -2), (key1896, 1), (key1548, 1), (key1896, 1), (key1393, 1), (key1548, 1), (key1393, 1), (key1911, 2), (key1593, 2), (key1593, 2), (key1903, -1), (key1575, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1298, -1), (key1926, -1), (key1633, -1), (key1926, -1), (key1444, -1), (key1633, -1), (key1444, -1), (key1920, 1), (key1624, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1326, 1)]

def rawRow3785 : Integer.Sparse Key := [(key1593, -2), (key1593, -2), (key1911, -2), (key1444, 1), (key1444, 1), (key1633, 1), (key1633, 1), (key1926, 1), (key1926, 1), (key1556, 2), (key1556, 2), (key1899, 2), (key1326, -1), (key1326, -1), (key1624, -1), (key1624, -1), (key1920, -1), (key1920, -1), (key1393, -1), (key1393, -1), (key1548, -1), (key1548, -1), (key1896, -1), (key1896, -1), (key1298, 1), (key1298, 1), (key1575, 1), (key1575, 1), (key1903, 1), (key1903, 1)]

def rawRow3786 : Integer.Sparse Key := [(key1593, -2), (key1911, -2), (key1593, -2), (key1633, 1), (key1926, 1), (key1444, 1), (key1926, 1), (key1444, 1), (key1633, 1), (key1556, 2), (key1899, 2), (key1556, 2), (key1624, -1), (key1920, -1), (key1326, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1548, -1), (key1896, -1), (key1393, -1), (key1896, -1), (key1393, -1), (key1548, -1), (key1575, 1), (key1903, 1), (key1298, 1), (key1903, 1), (key1298, 1), (key1575, 1)]

def rawRow3787 : Integer.Sparse Key := [(key1911, -2), (key1593, -2), (key1593, -2), (key1926, 1), (key1633, 1), (key1926, 1), (key1444, 1), (key1633, 1), (key1444, 1), (key1899, 2), (key1556, 2), (key1556, 2), (key1920, -1), (key1624, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1326, -1), (key1896, -1), (key1548, -1), (key1896, -1), (key1393, -1), (key1548, -1), (key1393, -1), (key1903, 1), (key1575, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1298, 1)]

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

def rawRow3860 : Integer.Sparse Key := [(key240, -1), (key240, -1), (key410, -1), (key410, -1), (key420, -1), (key420, -1), (key237, 2), (key407, 2), (key407, 2), (key268, 1), (key268, 1), (key468, 1), (key468, 1), (key477, 1), (key477, 1), (key249, -1), (key249, -1), (key386, -1), (key386, -1), (key436, -1), (key436, -1), (key273, -2), (key471, -2), (key471, -2), (key262, 1), (key262, 1), (key399, 1), (key399, 1), (key444, 1), (key444, 1)]

def rawRow3861 : Integer.Sparse Key := [(key410, -1), (key420, -1), (key240, -1), (key420, -1), (key240, -1), (key410, -1), (key407, 2), (key237, 2), (key407, 2), (key468, 1), (key477, 1), (key268, 1), (key477, 1), (key268, 1), (key468, 1), (key386, -1), (key436, -1), (key249, -1), (key436, -1), (key249, -1), (key386, -1), (key471, -2), (key273, -2), (key471, -2), (key399, 1), (key444, 1), (key262, 1), (key444, 1), (key262, 1), (key399, 1)]

def rawRow3862 : Integer.Sparse Key := [(key420, -1), (key410, -1), (key420, -1), (key240, -1), (key410, -1), (key240, -1), (key407, 2), (key407, 2), (key237, 2), (key477, 1), (key468, 1), (key477, 1), (key268, 1), (key468, 1), (key268, 1), (key436, -1), (key386, -1), (key436, -1), (key249, -1), (key386, -1), (key249, -1), (key471, -2), (key471, -2), (key273, -2), (key444, 1), (key399, 1), (key444, 1), (key262, 1), (key399, 1), (key262, 1)]

def rawRow3875 : Integer.Sparse Key := [(key268, -1), (key268, -1), (key468, -1), (key468, -1), (key477, -1), (key477, -1), (key273, 2), (key471, 2), (key471, 2), (key240, 1), (key240, 1), (key410, 1), (key410, 1), (key420, 1), (key420, 1), (key262, -1), (key262, -1), (key399, -1), (key399, -1), (key444, -1), (key444, -1), (key237, -2), (key407, -2), (key407, -2), (key249, 1), (key249, 1), (key386, 1), (key386, 1), (key436, 1), (key436, 1)]

def rawRow3876 : Integer.Sparse Key := [(key468, -1), (key477, -1), (key268, -1), (key477, -1), (key268, -1), (key468, -1), (key471, 2), (key273, 2), (key471, 2), (key410, 1), (key420, 1), (key240, 1), (key420, 1), (key240, 1), (key410, 1), (key399, -1), (key444, -1), (key262, -1), (key444, -1), (key262, -1), (key399, -1), (key407, -2), (key237, -2), (key407, -2), (key386, 1), (key436, 1), (key249, 1), (key436, 1), (key249, 1), (key386, 1)]

def rawRow3877 : Integer.Sparse Key := [(key477, -1), (key468, -1), (key477, -1), (key268, -1), (key468, -1), (key268, -1), (key471, 2), (key471, 2), (key273, 2), (key420, 1), (key410, 1), (key420, 1), (key240, 1), (key410, 1), (key240, 1), (key444, -1), (key399, -1), (key444, -1), (key262, -1), (key399, -1), (key262, -1), (key407, -2), (key407, -2), (key237, -2), (key436, 1), (key386, 1), (key436, 1), (key249, 1), (key386, 1), (key249, 1)]

def rawRow3920 : Integer.Sparse Key := [(key336, -2), (key336, -2), (key342, -2), (key306, 1), (key306, 1), (key320, 1), (key320, 1), (key330, 1), (key330, 1), (key579, 2), (key579, 2), (key585, 2), (key240, -1), (key240, -1), (key410, -1), (key410, -1), (key420, -1), (key420, -1), (key569, -1), (key569, -1), (key594, -1), (key594, -1), (key603, -1), (key603, -1), (key268, 1), (key268, 1), (key468, 1), (key468, 1), (key477, 1), (key477, 1)]

def rawRow3921 : Integer.Sparse Key := [(key336, -2), (key342, -2), (key336, -2), (key320, 1), (key330, 1), (key306, 1), (key330, 1), (key306, 1), (key320, 1), (key579, 2), (key585, 2), (key579, 2), (key410, -1), (key420, -1), (key240, -1), (key420, -1), (key240, -1), (key410, -1), (key594, -1), (key603, -1), (key569, -1), (key603, -1), (key569, -1), (key594, -1), (key468, 1), (key477, 1), (key268, 1), (key477, 1), (key268, 1), (key468, 1)]

def rawRow3922 : Integer.Sparse Key := [(key342, -2), (key336, -2), (key336, -2), (key330, 1), (key320, 1), (key330, 1), (key306, 1), (key320, 1), (key306, 1), (key585, 2), (key579, 2), (key579, 2), (key420, -1), (key410, -1), (key420, -1), (key240, -1), (key410, -1), (key240, -1), (key603, -1), (key594, -1), (key603, -1), (key569, -1), (key594, -1), (key569, -1), (key477, 1), (key468, 1), (key477, 1), (key268, 1), (key468, 1), (key268, 1)]

def rawRow3935 : Integer.Sparse Key := [(key579, -2), (key579, -2), (key585, -2), (key569, 1), (key569, 1), (key594, 1), (key594, 1), (key603, 1), (key603, 1), (key336, 2), (key336, 2), (key342, 2), (key268, -1), (key268, -1), (key468, -1), (key468, -1), (key477, -1), (key477, -1), (key306, -1), (key306, -1), (key320, -1), (key320, -1), (key330, -1), (key330, -1), (key240, 1), (key240, 1), (key410, 1), (key410, 1), (key420, 1), (key420, 1)]

def rawRow3936 : Integer.Sparse Key := [(key579, -2), (key585, -2), (key579, -2), (key594, 1), (key603, 1), (key569, 1), (key603, 1), (key569, 1), (key594, 1), (key336, 2), (key342, 2), (key336, 2), (key468, -1), (key477, -1), (key268, -1), (key477, -1), (key268, -1), (key468, -1), (key320, -1), (key330, -1), (key306, -1), (key330, -1), (key306, -1), (key320, -1), (key410, 1), (key420, 1), (key240, 1), (key420, 1), (key240, 1), (key410, 1)]

def rawRow3937 : Integer.Sparse Key := [(key585, -2), (key579, -2), (key579, -2), (key603, 1), (key594, 1), (key603, 1), (key569, 1), (key594, 1), (key569, 1), (key342, 2), (key336, 2), (key336, 2), (key477, -1), (key468, -1), (key477, -1), (key268, -1), (key468, -1), (key268, -1), (key330, -1), (key320, -1), (key330, -1), (key306, -1), (key320, -1), (key306, -1), (key420, 1), (key410, 1), (key420, 1), (key240, 1), (key410, 1), (key240, 1)]

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

def rawRow3980 : Integer.Sparse Key := [(key1397, -2), (key1774, -2), (key1774, -2), (key1391, 1), (key1391, 1), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1447, 2), (key1825, 2), (key1825, 2), (key1316, -1), (key1316, -1), (key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1466, -1), (key1466, -1), (key1667, -1), (key1667, -1), (key1844, -1), (key1844, -1), (key1339, 1), (key1339, 1), (key1457, 1), (key1457, 1), (key1839, 1), (key1839, 1)]

def rawRow3981 : Integer.Sparse Key := [(key1774, -2), (key1397, -2), (key1774, -2), (key1546, 1), (key1772, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1546, 1), (key1825, 2), (key1447, 2), (key1825, 2), (key1424, -1), (key1813, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1667, -1), (key1844, -1), (key1466, -1), (key1844, -1), (key1466, -1), (key1667, -1), (key1457, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1457, 1)]

def rawRow3982 : Integer.Sparse Key := [(key1774, -2), (key1774, -2), (key1397, -2), (key1772, 1), (key1546, 1), (key1772, 1), (key1391, 1), (key1546, 1), (key1391, 1), (key1825, 2), (key1825, 2), (key1447, 2), (key1813, -1), (key1424, -1), (key1813, -1), (key1316, -1), (key1424, -1), (key1316, -1), (key1844, -1), (key1667, -1), (key1844, -1), (key1466, -1), (key1667, -1), (key1466, -1), (key1839, 1), (key1457, 1), (key1839, 1), (key1339, 1), (key1457, 1), (key1339, 1)]

def rawRow3995 : Integer.Sparse Key := [(key1447, -2), (key1825, -2), (key1825, -2), (key1466, 1), (key1466, 1), (key1667, 1), (key1667, 1), (key1844, 1), (key1844, 1), (key1397, 2), (key1774, 2), (key1774, 2), (key1339, -1), (key1339, -1), (key1457, -1), (key1457, -1), (key1839, -1), (key1839, -1), (key1391, -1), (key1391, -1), (key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1316, 1), (key1316, 1), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1)]

def rawRow3996 : Integer.Sparse Key := [(key1825, -2), (key1447, -2), (key1825, -2), (key1667, 1), (key1844, 1), (key1466, 1), (key1844, 1), (key1466, 1), (key1667, 1), (key1774, 2), (key1397, 2), (key1774, 2), (key1457, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1546, -1), (key1772, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1546, -1), (key1424, 1), (key1813, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1424, 1)]

def rawRow3997 : Integer.Sparse Key := [(key1825, -2), (key1825, -2), (key1447, -2), (key1844, 1), (key1667, 1), (key1844, 1), (key1466, 1), (key1667, 1), (key1466, 1), (key1774, 2), (key1774, 2), (key1397, 2), (key1839, -1), (key1457, -1), (key1839, -1), (key1339, -1), (key1457, -1), (key1339, -1), (key1772, -1), (key1546, -1), (key1772, -1), (key1391, -1), (key1546, -1), (key1391, -1), (key1813, 1), (key1424, 1), (key1813, 1), (key1316, 1), (key1424, 1), (key1316, 1)]

def rawRow4070 : Integer.Sparse Key := [(key1554, -2), (key1554, -2), (key1778, -2), (key1390, 1), (key1390, 1), (key1545, 1), (key1545, 1), (key1771, 1), (key1771, 1), (key1591, 2), (key1591, 2), (key1796, 2), (key1295, -1), (key1295, -1), (key1572, -1), (key1572, -1), (key1787, -1), (key1787, -1), (key1442, -1), (key1442, -1), (key1631, -1), (key1631, -1), (key1823, -1), (key1823, -1), (key1324, 1), (key1324, 1), (key1622, 1), (key1622, 1), (key1815, 1), (key1815, 1)]

def rawRow4071 : Integer.Sparse Key := [(key1554, -2), (key1778, -2), (key1554, -2), (key1545, 1), (key1771, 1), (key1390, 1), (key1771, 1), (key1390, 1), (key1545, 1), (key1591, 2), (key1796, 2), (key1591, 2), (key1572, -1), (key1787, -1), (key1295, -1), (key1787, -1), (key1295, -1), (key1572, -1), (key1631, -1), (key1823, -1), (key1442, -1), (key1823, -1), (key1442, -1), (key1631, -1), (key1622, 1), (key1815, 1), (key1324, 1), (key1815, 1), (key1324, 1), (key1622, 1)]

def rawRow4072 : Integer.Sparse Key := [(key1778, -2), (key1554, -2), (key1554, -2), (key1771, 1), (key1545, 1), (key1771, 1), (key1390, 1), (key1545, 1), (key1390, 1), (key1796, 2), (key1591, 2), (key1591, 2), (key1787, -1), (key1572, -1), (key1787, -1), (key1295, -1), (key1572, -1), (key1295, -1), (key1823, -1), (key1631, -1), (key1823, -1), (key1442, -1), (key1631, -1), (key1442, -1), (key1815, 1), (key1622, 1), (key1815, 1), (key1324, 1), (key1622, 1), (key1324, 1)]

def rawRow4085 : Integer.Sparse Key := [(key1591, -2), (key1591, -2), (key1796, -2), (key1442, 1), (key1442, 1), (key1631, 1), (key1631, 1), (key1823, 1), (key1823, 1), (key1554, 2), (key1554, 2), (key1778, 2), (key1324, -1), (key1324, -1), (key1622, -1), (key1622, -1), (key1815, -1), (key1815, -1), (key1390, -1), (key1390, -1), (key1545, -1), (key1545, -1), (key1771, -1), (key1771, -1), (key1295, 1), (key1295, 1), (key1572, 1), (key1572, 1), (key1787, 1), (key1787, 1)]

def rawRow4086 : Integer.Sparse Key := [(key1591, -2), (key1796, -2), (key1591, -2), (key1631, 1), (key1823, 1), (key1442, 1), (key1823, 1), (key1442, 1), (key1631, 1), (key1554, 2), (key1778, 2), (key1554, 2), (key1622, -1), (key1815, -1), (key1324, -1), (key1815, -1), (key1324, -1), (key1622, -1), (key1545, -1), (key1771, -1), (key1390, -1), (key1771, -1), (key1390, -1), (key1545, -1), (key1572, 1), (key1787, 1), (key1295, 1), (key1787, 1), (key1295, 1), (key1572, 1)]

def rawRow4087 : Integer.Sparse Key := [(key1796, -2), (key1591, -2), (key1591, -2), (key1823, 1), (key1631, 1), (key1823, 1), (key1442, 1), (key1631, 1), (key1442, 1), (key1778, 2), (key1554, 2), (key1554, 2), (key1815, -1), (key1622, -1), (key1815, -1), (key1324, -1), (key1622, -1), (key1324, -1), (key1771, -1), (key1545, -1), (key1771, -1), (key1390, -1), (key1545, -1), (key1390, -1), (key1787, 1), (key1572, 1), (key1787, 1), (key1295, 1), (key1572, 1), (key1295, 1)]

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

def rawRow4160 : Integer.Sparse Key := [(key1298, -1), (key1298, -1), (key1575, -1), (key1575, -1), (key1903, -1), (key1903, -1), (key1292, 2), (key1569, 2), (key1569, 2), (key1326, 1), (key1326, 1), (key1624, 1), (key1624, 1), (key1920, 1), (key1920, 1), (key1312, -1), (key1312, -1), (key1420, -1), (key1420, -1), (key1618, -1), (key1618, -1), (key1354, -2), (key1683, -2), (key1683, -2), (key1351, 1), (key1351, 1), (key1472, 1), (key1472, 1), (key1681, 1), (key1681, 1)]

def rawRow4161 : Integer.Sparse Key := [(key1575, -1), (key1903, -1), (key1298, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1569, 2), (key1292, 2), (key1569, 2), (key1624, 1), (key1920, 1), (key1326, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1420, -1), (key1618, -1), (key1312, -1), (key1618, -1), (key1312, -1), (key1420, -1), (key1683, -2), (key1354, -2), (key1683, -2), (key1472, 1), (key1681, 1), (key1351, 1), (key1681, 1), (key1351, 1), (key1472, 1)]

def rawRow4162 : Integer.Sparse Key := [(key1903, -1), (key1575, -1), (key1903, -1), (key1298, -1), (key1575, -1), (key1298, -1), (key1569, 2), (key1569, 2), (key1292, 2), (key1920, 1), (key1624, 1), (key1920, 1), (key1326, 1), (key1624, 1), (key1326, 1), (key1618, -1), (key1420, -1), (key1618, -1), (key1312, -1), (key1420, -1), (key1312, -1), (key1683, -2), (key1683, -2), (key1354, -2), (key1681, 1), (key1472, 1), (key1681, 1), (key1351, 1), (key1472, 1), (key1351, 1)]

def rawRow4175 : Integer.Sparse Key := [(key1326, -1), (key1326, -1), (key1624, -1), (key1624, -1), (key1920, -1), (key1920, -1), (key1354, 2), (key1683, 2), (key1683, 2), (key1298, 1), (key1298, 1), (key1575, 1), (key1575, 1), (key1903, 1), (key1903, 1), (key1351, -1), (key1351, -1), (key1472, -1), (key1472, -1), (key1681, -1), (key1681, -1), (key1292, -2), (key1569, -2), (key1569, -2), (key1312, 1), (key1312, 1), (key1420, 1), (key1420, 1), (key1618, 1), (key1618, 1)]

def rawRow4176 : Integer.Sparse Key := [(key1624, -1), (key1920, -1), (key1326, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1683, 2), (key1354, 2), (key1683, 2), (key1575, 1), (key1903, 1), (key1298, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1472, -1), (key1681, -1), (key1351, -1), (key1681, -1), (key1351, -1), (key1472, -1), (key1569, -2), (key1292, -2), (key1569, -2), (key1420, 1), (key1618, 1), (key1312, 1), (key1618, 1), (key1312, 1), (key1420, 1)]

def rawRow4177 : Integer.Sparse Key := [(key1920, -1), (key1624, -1), (key1920, -1), (key1326, -1), (key1624, -1), (key1326, -1), (key1683, 2), (key1683, 2), (key1354, 2), (key1903, 1), (key1575, 1), (key1903, 1), (key1298, 1), (key1575, 1), (key1298, 1), (key1681, -1), (key1472, -1), (key1681, -1), (key1351, -1), (key1472, -1), (key1351, -1), (key1569, -2), (key1569, -2), (key1292, -2), (key1618, 1), (key1420, 1), (key1618, 1), (key1312, 1), (key1420, 1), (key1312, 1)]

def rawRow4184 : Integer.Sparse Key := [(key1541, -2), (key1545, -2), (key1771, -2), (key1390, 2), (key1545, 2), (key1554, 2), (key1568, 2), (key1572, 2), (key1787, 2), (key1295, -2), (key1572, -2), (key1591, -2), (key1454, -2), (key1654, -2), (key1657, -2), (key1336, 2), (key1654, 2), (key1665, 2)]

def rawRow4185 : Integer.Sparse Key := [(key1545, -2), (key1541, -2), (key1771, -2), (key1390, 2), (key1554, 2), (key1545, 2), (key1572, 2), (key1568, 2), (key1787, 2), (key1295, -2), (key1591, -2), (key1572, -2), (key1454, -2), (key1657, -2), (key1654, -2), (key1336, 2), (key1665, 2), (key1654, 2)]

def rawRow4186 : Integer.Sparse Key := [(key1541, -2), (key1771, -2), (key1545, -2), (key1545, 2), (key1390, 2), (key1554, 2), (key1568, 2), (key1787, 2), (key1572, 2), (key1572, -2), (key1295, -2), (key1591, -2), (key1654, -2), (key1454, -2), (key1657, -2), (key1654, 2), (key1336, 2), (key1665, 2)]

def rawRow4187 : Integer.Sparse Key := [(key1771, -2), (key1541, -2), (key1545, -2), (key1545, 2), (key1554, 2), (key1390, 2), (key1787, 2), (key1568, 2), (key1572, 2), (key1572, -2), (key1591, -2), (key1295, -2), (key1654, -2), (key1657, -2), (key1454, -2), (key1654, 2), (key1665, 2), (key1336, 2)]

def rawRow4188 : Integer.Sparse Key := [(key1545, -2), (key1771, -2), (key1541, -2), (key1554, 2), (key1390, 2), (key1545, 2), (key1572, 2), (key1787, 2), (key1568, 2), (key1591, -2), (key1295, -2), (key1572, -2), (key1657, -2), (key1454, -2), (key1654, -2), (key1665, 2), (key1336, 2), (key1654, 2)]

def rawRow4189 : Integer.Sparse Key := [(key1771, -2), (key1545, -2), (key1541, -2), (key1554, 2), (key1545, 2), (key1390, 2), (key1787, 2), (key1572, 2), (key1568, 2), (key1591, -2), (key1572, -2), (key1295, -2), (key1657, -2), (key1654, -2), (key1454, -2), (key1665, 2), (key1654, 2), (key1336, 2)]

def rawRow4190 : Integer.Sparse Key := [(key1554, -2), (key1554, -2), (key1778, -2), (key1386, 2), (key1541, 2), (key1541, 2), (key1591, 2), (key1591, 2), (key1796, 2), (key1291, -2), (key1568, -2), (key1568, -2), (key1464, -2), (key1665, -2), (key1665, -2), (key1343, 2), (key1657, 2), (key1657, 2)]

def rawRow4191 : Integer.Sparse Key := [(key1554, -2), (key1778, -2), (key1554, -2), (key1541, 2), (key1386, 2), (key1541, 2), (key1591, 2), (key1796, 2), (key1591, 2), (key1568, -2), (key1291, -2), (key1568, -2), (key1665, -2), (key1464, -2), (key1665, -2), (key1657, 2), (key1343, 2), (key1657, 2)]

def rawRow4192 : Integer.Sparse Key := [(key1778, -2), (key1554, -2), (key1554, -2), (key1541, 2), (key1541, 2), (key1386, 2), (key1796, 2), (key1591, 2), (key1591, 2), (key1568, -2), (key1568, -2), (key1291, -2), (key1665, -2), (key1665, -2), (key1464, -2), (key1657, 2), (key1657, 2), (key1343, 2)]

def rawRow4193 : Integer.Sparse Key := [(key1568, -2), (key1572, -2), (key1787, -2), (key1454, 2), (key1654, 2), (key1657, 2), (key1541, 2), (key1545, 2), (key1771, 2), (key1336, -2), (key1654, -2), (key1665, -2), (key1390, -2), (key1545, -2), (key1554, -2), (key1295, 2), (key1572, 2), (key1591, 2)]

def rawRow4194 : Integer.Sparse Key := [(key1572, -2), (key1568, -2), (key1787, -2), (key1454, 2), (key1657, 2), (key1654, 2), (key1545, 2), (key1541, 2), (key1771, 2), (key1336, -2), (key1665, -2), (key1654, -2), (key1390, -2), (key1554, -2), (key1545, -2), (key1295, 2), (key1591, 2), (key1572, 2)]

def rawRow4195 : Integer.Sparse Key := [(key1568, -2), (key1787, -2), (key1572, -2), (key1654, 2), (key1454, 2), (key1657, 2), (key1541, 2), (key1771, 2), (key1545, 2), (key1654, -2), (key1336, -2), (key1665, -2), (key1545, -2), (key1390, -2), (key1554, -2), (key1572, 2), (key1295, 2), (key1591, 2)]

def rawRow4196 : Integer.Sparse Key := [(key1787, -2), (key1568, -2), (key1572, -2), (key1654, 2), (key1657, 2), (key1454, 2), (key1771, 2), (key1541, 2), (key1545, 2), (key1654, -2), (key1665, -2), (key1336, -2), (key1545, -2), (key1554, -2), (key1390, -2), (key1572, 2), (key1591, 2), (key1295, 2)]

def rawRow4197 : Integer.Sparse Key := [(key1572, -2), (key1787, -2), (key1568, -2), (key1657, 2), (key1454, 2), (key1654, 2), (key1545, 2), (key1771, 2), (key1541, 2), (key1665, -2), (key1336, -2), (key1654, -2), (key1554, -2), (key1390, -2), (key1545, -2), (key1591, 2), (key1295, 2), (key1572, 2)]

def rawRow4198 : Integer.Sparse Key := [(key1787, -2), (key1572, -2), (key1568, -2), (key1657, 2), (key1654, 2), (key1454, 2), (key1771, 2), (key1545, 2), (key1541, 2), (key1665, -2), (key1654, -2), (key1336, -2), (key1554, -2), (key1545, -2), (key1390, -2), (key1591, 2), (key1572, 2), (key1295, 2)]

def rawRow4199 : Integer.Sparse Key := [(key1622, -2), (key1657, -2), (key1815, -2), (key1419, 2), (key1568, 2), (key1617, 2), (key1631, 2), (key1665, 2), (key1823, 2), (key1311, -2), (key1541, -2), (key1617, -2), (key1442, -2), (key1591, -2), (key1631, -2), (key1324, 2), (key1554, 2), (key1622, 2)]

def rawRow4200 : Integer.Sparse Key := [(key1657, -2), (key1622, -2), (key1815, -2), (key1419, 2), (key1617, 2), (key1568, 2), (key1665, 2), (key1631, 2), (key1823, 2), (key1311, -2), (key1617, -2), (key1541, -2), (key1442, -2), (key1631, -2), (key1591, -2), (key1324, 2), (key1622, 2), (key1554, 2)]

def rawRow4201 : Integer.Sparse Key := [(key1622, -2), (key1815, -2), (key1657, -2), (key1568, 2), (key1419, 2), (key1617, 2), (key1631, 2), (key1823, 2), (key1665, 2), (key1541, -2), (key1311, -2), (key1617, -2), (key1591, -2), (key1442, -2), (key1631, -2), (key1554, 2), (key1324, 2), (key1622, 2)]

def rawRow4202 : Integer.Sparse Key := [(key1815, -2), (key1622, -2), (key1657, -2), (key1568, 2), (key1617, 2), (key1419, 2), (key1823, 2), (key1631, 2), (key1665, 2), (key1541, -2), (key1617, -2), (key1311, -2), (key1591, -2), (key1631, -2), (key1442, -2), (key1554, 2), (key1622, 2), (key1324, 2)]

def rawRow4203 : Integer.Sparse Key := [(key1657, -2), (key1815, -2), (key1622, -2), (key1617, 2), (key1419, 2), (key1568, 2), (key1665, 2), (key1823, 2), (key1631, 2), (key1617, -2), (key1311, -2), (key1541, -2), (key1631, -2), (key1442, -2), (key1591, -2), (key1622, 2), (key1324, 2), (key1554, 2)]

def rawRow4204 : Integer.Sparse Key := [(key1815, -2), (key1657, -2), (key1622, -2), (key1617, 2), (key1568, 2), (key1419, 2), (key1823, 2), (key1665, 2), (key1631, 2), (key1617, -2), (key1541, -2), (key1311, -2), (key1631, -2), (key1591, -2), (key1442, -2), (key1622, 2), (key1554, 2), (key1324, 2)]

def rawRow4205 : Integer.Sparse Key := [(key1591, -2), (key1591, -2), (key1796, -2), (key1464, 2), (key1665, 2), (key1665, 2), (key1554, 2), (key1554, 2), (key1778, 2), (key1343, -2), (key1657, -2), (key1657, -2), (key1386, -2), (key1541, -2), (key1541, -2), (key1291, 2), (key1568, 2), (key1568, 2)]

def rawRow4206 : Integer.Sparse Key := [(key1591, -2), (key1796, -2), (key1591, -2), (key1665, 2), (key1464, 2), (key1665, 2), (key1554, 2), (key1778, 2), (key1554, 2), (key1657, -2), (key1343, -2), (key1657, -2), (key1541, -2), (key1386, -2), (key1541, -2), (key1568, 2), (key1291, 2), (key1568, 2)]

def rawRow4207 : Integer.Sparse Key := [(key1796, -2), (key1591, -2), (key1591, -2), (key1665, 2), (key1665, 2), (key1464, 2), (key1778, 2), (key1554, 2), (key1554, 2), (key1657, -2), (key1657, -2), (key1343, -2), (key1541, -2), (key1541, -2), (key1386, -2), (key1568, 2), (key1568, 2), (key1291, 2)]

def rawRow4208 : Integer.Sparse Key := [(key1631, -2), (key1665, -2), (key1823, -2), (key1442, 2), (key1591, 2), (key1631, 2), (key1622, 2), (key1657, 2), (key1815, 2), (key1324, -2), (key1554, -2), (key1622, -2), (key1419, -2), (key1568, -2), (key1617, -2), (key1311, 2), (key1541, 2), (key1617, 2)]

def rawRow4209 : Integer.Sparse Key := [(key1665, -2), (key1631, -2), (key1823, -2), (key1442, 2), (key1631, 2), (key1591, 2), (key1657, 2), (key1622, 2), (key1815, 2), (key1324, -2), (key1622, -2), (key1554, -2), (key1419, -2), (key1617, -2), (key1568, -2), (key1311, 2), (key1617, 2), (key1541, 2)]

def rawRow4210 : Integer.Sparse Key := [(key1631, -2), (key1823, -2), (key1665, -2), (key1591, 2), (key1442, 2), (key1631, 2), (key1622, 2), (key1815, 2), (key1657, 2), (key1554, -2), (key1324, -2), (key1622, -2), (key1568, -2), (key1419, -2), (key1617, -2), (key1541, 2), (key1311, 2), (key1617, 2)]

def rawRow4211 : Integer.Sparse Key := [(key1823, -2), (key1631, -2), (key1665, -2), (key1591, 2), (key1631, 2), (key1442, 2), (key1815, 2), (key1622, 2), (key1657, 2), (key1554, -2), (key1622, -2), (key1324, -2), (key1568, -2), (key1617, -2), (key1419, -2), (key1541, 2), (key1617, 2), (key1311, 2)]

def rawRow4212 : Integer.Sparse Key := [(key1665, -2), (key1823, -2), (key1631, -2), (key1631, 2), (key1442, 2), (key1591, 2), (key1657, 2), (key1815, 2), (key1622, 2), (key1622, -2), (key1324, -2), (key1554, -2), (key1617, -2), (key1419, -2), (key1568, -2), (key1617, 2), (key1311, 2), (key1541, 2)]

def rawRow4213 : Integer.Sparse Key := [(key1823, -2), (key1665, -2), (key1631, -2), (key1631, 2), (key1591, 2), (key1442, 2), (key1815, 2), (key1657, 2), (key1622, 2), (key1622, -2), (key1554, -2), (key1324, -2), (key1617, -2), (key1568, -2), (key1419, -2), (key1617, 2), (key1541, 2), (key1311, 2)]

def rawRow4220 : Integer.Sparse Key := [(key239, -1), (key239, -1), (key409, -1), (key409, -1), (key418, -1), (key418, -1), (key236, 2), (key406, 2), (key406, 2), (key260, 1), (key260, 1), (key442, 1), (key442, 1), (key595, 1), (key595, 1), (key248, -1), (key248, -1), (key316, -1), (key316, -1), (key435, -1), (key435, -1), (key271, -2), (key469, -2), (key469, -2), (key267, 1), (key267, 1), (key335, 1), (key335, 1), (key467, 1), (key467, 1)]

def rawRow4221 : Integer.Sparse Key := [(key409, -1), (key418, -1), (key239, -1), (key418, -1), (key239, -1), (key409, -1), (key406, 2), (key236, 2), (key406, 2), (key442, 1), (key595, 1), (key260, 1), (key595, 1), (key260, 1), (key442, 1), (key316, -1), (key435, -1), (key248, -1), (key435, -1), (key248, -1), (key316, -1), (key469, -2), (key271, -2), (key469, -2), (key335, 1), (key467, 1), (key267, 1), (key467, 1), (key267, 1), (key335, 1)]

def rawRow4222 : Integer.Sparse Key := [(key418, -1), (key409, -1), (key418, -1), (key239, -1), (key409, -1), (key239, -1), (key406, 2), (key406, 2), (key236, 2), (key595, 1), (key442, 1), (key595, 1), (key260, 1), (key442, 1), (key260, 1), (key435, -1), (key316, -1), (key435, -1), (key248, -1), (key316, -1), (key248, -1), (key469, -2), (key469, -2), (key271, -2), (key467, 1), (key335, 1), (key467, 1), (key267, 1), (key335, 1), (key267, 1)]

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

def rawRow4235 : Integer.Sparse Key := [(key267, -1), (key267, -1), (key467, -1), (key467, -1), (key475, -1), (key475, -1), (key271, 2), (key469, 2), (key469, 2), (key239, 1), (key239, 1), (key409, 1), (key409, 1), (key418, 1), (key418, 1), (key260, -1), (key260, -1), (key397, -1), (key397, -1), (key442, -1), (key442, -1), (key236, -2), (key406, -2), (key406, -2), (key248, 1), (key248, 1), (key316, 1), (key316, 1), (key435, 1), (key435, 1)]

def rawRow4236 : Integer.Sparse Key := [(key467, -1), (key475, -1), (key267, -1), (key475, -1), (key267, -1), (key467, -1), (key469, 2), (key271, 2), (key469, 2), (key409, 1), (key418, 1), (key239, 1), (key418, 1), (key239, 1), (key409, 1), (key397, -1), (key442, -1), (key260, -1), (key442, -1), (key260, -1), (key397, -1), (key406, -2), (key236, -2), (key406, -2), (key316, 1), (key435, 1), (key248, 1), (key435, 1), (key248, 1), (key316, 1)]

def rawRow4237 : Integer.Sparse Key := [(key475, -1), (key467, -1), (key475, -1), (key267, -1), (key467, -1), (key267, -1), (key469, 2), (key469, 2), (key271, 2), (key418, 1), (key409, 1), (key418, 1), (key239, 1), (key409, 1), (key239, 1), (key442, -1), (key397, -1), (key442, -1), (key260, -1), (key397, -1), (key260, -1), (key406, -2), (key406, -2), (key236, -2), (key435, 1), (key316, 1), (key435, 1), (key248, 1), (key316, 1), (key248, 1)]

def rawRow4244 : Integer.Sparse Key := [(key2642, -2), (key2729, -2), (key2883, -2), (key2632, 1), (key2640, 1), (key2706, 1), (key2860, 1), (key2726, 1), (key2870, 1), (key2654, 2), (key2748, 2), (key2913, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2649, -1), (key2654, -1), (key2738, -1), (key2898, -1), (key2748, -1), (key2905, -1), (key2619, 1), (key2642, 1), (key2674, 1), (key2796, 1), (key2729, 1), (key2832, 1)]

def rawRow4245 : Integer.Sparse Key := [(key2642, -2), (key2883, -2), (key2729, -2), (key2640, 1), (key2632, 1), (key2860, 1), (key2706, 1), (key2870, 1), (key2726, 1), (key2654, 2), (key2913, 2), (key2748, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2654, -1), (key2649, -1), (key2898, -1), (key2738, -1), (key2905, -1), (key2748, -1), (key2642, 1), (key2619, 1), (key2796, 1), (key2674, 1), (key2832, 1), (key2729, 1)]

def rawRow4246 : Integer.Sparse Key := [(key2729, -2), (key2642, -2), (key2883, -2), (key2706, 1), (key2726, 1), (key2632, 1), (key2870, 1), (key2640, 1), (key2860, 1), (key2748, 2), (key2654, 2), (key2913, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2738, -1), (key2748, -1), (key2649, -1), (key2905, -1), (key2654, -1), (key2898, -1), (key2674, 1), (key2729, 1), (key2619, 1), (key2832, 1), (key2642, 1), (key2796, 1)]

def rawRow4247 : Integer.Sparse Key := [(key2729, -2), (key2883, -2), (key2642, -2), (key2726, 1), (key2706, 1), (key2870, 1), (key2632, 1), (key2860, 1), (key2640, 1), (key2748, 2), (key2913, 2), (key2654, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2748, -1), (key2738, -1), (key2905, -1), (key2649, -1), (key2898, -1), (key2654, -1), (key2729, 1), (key2674, 1), (key2832, 1), (key2619, 1), (key2796, 1), (key2642, 1)]

def rawRow4248 : Integer.Sparse Key := [(key2883, -2), (key2642, -2), (key2729, -2), (key2860, 1), (key2870, 1), (key2640, 1), (key2726, 1), (key2632, 1), (key2706, 1), (key2913, 2), (key2654, 2), (key2748, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2898, -1), (key2905, -1), (key2654, -1), (key2748, -1), (key2649, -1), (key2738, -1), (key2796, 1), (key2832, 1), (key2642, 1), (key2729, 1), (key2619, 1), (key2674, 1)]

def rawRow4249 : Integer.Sparse Key := [(key2883, -2), (key2729, -2), (key2642, -2), (key2870, 1), (key2860, 1), (key2726, 1), (key2640, 1), (key2706, 1), (key2632, 1), (key2913, 2), (key2748, 2), (key2654, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2905, -1), (key2898, -1), (key2748, -1), (key2654, -1), (key2738, -1), (key2649, -1), (key2832, 1), (key2796, 1), (key2729, 1), (key2642, 1), (key2674, 1), (key2619, 1)]

def rawRow4250 : Integer.Sparse Key := [(key2654, -2), (key2748, -2), (key2913, -2), (key2649, 1), (key2654, 1), (key2738, 1), (key2898, 1), (key2748, 1), (key2905, 1), (key2642, 2), (key2729, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2796, -1), (key2729, -1), (key2832, -1), (key2632, -1), (key2640, -1), (key2706, -1), (key2860, -1), (key2726, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow4251 : Integer.Sparse Key := [(key2654, -2), (key2913, -2), (key2748, -2), (key2654, 1), (key2649, 1), (key2898, 1), (key2738, 1), (key2905, 1), (key2748, 1), (key2642, 2), (key2883, 2), (key2729, 2), (key2642, -1), (key2619, -1), (key2796, -1), (key2674, -1), (key2832, -1), (key2729, -1), (key2640, -1), (key2632, -1), (key2860, -1), (key2706, -1), (key2870, -1), (key2726, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow4252 : Integer.Sparse Key := [(key2748, -2), (key2654, -2), (key2913, -2), (key2738, 1), (key2748, 1), (key2649, 1), (key2905, 1), (key2654, 1), (key2898, 1), (key2729, 2), (key2642, 2), (key2883, 2), (key2674, -1), (key2729, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2706, -1), (key2726, -1), (key2632, -1), (key2870, -1), (key2640, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow4253 : Integer.Sparse Key := [(key2748, -2), (key2913, -2), (key2654, -2), (key2748, 1), (key2738, 1), (key2905, 1), (key2649, 1), (key2898, 1), (key2654, 1), (key2729, 2), (key2883, 2), (key2642, 2), (key2729, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2796, -1), (key2642, -1), (key2726, -1), (key2706, -1), (key2870, -1), (key2632, -1), (key2860, -1), (key2640, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow4254 : Integer.Sparse Key := [(key2913, -2), (key2654, -2), (key2748, -2), (key2898, 1), (key2905, 1), (key2654, 1), (key2748, 1), (key2649, 1), (key2738, 1), (key2883, 2), (key2642, 2), (key2729, 2), (key2796, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2619, -1), (key2674, -1), (key2860, -1), (key2870, -1), (key2640, -1), (key2726, -1), (key2632, -1), (key2706, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow4255 : Integer.Sparse Key := [(key2913, -2), (key2748, -2), (key2654, -2), (key2905, 1), (key2898, 1), (key2748, 1), (key2654, 1), (key2738, 1), (key2649, 1), (key2883, 2), (key2729, 2), (key2642, 2), (key2832, -1), (key2796, -1), (key2729, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, -1), (key2860, -1), (key2726, -1), (key2640, -1), (key2706, -1), (key2632, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow4268 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2973, 2), (key2975, 2), (key2982, 2), (key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2937, -1), (key2942, -1), (key2949, -1), (key2975, -1), (key2959, -1), (key2982, -1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1)]

def rawRow4269 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2975, 2), (key2973, 2), (key2982, 2), (key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2942, -1), (key2937, -1), (key2975, -1), (key2949, -1), (key2982, -1), (key2959, -1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1)]

def rawRow4270 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2973, 2), (key2982, 2), (key2975, 2), (key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2949, -1), (key2959, -1), (key2937, -1), (key2982, -1), (key2942, -1), (key2975, -1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1)]

def rawRow4271 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2982, 2), (key2973, 2), (key2975, 2), (key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2959, -1), (key2949, -1), (key2982, -1), (key2937, -1), (key2975, -1), (key2942, -1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1)]

def rawRow4272 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2975, 2), (key2982, 2), (key2973, 2), (key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2975, -1), (key2982, -1), (key2942, -1), (key2959, -1), (key2937, -1), (key2949, -1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1)]

def rawRow4273 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2982, 2), (key2975, 2), (key2973, 2), (key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2982, -1), (key2975, -1), (key2959, -1), (key2942, -1), (key2949, -1), (key2937, -1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1)]

def rawRow4274 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2894, 2), (key2896, 2), (key2903, 2), (key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2783, -1), (key2791, -1), (key2806, -1), (key2857, -1), (key2826, -1), (key2867, -1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1)]

def rawRow4275 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2896, 2), (key2894, 2), (key2903, 2), (key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2791, -1), (key2783, -1), (key2857, -1), (key2806, -1), (key2867, -1), (key2826, -1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1)]

def rawRow4276 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2894, 2), (key2903, 2), (key2896, 2), (key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2806, -1), (key2826, -1), (key2783, -1), (key2867, -1), (key2791, -1), (key2857, -1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1)]

def rawRow4277 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2903, 2), (key2894, 2), (key2896, 2), (key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2826, -1), (key2806, -1), (key2867, -1), (key2783, -1), (key2857, -1), (key2791, -1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1)]

def rawRow4278 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 2), (key2903, 2), (key2894, 2), (key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2857, -1), (key2867, -1), (key2791, -1), (key2826, -1), (key2783, -1), (key2806, -1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1)]

def rawRow4279 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 2), (key2896, 2), (key2894, 2), (key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2867, -1), (key2857, -1), (key2826, -1), (key2791, -1), (key2806, -1), (key2783, -1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1)]

def rawRow4304 : Integer.Sparse Key := [(key1317, -1), (key1325, -1), (key1425, -1), (key1623, -1), (key1443, -1), (key1632, -1), (key1312, 2), (key1420, 2), (key1618, 2), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1), (key1292, -1), (key1312, -1), (key1387, -1), (key1542, -1), (key1420, -1), (key1569, -1), (key1338, -2), (key1456, -2), (key1656, -2), (key1297, 1), (key1317, 1), (key1392, 1), (key1547, 1), (key1425, 1), (key1574, 1)]

def rawRow4305 : Integer.Sparse Key := [(key1325, -1), (key1317, -1), (key1623, -1), (key1425, -1), (key1632, -1), (key1443, -1), (key1312, 2), (key1618, 2), (key1420, 2), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1), (key1312, -1), (key1292, -1), (key1542, -1), (key1387, -1), (key1569, -1), (key1420, -1), (key1338, -2), (key1656, -2), (key1456, -2), (key1317, 1), (key1297, 1), (key1547, 1), (key1392, 1), (key1574, 1), (key1425, 1)]

def rawRow4306 : Integer.Sparse Key := [(key1425, -1), (key1443, -1), (key1317, -1), (key1632, -1), (key1325, -1), (key1623, -1), (key1420, 2), (key1312, 2), (key1618, 2), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1), (key1387, -1), (key1420, -1), (key1292, -1), (key1569, -1), (key1312, -1), (key1542, -1), (key1456, -2), (key1338, -2), (key1656, -2), (key1392, 1), (key1425, 1), (key1297, 1), (key1574, 1), (key1317, 1), (key1547, 1)]

def rawRow4307 : Integer.Sparse Key := [(key1443, -1), (key1425, -1), (key1632, -1), (key1317, -1), (key1623, -1), (key1325, -1), (key1420, 2), (key1618, 2), (key1312, 2), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1), (key1420, -1), (key1387, -1), (key1569, -1), (key1292, -1), (key1542, -1), (key1312, -1), (key1456, -2), (key1656, -2), (key1338, -2), (key1425, 1), (key1392, 1), (key1574, 1), (key1297, 1), (key1547, 1), (key1317, 1)]

def rawRow4308 : Integer.Sparse Key := [(key1623, -1), (key1632, -1), (key1325, -1), (key1443, -1), (key1317, -1), (key1425, -1), (key1618, 2), (key1312, 2), (key1420, 2), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1), (key1542, -1), (key1569, -1), (key1312, -1), (key1420, -1), (key1292, -1), (key1387, -1), (key1656, -2), (key1338, -2), (key1456, -2), (key1547, 1), (key1574, 1), (key1317, 1), (key1425, 1), (key1297, 1), (key1392, 1)]

def rawRow4309 : Integer.Sparse Key := [(key1632, -1), (key1623, -1), (key1443, -1), (key1325, -1), (key1425, -1), (key1317, -1), (key1618, 2), (key1420, 2), (key1312, 2), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1), (key1569, -1), (key1542, -1), (key1420, -1), (key1312, -1), (key1387, -1), (key1292, -1), (key1656, -2), (key1456, -2), (key1338, -2), (key1574, 1), (key1547, 1), (key1425, 1), (key1317, 1), (key1392, 1), (key1297, 1)]

def rawRow4310 : Integer.Sparse Key := [(key1338, -1), (key1344, -1), (key1456, -1), (key1658, -1), (key1465, -1), (key1666, -1), (key1338, 2), (key1456, 2), (key1656, 2), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1), (key1297, -1), (key1317, -1), (key1392, -1), (key1547, -1), (key1425, -1), (key1574, -1), (key1312, -2), (key1420, -2), (key1618, -2), (key1292, 1), (key1312, 1), (key1387, 1), (key1542, 1), (key1420, 1), (key1569, 1)]

def rawRow4311 : Integer.Sparse Key := [(key1344, -1), (key1338, -1), (key1658, -1), (key1456, -1), (key1666, -1), (key1465, -1), (key1338, 2), (key1656, 2), (key1456, 2), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1), (key1317, -1), (key1297, -1), (key1547, -1), (key1392, -1), (key1574, -1), (key1425, -1), (key1312, -2), (key1618, -2), (key1420, -2), (key1312, 1), (key1292, 1), (key1542, 1), (key1387, 1), (key1569, 1), (key1420, 1)]

def rawRow4312 : Integer.Sparse Key := [(key1456, -1), (key1465, -1), (key1338, -1), (key1666, -1), (key1344, -1), (key1658, -1), (key1456, 2), (key1338, 2), (key1656, 2), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1), (key1392, -1), (key1425, -1), (key1297, -1), (key1574, -1), (key1317, -1), (key1547, -1), (key1420, -2), (key1312, -2), (key1618, -2), (key1387, 1), (key1420, 1), (key1292, 1), (key1569, 1), (key1312, 1), (key1542, 1)]

def rawRow4313 : Integer.Sparse Key := [(key1465, -1), (key1456, -1), (key1666, -1), (key1338, -1), (key1658, -1), (key1344, -1), (key1456, 2), (key1656, 2), (key1338, 2), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1), (key1425, -1), (key1392, -1), (key1574, -1), (key1297, -1), (key1547, -1), (key1317, -1), (key1420, -2), (key1618, -2), (key1312, -2), (key1420, 1), (key1387, 1), (key1569, 1), (key1292, 1), (key1542, 1), (key1312, 1)]

def rawRow4314 : Integer.Sparse Key := [(key1658, -1), (key1666, -1), (key1344, -1), (key1465, -1), (key1338, -1), (key1456, -1), (key1656, 2), (key1338, 2), (key1456, 2), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1), (key1547, -1), (key1574, -1), (key1317, -1), (key1425, -1), (key1297, -1), (key1392, -1), (key1618, -2), (key1312, -2), (key1420, -2), (key1542, 1), (key1569, 1), (key1312, 1), (key1420, 1), (key1292, 1), (key1387, 1)]

def rawRow4315 : Integer.Sparse Key := [(key1666, -1), (key1658, -1), (key1465, -1), (key1344, -1), (key1456, -1), (key1338, -1), (key1656, 2), (key1456, 2), (key1338, 2), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1), (key1574, -1), (key1547, -1), (key1425, -1), (key1317, -1), (key1392, -1), (key1297, -1), (key1618, -2), (key1420, -2), (key1312, -2), (key1569, 1), (key1542, 1), (key1420, 1), (key1312, 1), (key1387, 1), (key1292, 1)]

def rawRow4328 : Integer.Sparse Key := [(key1656, -2), (key1658, -2), (key1666, -2), (key1547, 1), (key1555, 1), (key1574, 1), (key1623, 1), (key1592, 1), (key1632, 1), (key1814, 2), (key1816, 2), (key1824, 2), (key1317, -1), (key1325, -1), (key1425, -1), (key1623, -1), (key1443, -1), (key1632, -1), (key1773, -1), (key1779, -1), (key1789, -1), (key1816, -1), (key1797, -1), (key1824, -1), (key1338, 1), (key1344, 1), (key1456, 1), (key1658, 1), (key1465, 1), (key1666, 1)]

def rawRow4329 : Integer.Sparse Key := [(key1658, -2), (key1656, -2), (key1666, -2), (key1555, 1), (key1547, 1), (key1623, 1), (key1574, 1), (key1632, 1), (key1592, 1), (key1816, 2), (key1814, 2), (key1824, 2), (key1325, -1), (key1317, -1), (key1623, -1), (key1425, -1), (key1632, -1), (key1443, -1), (key1779, -1), (key1773, -1), (key1816, -1), (key1789, -1), (key1824, -1), (key1797, -1), (key1344, 1), (key1338, 1), (key1658, 1), (key1456, 1), (key1666, 1), (key1465, 1)]

def rawRow4330 : Integer.Sparse Key := [(key1656, -2), (key1666, -2), (key1658, -2), (key1574, 1), (key1592, 1), (key1547, 1), (key1632, 1), (key1555, 1), (key1623, 1), (key1814, 2), (key1824, 2), (key1816, 2), (key1425, -1), (key1443, -1), (key1317, -1), (key1632, -1), (key1325, -1), (key1623, -1), (key1789, -1), (key1797, -1), (key1773, -1), (key1824, -1), (key1779, -1), (key1816, -1), (key1456, 1), (key1465, 1), (key1338, 1), (key1666, 1), (key1344, 1), (key1658, 1)]

def rawRow4331 : Integer.Sparse Key := [(key1666, -2), (key1656, -2), (key1658, -2), (key1592, 1), (key1574, 1), (key1632, 1), (key1547, 1), (key1623, 1), (key1555, 1), (key1824, 2), (key1814, 2), (key1816, 2), (key1443, -1), (key1425, -1), (key1632, -1), (key1317, -1), (key1623, -1), (key1325, -1), (key1797, -1), (key1789, -1), (key1824, -1), (key1773, -1), (key1816, -1), (key1779, -1), (key1465, 1), (key1456, 1), (key1666, 1), (key1338, 1), (key1658, 1), (key1344, 1)]

def rawRow4332 : Integer.Sparse Key := [(key1658, -2), (key1666, -2), (key1656, -2), (key1623, 1), (key1632, 1), (key1555, 1), (key1592, 1), (key1547, 1), (key1574, 1), (key1816, 2), (key1824, 2), (key1814, 2), (key1623, -1), (key1632, -1), (key1325, -1), (key1443, -1), (key1317, -1), (key1425, -1), (key1816, -1), (key1824, -1), (key1779, -1), (key1797, -1), (key1773, -1), (key1789, -1), (key1658, 1), (key1666, 1), (key1344, 1), (key1465, 1), (key1338, 1), (key1456, 1)]

def rawRow4333 : Integer.Sparse Key := [(key1666, -2), (key1658, -2), (key1656, -2), (key1632, 1), (key1623, 1), (key1592, 1), (key1555, 1), (key1574, 1), (key1547, 1), (key1824, 2), (key1816, 2), (key1814, 2), (key1632, -1), (key1623, -1), (key1443, -1), (key1325, -1), (key1425, -1), (key1317, -1), (key1824, -1), (key1816, -1), (key1797, -1), (key1779, -1), (key1789, -1), (key1773, -1), (key1666, 1), (key1658, 1), (key1465, 1), (key1344, 1), (key1456, 1), (key1338, 1)]

def rawRow4334 : Integer.Sparse Key := [(key1814, -2), (key1816, -2), (key1824, -2), (key1773, 1), (key1779, 1), (key1789, 1), (key1816, 1), (key1797, 1), (key1824, 1), (key1656, 2), (key1658, 2), (key1666, 2), (key1338, -1), (key1344, -1), (key1456, -1), (key1658, -1), (key1465, -1), (key1666, -1), (key1547, -1), (key1555, -1), (key1574, -1), (key1623, -1), (key1592, -1), (key1632, -1), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1)]

def rawRow4335 : Integer.Sparse Key := [(key1816, -2), (key1814, -2), (key1824, -2), (key1779, 1), (key1773, 1), (key1816, 1), (key1789, 1), (key1824, 1), (key1797, 1), (key1658, 2), (key1656, 2), (key1666, 2), (key1344, -1), (key1338, -1), (key1658, -1), (key1456, -1), (key1666, -1), (key1465, -1), (key1555, -1), (key1547, -1), (key1623, -1), (key1574, -1), (key1632, -1), (key1592, -1), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1)]

def rawRow4336 : Integer.Sparse Key := [(key1814, -2), (key1824, -2), (key1816, -2), (key1789, 1), (key1797, 1), (key1773, 1), (key1824, 1), (key1779, 1), (key1816, 1), (key1656, 2), (key1666, 2), (key1658, 2), (key1456, -1), (key1465, -1), (key1338, -1), (key1666, -1), (key1344, -1), (key1658, -1), (key1574, -1), (key1592, -1), (key1547, -1), (key1632, -1), (key1555, -1), (key1623, -1), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1)]

def rawRow4337 : Integer.Sparse Key := [(key1824, -2), (key1814, -2), (key1816, -2), (key1797, 1), (key1789, 1), (key1824, 1), (key1773, 1), (key1816, 1), (key1779, 1), (key1666, 2), (key1656, 2), (key1658, 2), (key1465, -1), (key1456, -1), (key1666, -1), (key1338, -1), (key1658, -1), (key1344, -1), (key1592, -1), (key1574, -1), (key1632, -1), (key1547, -1), (key1623, -1), (key1555, -1), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1)]

def rawRow4338 : Integer.Sparse Key := [(key1816, -2), (key1824, -2), (key1814, -2), (key1816, 1), (key1824, 1), (key1779, 1), (key1797, 1), (key1773, 1), (key1789, 1), (key1658, 2), (key1666, 2), (key1656, 2), (key1658, -1), (key1666, -1), (key1344, -1), (key1465, -1), (key1338, -1), (key1456, -1), (key1623, -1), (key1632, -1), (key1555, -1), (key1592, -1), (key1547, -1), (key1574, -1), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1)]

def rawRow4339 : Integer.Sparse Key := [(key1824, -2), (key1816, -2), (key1814, -2), (key1824, 1), (key1816, 1), (key1797, 1), (key1779, 1), (key1789, 1), (key1773, 1), (key1666, 2), (key1658, 2), (key1656, 2), (key1666, -1), (key1658, -1), (key1465, -1), (key1344, -1), (key1456, -1), (key1338, -1), (key1632, -1), (key1623, -1), (key1592, -1), (key1555, -1), (key1574, -1), (key1547, -1), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1)]

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

def rawRow4352 : Integer.Sparse Key := [(key2796, -2), (key2832, -2), (key2883, -2), (key2786, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2829, 1), (key2870, 1), (key2944, 2), (key2961, 2), (key2992, 2), (key2616, -1), (key2640, -1), (key2671, -1), (key2794, -1), (key2726, -1), (key2829, -1), (key2939, -1), (key2944, -1), (key2951, -1), (key2977, -1), (key2961, -1), (key2984, -1), (key2619, 1), (key2642, 1), (key2674, 1), (key2796, 1), (key2729, 1), (key2832, 1)]

def rawRow4353 : Integer.Sparse Key := [(key2796, -2), (key2883, -2), (key2832, -2), (key2794, 1), (key2786, 1), (key2860, 1), (key2809, 1), (key2870, 1), (key2829, 1), (key2944, 2), (key2992, 2), (key2961, 2), (key2640, -1), (key2616, -1), (key2794, -1), (key2671, -1), (key2829, -1), (key2726, -1), (key2944, -1), (key2939, -1), (key2977, -1), (key2951, -1), (key2984, -1), (key2961, -1), (key2642, 1), (key2619, 1), (key2796, 1), (key2674, 1), (key2832, 1), (key2729, 1)]

def rawRow4354 : Integer.Sparse Key := [(key2832, -2), (key2796, -2), (key2883, -2), (key2809, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2794, 1), (key2860, 1), (key2961, 2), (key2944, 2), (key2992, 2), (key2671, -1), (key2726, -1), (key2616, -1), (key2829, -1), (key2640, -1), (key2794, -1), (key2951, -1), (key2961, -1), (key2939, -1), (key2984, -1), (key2944, -1), (key2977, -1), (key2674, 1), (key2729, 1), (key2619, 1), (key2832, 1), (key2642, 1), (key2796, 1)]

def rawRow4355 : Integer.Sparse Key := [(key2832, -2), (key2883, -2), (key2796, -2), (key2829, 1), (key2809, 1), (key2870, 1), (key2786, 1), (key2860, 1), (key2794, 1), (key2961, 2), (key2992, 2), (key2944, 2), (key2726, -1), (key2671, -1), (key2829, -1), (key2616, -1), (key2794, -1), (key2640, -1), (key2961, -1), (key2951, -1), (key2984, -1), (key2939, -1), (key2977, -1), (key2944, -1), (key2729, 1), (key2674, 1), (key2832, 1), (key2619, 1), (key2796, 1), (key2642, 1)]

def rawRow4356 : Integer.Sparse Key := [(key2883, -2), (key2796, -2), (key2832, -2), (key2860, 1), (key2870, 1), (key2794, 1), (key2829, 1), (key2786, 1), (key2809, 1), (key2992, 2), (key2944, 2), (key2961, 2), (key2794, -1), (key2829, -1), (key2640, -1), (key2726, -1), (key2616, -1), (key2671, -1), (key2977, -1), (key2984, -1), (key2944, -1), (key2961, -1), (key2939, -1), (key2951, -1), (key2796, 1), (key2832, 1), (key2642, 1), (key2729, 1), (key2619, 1), (key2674, 1)]

def rawRow4357 : Integer.Sparse Key := [(key2883, -2), (key2832, -2), (key2796, -2), (key2870, 1), (key2860, 1), (key2829, 1), (key2794, 1), (key2809, 1), (key2786, 1), (key2992, 2), (key2961, 2), (key2944, 2), (key2829, -1), (key2794, -1), (key2726, -1), (key2640, -1), (key2671, -1), (key2616, -1), (key2984, -1), (key2977, -1), (key2961, -1), (key2944, -1), (key2951, -1), (key2939, -1), (key2832, 1), (key2796, 1), (key2729, 1), (key2642, 1), (key2674, 1), (key2619, 1)]

def rawRow4358 : Integer.Sparse Key := [(key2944, -2), (key2961, -2), (key2992, -2), (key2939, 1), (key2944, 1), (key2951, 1), (key2977, 1), (key2961, 1), (key2984, 1), (key2796, 2), (key2832, 2), (key2883, 2), (key2619, -1), (key2642, -1), (key2674, -1), (key2796, -1), (key2729, -1), (key2832, -1), (key2786, -1), (key2794, -1), (key2809, -1), (key2860, -1), (key2829, -1), (key2870, -1), (key2616, 1), (key2640, 1), (key2671, 1), (key2794, 1), (key2726, 1), (key2829, 1)]

def rawRow4359 : Integer.Sparse Key := [(key2944, -2), (key2992, -2), (key2961, -2), (key2944, 1), (key2939, 1), (key2977, 1), (key2951, 1), (key2984, 1), (key2961, 1), (key2796, 2), (key2883, 2), (key2832, 2), (key2642, -1), (key2619, -1), (key2796, -1), (key2674, -1), (key2832, -1), (key2729, -1), (key2794, -1), (key2786, -1), (key2860, -1), (key2809, -1), (key2870, -1), (key2829, -1), (key2640, 1), (key2616, 1), (key2794, 1), (key2671, 1), (key2829, 1), (key2726, 1)]

def rawRow4360 : Integer.Sparse Key := [(key2961, -2), (key2944, -2), (key2992, -2), (key2951, 1), (key2961, 1), (key2939, 1), (key2984, 1), (key2944, 1), (key2977, 1), (key2832, 2), (key2796, 2), (key2883, 2), (key2674, -1), (key2729, -1), (key2619, -1), (key2832, -1), (key2642, -1), (key2796, -1), (key2809, -1), (key2829, -1), (key2786, -1), (key2870, -1), (key2794, -1), (key2860, -1), (key2671, 1), (key2726, 1), (key2616, 1), (key2829, 1), (key2640, 1), (key2794, 1)]

def rawRow4361 : Integer.Sparse Key := [(key2961, -2), (key2992, -2), (key2944, -2), (key2961, 1), (key2951, 1), (key2984, 1), (key2939, 1), (key2977, 1), (key2944, 1), (key2832, 2), (key2883, 2), (key2796, 2), (key2729, -1), (key2674, -1), (key2832, -1), (key2619, -1), (key2796, -1), (key2642, -1), (key2829, -1), (key2809, -1), (key2870, -1), (key2786, -1), (key2860, -1), (key2794, -1), (key2726, 1), (key2671, 1), (key2829, 1), (key2616, 1), (key2794, 1), (key2640, 1)]

def rawRow4362 : Integer.Sparse Key := [(key2992, -2), (key2944, -2), (key2961, -2), (key2977, 1), (key2984, 1), (key2944, 1), (key2961, 1), (key2939, 1), (key2951, 1), (key2883, 2), (key2796, 2), (key2832, 2), (key2796, -1), (key2832, -1), (key2642, -1), (key2729, -1), (key2619, -1), (key2674, -1), (key2860, -1), (key2870, -1), (key2794, -1), (key2829, -1), (key2786, -1), (key2809, -1), (key2794, 1), (key2829, 1), (key2640, 1), (key2726, 1), (key2616, 1), (key2671, 1)]

def rawRow4363 : Integer.Sparse Key := [(key2992, -2), (key2961, -2), (key2944, -2), (key2984, 1), (key2977, 1), (key2961, 1), (key2944, 1), (key2951, 1), (key2939, 1), (key2883, 2), (key2832, 2), (key2796, 2), (key2832, -1), (key2796, -1), (key2729, -1), (key2642, -1), (key2674, -1), (key2619, -1), (key2870, -1), (key2860, -1), (key2829, -1), (key2794, -1), (key2809, -1), (key2786, -1), (key2829, 1), (key2794, 1), (key2726, 1), (key2640, 1), (key2671, 1), (key2616, 1)]

def rawRow4388 : Integer.Sparse Key := [(key2892, -2), (key2895, -2), (key2902, -2), (key2781, 1), (key2790, 1), (key2804, 1), (key2856, 1), (key2825, 1), (key2866, 1), (key2971, 2), (key2974, 2), (key2981, 2), (key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2935, -1), (key2941, -1), (key2947, -1), (key2974, -1), (key2958, -1), (key2981, -1), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1)]

def rawRow4389 : Integer.Sparse Key := [(key2895, -2), (key2892, -2), (key2902, -2), (key2790, 1), (key2781, 1), (key2856, 1), (key2804, 1), (key2866, 1), (key2825, 1), (key2974, 2), (key2971, 2), (key2981, 2), (key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2941, -1), (key2935, -1), (key2974, -1), (key2947, -1), (key2981, -1), (key2958, -1), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1)]

def rawRow4390 : Integer.Sparse Key := [(key2892, -2), (key2902, -2), (key2895, -2), (key2804, 1), (key2825, 1), (key2781, 1), (key2866, 1), (key2790, 1), (key2856, 1), (key2971, 2), (key2981, 2), (key2974, 2), (key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2947, -1), (key2958, -1), (key2935, -1), (key2981, -1), (key2941, -1), (key2974, -1), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1)]

def rawRow4391 : Integer.Sparse Key := [(key2902, -2), (key2892, -2), (key2895, -2), (key2825, 1), (key2804, 1), (key2866, 1), (key2781, 1), (key2856, 1), (key2790, 1), (key2981, 2), (key2971, 2), (key2974, 2), (key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2958, -1), (key2947, -1), (key2981, -1), (key2935, -1), (key2974, -1), (key2941, -1), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1)]

def rawRow4392 : Integer.Sparse Key := [(key2895, -2), (key2902, -2), (key2892, -2), (key2856, 1), (key2866, 1), (key2790, 1), (key2825, 1), (key2781, 1), (key2804, 1), (key2974, 2), (key2981, 2), (key2971, 2), (key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2974, -1), (key2981, -1), (key2941, -1), (key2958, -1), (key2935, -1), (key2947, -1), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1)]

def rawRow4393 : Integer.Sparse Key := [(key2902, -2), (key2895, -2), (key2892, -2), (key2866, 1), (key2856, 1), (key2825, 1), (key2790, 1), (key2804, 1), (key2781, 1), (key2981, 2), (key2974, 2), (key2971, 2), (key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2981, -1), (key2974, -1), (key2958, -1), (key2941, -1), (key2947, -1), (key2935, -1), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

def rawRow4394 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2935, 1), (key2941, 1), (key2947, 1), (key2974, 1), (key2958, 1), (key2981, 1), (key2892, 2), (key2895, 2), (key2902, 2), (key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2781, -1), (key2790, -1), (key2804, -1), (key2856, -1), (key2825, -1), (key2866, -1), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1)]

def rawRow4395 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2941, 1), (key2935, 1), (key2974, 1), (key2947, 1), (key2981, 1), (key2958, 1), (key2895, 2), (key2892, 2), (key2902, 2), (key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2790, -1), (key2781, -1), (key2856, -1), (key2804, -1), (key2866, -1), (key2825, -1), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1)]

def rawRow4396 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2947, 1), (key2958, 1), (key2935, 1), (key2981, 1), (key2941, 1), (key2974, 1), (key2892, 2), (key2902, 2), (key2895, 2), (key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2804, -1), (key2825, -1), (key2781, -1), (key2866, -1), (key2790, -1), (key2856, -1), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1)]

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

def rawRow339 : Integer.Sparse Key := [(key1320, -1), (key1320, -1), (key1353, 2), (key1300, 1), (key1300, 1), (key1356, -1), (key1356, -1), (key1306, -2), (key1333, 1), (key1333, 1), (key1428, 1), (key1428, 1), (key1474, -2), (key1395, -1), (key1395, -1), (key1482, 1), (key1482, 1), (key1401, 2), (key1451, -1), (key1451, -1), (key1577, -1), (key1577, -1), (key1685, 1), (key1685, 1), (key1550, 1), (key1550, 1), (key1691, -1), (key1691, -1), (key1563, -1), (key1563, -1), (key1600, 1), (key1600, 1), (key1905, 2), (key1922, -1), (key1922, -1), (key1898, -2), (key1928, 1), (key1928, 1), (key1901, 1), (key1901, 1), (key1913, -1), (key1913, -1)]

def rawRow346 : Integer.Sparse Key := [(key1395, -1), (key1395, -1), (key1401, 2), (key1550, 1), (key1550, 1), (key1563, -1), (key1563, -1), (key1898, -2), (key1901, 1), (key1901, 1), (key1300, 1), (key1300, 1), (key1306, -2), (key1577, -1), (key1577, -1), (key1600, 1), (key1600, 1), (key1905, 2), (key1913, -1), (key1913, -1), (key1320, -1), (key1320, -1), (key1333, 1), (key1333, 1), (key1428, 1), (key1428, 1), (key1451, -1), (key1451, -1), (key1922, -1), (key1922, -1), (key1928, 1), (key1928, 1), (key1353, 2), (key1356, -1), (key1356, -1), (key1474, -2), (key1482, 1), (key1482, 1), (key1685, 1), (key1685, 1), (key1691, -1), (key1691, -1)]

def rawRow349 : Integer.Sparse Key := [(key1550, -1), (key1550, -1), (key1898, 2), (key1395, 1), (key1395, 1), (key1901, -1), (key1901, -1), (key1401, -2), (key1563, 1), (key1563, 1), (key1577, 1), (key1577, 1), (key1905, -2), (key1300, -1), (key1300, -1), (key1913, 1), (key1913, 1), (key1306, 2), (key1600, -1), (key1600, -1), (key1428, -1), (key1428, -1), (key1922, 1), (key1922, 1), (key1320, 1), (key1320, 1), (key1928, -1), (key1928, -1), (key1333, -1), (key1333, -1), (key1451, 1), (key1451, 1), (key1474, 2), (key1685, -1), (key1685, -1), (key1353, -2), (key1691, 1), (key1691, 1), (key1356, 1), (key1356, 1), (key1482, -1), (key1482, -1)]

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

def rawRow356 : Integer.Sparse Key := [(key1428, -1), (key1428, -1), (key1474, 2), (key1577, 1), (key1577, 1), (key1685, -1), (key1685, -1), (key1905, -2), (key1922, 1), (key1922, 1), (key1320, 1), (key1320, 1), (key1353, -2), (key1550, -1), (key1550, -1), (key1691, 1), (key1691, 1), (key1898, 2), (key1928, -1), (key1928, -1), (key1300, -1), (key1300, -1), (key1356, 1), (key1356, 1), (key1395, 1), (key1395, 1), (key1482, -1), (key1482, -1), (key1901, -1), (key1901, -1), (key1913, 1), (key1913, 1), (key1306, 2), (key1333, -1), (key1333, -1), (key1401, -2), (key1451, 1), (key1451, 1), (key1563, 1), (key1563, 1), (key1600, -1), (key1600, -1)]

def rawRow359 : Integer.Sparse Key := [(key1577, -1), (key1577, -1), (key1905, 2), (key1428, 1), (key1428, 1), (key1922, -1), (key1922, -1), (key1474, -2), (key1685, 1), (key1685, 1), (key1550, 1), (key1550, 1), (key1898, -2), (key1320, -1), (key1320, -1), (key1928, 1), (key1928, 1), (key1353, 2), (key1691, -1), (key1691, -1), (key1395, -1), (key1395, -1), (key1901, 1), (key1901, 1), (key1300, 1), (key1300, 1), (key1913, -1), (key1913, -1), (key1356, -1), (key1356, -1), (key1482, 1), (key1482, 1), (key1401, 2), (key1563, -1), (key1563, -1), (key1306, -2), (key1600, 1), (key1600, 1), (key1333, 1), (key1333, 1), (key1451, -1), (key1451, -1)]

def rawRow378 : Integer.Sparse Key := [(key243, -2), (key245, 1), (key245, 1), (key255, 2), (key266, -1), (key266, -1), (key270, -1), (key270, -1), (key275, 1), (key275, 1), (key309, 2), (key311, -1), (key311, -1), (key323, -2), (key334, 1), (key334, 1), (key338, 1), (key338, 1), (key344, -1), (key344, -1), (key392, -2), (key403, 1), (key403, 1), (key413, 2), (key424, -1), (key424, -1), (key473, -1), (key473, -1), (key479, 1), (key479, 1), (key571, 1), (key571, 1), (key576, -1), (key576, -1), (key581, -1), (key581, -1), (key587, 1), (key587, 1), (key599, 1), (key599, 1), (key605, -1), (key605, -1)]

def rawRow381 : Integer.Sparse Key := [(key255, -2), (key266, 1), (key266, 1), (key243, 2), (key275, -1), (key275, -1), (key245, -1), (key245, -1), (key266, 1), (key266, 1), (key323, 2), (key338, -1), (key338, -1), (key309, -2), (key344, 1), (key344, 1), (key311, 1), (key311, 1), (key334, -1), (key334, -1), (key413, -2), (key473, 1), (key473, 1), (key392, 2), (key479, -1), (key479, -1), (key403, -1), (key403, -1), (key424, 1), (key424, 1), (key581, 1), (key581, 1), (key599, -1), (key599, -1), (key571, -1), (key571, -1), (key605, 1), (key605, 1), (key576, 1), (key576, 1), (key587, -1), (key587, -1)]

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

def rawRow388 : Integer.Sparse Key := [(key309, -2), (key311, 1), (key311, 1), (key323, 2), (key338, -1), (key338, -1), (key334, -1), (key334, -1), (key344, 1), (key344, 1), (key243, 2), (key245, -1), (key245, -1), (key413, -2), (key424, 1), (key424, 1), (key581, 1), (key581, 1), (key587, -1), (key587, -1), (key255, -2), (key266, 1), (key266, 1), (key323, 2), (key334, -1), (key334, -1), (key599, -1), (key599, -1), (key605, 1), (key605, 1), (key270, 1), (key270, 1), (key275, -1), (key275, -1), (key338, -1), (key338, -1), (key344, 1), (key344, 1), (key473, 1), (key473, 1), (key479, -1), (key479, -1)]

def rawRow391 : Integer.Sparse Key := [(key323, -2), (key334, 1), (key334, 1), (key309, 2), (key344, -1), (key344, -1), (key311, -1), (key311, -1), (key338, 1), (key338, 1), (key413, 2), (key424, -1), (key424, -1), (key243, -2), (key587, 1), (key587, 1), (key245, 1), (key245, 1), (key424, -1), (key424, -1), (key323, -2), (key599, 1), (key599, 1), (key255, 2), (key605, -1), (key605, -1), (key266, -1), (key266, -1), (key334, 1), (key334, 1), (key338, 1), (key338, 1), (key473, -1), (key473, -1), (key270, -1), (key270, -1), (key479, 1), (key479, 1), (key275, 1), (key275, 1), (key344, -1), (key344, -1)]

def rawRow398 : Integer.Sparse Key := [(key392, -2), (key403, 1), (key403, 1), (key413, 2), (key473, -1), (key473, -1), (key424, -1), (key424, -1), (key479, 1), (key479, 1), (key255, 2), (key266, -1), (key266, -1), (key323, -2), (key599, 1), (key599, 1), (key334, 1), (key334, 1), (key605, -1), (key605, -1), (key243, -2), (key275, 1), (key275, 1), (key309, 2), (key344, -1), (key344, -1), (key576, -1), (key576, -1), (key587, 1), (key587, 1), (key245, 1), (key245, 1), (key266, -1), (key266, -1), (key311, -1), (key311, -1), (key334, 1), (key334, 1), (key403, 1), (key403, 1), (key424, -1), (key424, -1)]

def rawRow401 : Integer.Sparse Key := [(key413, -2), (key424, 1), (key424, 1), (key392, 2), (key479, -1), (key479, -1), (key403, -1), (key403, -1), (key473, 1), (key473, 1), (key323, 2), (key334, -1), (key334, -1), (key255, -2), (key605, 1), (key605, 1), (key266, 1), (key266, 1), (key599, -1), (key599, -1), (key309, -2), (key344, 1), (key344, 1), (key243, 2), (key587, -1), (key587, -1), (key275, -1), (key275, -1), (key344, 1), (key344, 1), (key311, 1), (key311, 1), (key403, -1), (key403, -1), (key245, -1), (key245, -1), (key424, 1), (key424, 1), (key266, 1), (key266, 1), (key334, -1), (key334, -1)]

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

def row10 : Integer.Sparse (Fin 3237) := [(0, 1), (261, 5), (2571, -30), (2579, -10), (2763, -60), (2766, -30)]

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

def nodeValue1020 : Sparse Master := []

end MUB6.Certificate.MixedSemantics

end OAI
end


