-- Prove2me | Definitions.Def_OAIQ106D102
-- name    : OAIQ106D102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T13:02:35.093542+00:00
-- url     : https://prove2.me/theorems/eaef68b0-eb22-4055-b3da-e4f0b0cc37aa
-- title:
--   Definitions bundle OAIQ106D102 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 478 declarations of OpenAI's Lean: 478 definitions. The definitions and types are `OAI.MUB6.Certificate.GramRows.rawRow4397`, `OAI.MUB6.Certificate.GramRows.rawRow4398`, `OAI.MUB6.Certificate.GramRows.rawRow4399`, `OAI.MUB6.Certificate.GramRows.rawRow4424`, `OAI.MUB6.Certificate.GramRows.rawRow4425`, `OAI.MUB6.Certificate.GramRows.rawRow4426`, `OAI.MUB6.Certificate.GramRows.rawRow4427`, `OAI.MUB6.Certificate.GramRows.rawRow4428`, `OAI.MUB6.Certificate.GramRows.rawRow4429`, `OAI.MUB6.Certificate.GramRows.rawRow4430`, `OAI.MUB6.Certificate.GramRows.rawRow4431`, `OAI.MUB6.Certificate.GramRows.rawRow4432`, `OAI.MUB6.Certificate.GramRows.rawRow4433`, `OAI.MUB6.Certificate.GramRows.rawRow4434`, `OAI.MUB6.Certificate.GramRows.rawRow4435`, `OAI.MUB6.Certificate.GramRows.rawRow4436`, `OAI.MUB6.Certificate.GramRows.rawRow4437`, `OAI.MUB6.Certificate.GramRows.rawRow4438`, `OAI.MUB6.Certificate.GramRows.rawRow4439`, `OAI.MUB6.Certificate.GramRows.rawRow4440`, `OAI.MUB6.Certificate.GramRows.rawRow4441`, `OAI.MUB6.Certificate.GramRows.rawRow4442`, `OAI.MUB6.Certificate.GramRows.rawRow4443`, `OAI.MUB6.Certificate.GramRows.rawRow4444`, `OAI.MUB6.Certificate.GramRows.rawRow4445`, `OAI.MUB6.Certificate.GramRows.rawRow4446`, `OAI.MUB6.Certificate.GramRows.rawRow4447`, `OAI.MUB6.Certificate.GramRows.rawRow4448`, `OAI.MUB6.Certificate.GramRows.rawRow4449`, `OAI.MUB6.Certificate.GramRows.rawRow4450`, `OAI.MUB6.Certificate.GramRows.rawRow4451`, `OAI.MUB6.Certificate.GramRows.rawRow4452`, `OAI.MUB6.Certificate.GramRows.rawRow4453`, `OAI.MUB6.Certificate.GramRows.rawRow4454`, `OAI.MUB6.Certificate.GramRows.rawRow4455`, `OAI.MUB6.Certificate.GramRows.rawRow4456`, `OAI.MUB6.Certificate.GramRows.rawRow4457`, `OAI.MUB6.Certificate.GramRows.rawRow4458`, `OAI.MUB6.Certificate.GramRows.rawRow4459`, `OAI.MUB6.Certificate.GramRows.rawRow4460` and 438 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block11`, `MutuallyUnbiased_GramRows_Block12`, `MutuallyUnbiased_GramRows_Block13`, `MutuallyUnbiased_GramRows_Block18`, `MutuallyUnbiased_GramRows_Block58`, `MutuallyUnbiased_GramRows_Block59`, `MutuallyUnbiased_GramRows_Block60`, `MutuallyUnbiased_GramRows_Block61`, `MutuallyUnbiased_GramRows_Block62`, `MutuallyUnbiased_GramRows_Block63`, `MutuallyUnbiased_GramRows_Block64`, `MutuallyUnbiased_MixedData_Source8`, `MutuallyUnbiased_MixedSemantics_Values18`.
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

def rawRow45 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1329, 2), (key1296, 1), (key1296, 1), (key1345, -1), (key1345, -1), (key1302, -2), (key1339, 1), (key1339, 1), (key1546, 1), (key1546, 1), (key1559, -2), (key1391, -1), (key1391, -1), (key1780, 1), (key1780, 1), (key1397, 2), (key1774, -1), (key1774, -1), (key1573, -1), (key1573, -1), (key1659, 1), (key1659, 1), (key1424, 1), (key1424, 1), (key1817, -1), (key1817, -1), (key1457, -1), (key1457, -1), (key1790, 1), (key1790, 1), (key1596, 2), (key1667, -1), (key1667, -1), (key1447, -2), (key1825, 1), (key1825, 1), (key1466, 1), (key1466, 1), (key1798, -1), (key1798, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow452 : Integer.Sparse Key := [(key1771, -1), (key1771, -1), (key1778, 2), (key1787, 1), (key1787, 1), (key1815, -1), (key1815, -1), (key1796, -2), (key1823, 1), (key1823, 1), (key1336, 1), (key1336, 1), (key1343, -2), (key1454, -1), (key1454, -1), (key1657, 1), (key1657, 1), (key1464, 2), (key1665, -1), (key1665, -1), (key1295, -1), (key1295, -1), (key1324, 1), (key1324, 1), (key1390, 1), (key1390, 1), (key1554, -1), (key1554, -1), (key1442, -1), (key1442, -1), (key1591, 1), (key1591, 1), (key1291, 2), (key1311, -1), (key1311, -1), (key1386, -2), (key1541, 1), (key1541, 1), (key1419, 1), (key1419, 1), (key1568, -1), (key1568, -1)]

def rawRow455 : Integer.Sparse Key := [(key1787, -1), (key1787, -1), (key1796, 2), (key1771, 1), (key1771, 1), (key1823, -1), (key1823, -1), (key1778, -2), (key1815, 1), (key1815, 1), (key1454, 1), (key1454, 1), (key1464, -2), (key1336, -1), (key1336, -1), (key1665, 1), (key1665, 1), (key1343, 2), (key1657, -1), (key1657, -1), (key1390, -1), (key1390, -1), (key1442, 1), (key1442, 1), (key1295, 1), (key1295, 1), (key1591, -1), (key1591, -1), (key1324, -1), (key1324, -1), (key1554, 1), (key1554, 1), (key1386, 2), (key1419, -1), (key1419, -1), (key1291, -2), (key1568, 1), (key1568, 1), (key1311, 1), (key1311, 1), (key1541, -1), (key1541, -1)]

def rawRow462 : Integer.Sparse Key := [(key2616, -2), (key2616, 1), (key2619, 1), (key2632, 2), (key2632, -1), (key2649, -1), (key2640, -1), (key2642, -1), (key2640, 1), (key2654, 1), (key2671, 2), (key2671, -1), (key2674, -1), (key2786, -2), (key2786, 1), (key2939, 1), (key2794, 1), (key2796, 1), (key2794, -1), (key2944, -1), (key2706, -2), (key2706, 1), (key2738, 1), (key2809, 2), (key2809, -1), (key2951, -1), (key2860, -1), (key2898, -1), (key2860, 1), (key2977, 1), (key2726, 1), (key2729, 1), (key2726, -1), (key2748, -1), (key2829, -1), (key2832, -1), (key2829, 1), (key2961, 1), (key2870, 1), (key2905, 1), (key2870, -1), (key2984, -1)]

def rawRow463 : Integer.Sparse Key := [(key2616, -2), (key2619, 1), (key2616, 1), (key2632, 2), (key2649, -1), (key2632, -1), (key2642, -1), (key2640, -1), (key2654, 1), (key2640, 1), (key2671, 2), (key2674, -1), (key2671, -1), (key2786, -2), (key2939, 1), (key2786, 1), (key2796, 1), (key2794, 1), (key2944, -1), (key2794, -1), (key2706, -2), (key2738, 1), (key2706, 1), (key2809, 2), (key2951, -1), (key2809, -1), (key2898, -1), (key2860, -1), (key2977, 1), (key2860, 1), (key2729, 1), (key2726, 1), (key2748, -1), (key2726, -1), (key2832, -1), (key2829, -1), (key2961, 1), (key2829, 1), (key2905, 1), (key2870, 1), (key2984, -1), (key2870, -1)]

def rawRow464 : Integer.Sparse Key := [(key2619, -2), (key2616, 1), (key2616, 1), (key2649, 2), (key2632, -1), (key2632, -1), (key2654, -1), (key2654, -1), (key2642, 1), (key2642, 1), (key2674, 2), (key2671, -1), (key2671, -1), (key2939, -2), (key2786, 1), (key2786, 1), (key2944, 1), (key2944, 1), (key2796, -1), (key2796, -1), (key2738, -2), (key2706, 1), (key2706, 1), (key2951, 2), (key2809, -1), (key2809, -1), (key2977, -1), (key2977, -1), (key2898, 1), (key2898, 1), (key2748, 1), (key2748, 1), (key2729, -1), (key2729, -1), (key2961, -1), (key2961, -1), (key2832, 1), (key2832, 1), (key2984, 1), (key2984, 1), (key2905, -1), (key2905, -1)]

def rawRow465 : Integer.Sparse Key := [(key2632, -2), (key2640, 1), (key2642, 1), (key2616, 2), (key2640, -1), (key2654, -1), (key2616, -1), (key2619, -1), (key2632, 1), (key2649, 1), (key2786, 2), (key2794, -1), (key2796, -1), (key2671, -2), (key2794, 1), (key2944, 1), (key2671, 1), (key2674, 1), (key2786, -1), (key2939, -1), (key2809, -2), (key2860, 1), (key2898, 1), (key2706, 2), (key2860, -1), (key2977, -1), (key2706, -1), (key2738, -1), (key2809, 1), (key2951, 1), (key2829, 1), (key2832, 1), (key2870, -1), (key2905, -1), (key2726, -1), (key2729, -1), (key2870, 1), (key2984, 1), (key2726, 1), (key2748, 1), (key2829, -1), (key2961, -1)]

def rawRow466 : Integer.Sparse Key := [(key2632, -2), (key2642, 1), (key2640, 1), (key2616, 2), (key2654, -1), (key2640, -1), (key2619, -1), (key2616, -1), (key2649, 1), (key2632, 1), (key2786, 2), (key2796, -1), (key2794, -1), (key2671, -2), (key2944, 1), (key2794, 1), (key2674, 1), (key2671, 1), (key2939, -1), (key2786, -1), (key2809, -2), (key2898, 1), (key2860, 1), (key2706, 2), (key2977, -1), (key2860, -1), (key2738, -1), (key2706, -1), (key2951, 1), (key2809, 1), (key2832, 1), (key2829, 1), (key2905, -1), (key2870, -1), (key2729, -1), (key2726, -1), (key2984, 1), (key2870, 1), (key2748, 1), (key2726, 1), (key2961, -1), (key2829, -1)]

def rawRow467 : Integer.Sparse Key := [(key2642, -2), (key2632, 1), (key2640, 1), (key2654, 2), (key2616, -1), (key2640, -1), (key2649, -1), (key2654, -1), (key2619, 1), (key2642, 1), (key2796, 2), (key2786, -1), (key2794, -1), (key2944, -2), (key2671, 1), (key2794, 1), (key2939, 1), (key2944, 1), (key2674, -1), (key2796, -1), (key2898, -2), (key2809, 1), (key2860, 1), (key2977, 2), (key2706, -1), (key2860, -1), (key2951, -1), (key2977, -1), (key2738, 1), (key2898, 1), (key2905, 1), (key2913, 1), (key2832, -1), (key2883, -1), (key2984, -1), (key2992, -1), (key2729, 1), (key2883, 1), (key2961, 1), (key2992, 1), (key2748, -1), (key2913, -1)]

def rawRow468 : Integer.Sparse Key := [(key2642, -2), (key2640, 1), (key2632, 1), (key2654, 2), (key2640, -1), (key2616, -1), (key2654, -1), (key2649, -1), (key2642, 1), (key2619, 1), (key2796, 2), (key2794, -1), (key2786, -1), (key2944, -2), (key2794, 1), (key2671, 1), (key2944, 1), (key2939, 1), (key2796, -1), (key2674, -1), (key2898, -2), (key2860, 1), (key2809, 1), (key2977, 2), (key2860, -1), (key2706, -1), (key2977, -1), (key2951, -1), (key2898, 1), (key2738, 1), (key2913, 1), (key2905, 1), (key2883, -1), (key2832, -1), (key2992, -1), (key2984, -1), (key2883, 1), (key2729, 1), (key2992, 1), (key2961, 1), (key2913, -1), (key2748, -1)]

def rawRow469 : Integer.Sparse Key := [(key2649, -2), (key2654, 1), (key2654, 1), (key2619, 2), (key2642, -1), (key2642, -1), (key2616, -1), (key2616, -1), (key2632, 1), (key2632, 1), (key2939, 2), (key2944, -1), (key2944, -1), (key2674, -2), (key2796, 1), (key2796, 1), (key2671, 1), (key2671, 1), (key2786, -1), (key2786, -1), (key2951, -2), (key2977, 1), (key2977, 1), (key2738, 2), (key2898, -1), (key2898, -1), (key2706, -1), (key2706, -1), (key2809, 1), (key2809, 1), (key2961, 1), (key2961, 1), (key2984, -1), (key2984, -1), (key2748, -1), (key2748, -1), (key2905, 1), (key2905, 1), (key2729, 1), (key2729, 1), (key2832, -1), (key2832, -1)]

def rawRow470 : Integer.Sparse Key := [(key2654, -2), (key2649, 1), (key2654, 1), (key2642, 2), (key2619, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2616, 1), (key2640, 1), (key2944, 2), (key2939, -1), (key2944, -1), (key2796, -2), (key2674, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2671, -1), (key2794, -1), (key2977, -2), (key2951, 1), (key2977, 1), (key2898, 2), (key2738, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2706, 1), (key2860, 1), (key2984, 1), (key2992, 1), (key2961, -1), (key2992, -1), (key2905, -1), (key2913, -1), (key2748, 1), (key2913, 1), (key2832, 1), (key2883, 1), (key2729, -1), (key2883, -1)]

def rawRow471 : Integer.Sparse Key := [(key2654, -2), (key2654, 1), (key2649, 1), (key2642, 2), (key2642, -1), (key2619, -1), (key2640, -1), (key2632, -1), (key2640, 1), (key2616, 1), (key2944, 2), (key2944, -1), (key2939, -1), (key2796, -2), (key2796, 1), (key2674, 1), (key2794, 1), (key2786, 1), (key2794, -1), (key2671, -1), (key2977, -2), (key2977, 1), (key2951, 1), (key2898, 2), (key2898, -1), (key2738, -1), (key2860, -1), (key2809, -1), (key2860, 1), (key2706, 1), (key2992, 1), (key2984, 1), (key2992, -1), (key2961, -1), (key2913, -1), (key2905, -1), (key2913, 1), (key2748, 1), (key2883, 1), (key2832, 1), (key2883, -1), (key2729, -1)]

def rawRow472 : Integer.Sparse Key := [(key2671, -2), (key2671, 1), (key2674, 1), (key2706, 2), (key2706, -1), (key2738, -1), (key2726, -1), (key2729, -1), (key2726, 1), (key2748, 1), (key2616, 2), (key2616, -1), (key2619, -1), (key2809, -2), (key2809, 1), (key2951, 1), (key2829, 1), (key2832, 1), (key2829, -1), (key2961, -1), (key2632, -2), (key2632, 1), (key2649, 1), (key2786, 2), (key2786, -1), (key2939, -1), (key2870, -1), (key2905, -1), (key2870, 1), (key2984, 1), (key2640, 1), (key2642, 1), (key2640, -1), (key2654, -1), (key2794, -1), (key2796, -1), (key2794, 1), (key2944, 1), (key2860, 1), (key2898, 1), (key2860, -1), (key2977, -1)]

def rawRow473 : Integer.Sparse Key := [(key2671, -2), (key2674, 1), (key2671, 1), (key2706, 2), (key2738, -1), (key2706, -1), (key2729, -1), (key2726, -1), (key2748, 1), (key2726, 1), (key2616, 2), (key2619, -1), (key2616, -1), (key2809, -2), (key2951, 1), (key2809, 1), (key2832, 1), (key2829, 1), (key2961, -1), (key2829, -1), (key2632, -2), (key2649, 1), (key2632, 1), (key2786, 2), (key2939, -1), (key2786, -1), (key2905, -1), (key2870, -1), (key2984, 1), (key2870, 1), (key2642, 1), (key2640, 1), (key2654, -1), (key2640, -1), (key2796, -1), (key2794, -1), (key2944, 1), (key2794, 1), (key2898, 1), (key2860, 1), (key2977, -1), (key2860, -1)]

def rawRow474 : Integer.Sparse Key := [(key2674, -2), (key2671, 1), (key2671, 1), (key2738, 2), (key2706, -1), (key2706, -1), (key2748, -1), (key2748, -1), (key2729, 1), (key2729, 1), (key2619, 2), (key2616, -1), (key2616, -1), (key2951, -2), (key2809, 1), (key2809, 1), (key2961, 1), (key2961, 1), (key2832, -1), (key2832, -1), (key2649, -2), (key2632, 1), (key2632, 1), (key2939, 2), (key2786, -1), (key2786, -1), (key2984, -1), (key2984, -1), (key2905, 1), (key2905, 1), (key2654, 1), (key2654, 1), (key2642, -1), (key2642, -1), (key2944, -1), (key2944, -1), (key2796, 1), (key2796, 1), (key2977, 1), (key2977, 1), (key2898, -1), (key2898, -1)]

def rawRow475 : Integer.Sparse Key := [(key2706, -2), (key2726, 1), (key2729, 1), (key2671, 2), (key2726, -1), (key2748, -1), (key2671, -1), (key2674, -1), (key2706, 1), (key2738, 1), (key2809, 2), (key2829, -1), (key2832, -1), (key2616, -2), (key2829, 1), (key2961, 1), (key2616, 1), (key2619, 1), (key2809, -1), (key2951, -1), (key2786, -2), (key2870, 1), (key2905, 1), (key2632, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2649, -1), (key2786, 1), (key2939, 1), (key2794, 1), (key2796, 1), (key2860, -1), (key2898, -1), (key2640, -1), (key2642, -1), (key2860, 1), (key2977, 1), (key2640, 1), (key2654, 1), (key2794, -1), (key2944, -1)]

def rawRow476 : Integer.Sparse Key := [(key2706, -2), (key2729, 1), (key2726, 1), (key2671, 2), (key2748, -1), (key2726, -1), (key2674, -1), (key2671, -1), (key2738, 1), (key2706, 1), (key2809, 2), (key2832, -1), (key2829, -1), (key2616, -2), (key2961, 1), (key2829, 1), (key2619, 1), (key2616, 1), (key2951, -1), (key2809, -1), (key2786, -2), (key2905, 1), (key2870, 1), (key2632, 2), (key2984, -1), (key2870, -1), (key2649, -1), (key2632, -1), (key2939, 1), (key2786, 1), (key2796, 1), (key2794, 1), (key2898, -1), (key2860, -1), (key2642, -1), (key2640, -1), (key2977, 1), (key2860, 1), (key2654, 1), (key2640, 1), (key2944, -1), (key2794, -1)]

def rawRow477 : Integer.Sparse Key := [(key2729, -2), (key2706, 1), (key2726, 1), (key2748, 2), (key2671, -1), (key2726, -1), (key2738, -1), (key2748, -1), (key2674, 1), (key2729, 1), (key2832, 2), (key2809, -1), (key2829, -1), (key2961, -2), (key2616, 1), (key2829, 1), (key2951, 1), (key2961, 1), (key2619, -1), (key2832, -1), (key2905, -2), (key2786, 1), (key2870, 1), (key2984, 2), (key2632, -1), (key2870, -1), (key2939, -1), (key2984, -1), (key2649, 1), (key2905, 1), (key2898, 1), (key2913, 1), (key2796, -1), (key2883, -1), (key2977, -1), (key2992, -1), (key2642, 1), (key2883, 1), (key2944, 1), (key2992, 1), (key2654, -1), (key2913, -1)]

def rawRow478 : Integer.Sparse Key := [(key2729, -2), (key2726, 1), (key2706, 1), (key2748, 2), (key2726, -1), (key2671, -1), (key2748, -1), (key2738, -1), (key2729, 1), (key2674, 1), (key2832, 2), (key2829, -1), (key2809, -1), (key2961, -2), (key2829, 1), (key2616, 1), (key2961, 1), (key2951, 1), (key2832, -1), (key2619, -1), (key2905, -2), (key2870, 1), (key2786, 1), (key2984, 2), (key2870, -1), (key2632, -1), (key2984, -1), (key2939, -1), (key2905, 1), (key2649, 1), (key2913, 1), (key2898, 1), (key2883, -1), (key2796, -1), (key2992, -1), (key2977, -1), (key2883, 1), (key2642, 1), (key2992, 1), (key2944, 1), (key2913, -1), (key2654, -1)]

def rawRow479 : Integer.Sparse Key := [(key2738, -2), (key2748, 1), (key2748, 1), (key2674, 2), (key2729, -1), (key2729, -1), (key2671, -1), (key2671, -1), (key2706, 1), (key2706, 1), (key2951, 2), (key2961, -1), (key2961, -1), (key2619, -2), (key2832, 1), (key2832, 1), (key2616, 1), (key2616, 1), (key2809, -1), (key2809, -1), (key2939, -2), (key2984, 1), (key2984, 1), (key2649, 2), (key2905, -1), (key2905, -1), (key2632, -1), (key2632, -1), (key2786, 1), (key2786, 1), (key2944, 1), (key2944, 1), (key2977, -1), (key2977, -1), (key2654, -1), (key2654, -1), (key2898, 1), (key2898, 1), (key2642, 1), (key2642, 1), (key2796, -1), (key2796, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow480 : Integer.Sparse Key := [(key2748, -2), (key2738, 1), (key2748, 1), (key2729, 2), (key2674, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2671, 1), (key2726, 1), (key2961, 2), (key2951, -1), (key2961, -1), (key2832, -2), (key2619, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2616, -1), (key2829, -1), (key2984, -2), (key2939, 1), (key2984, 1), (key2905, 2), (key2649, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2632, 1), (key2870, 1), (key2977, 1), (key2992, 1), (key2944, -1), (key2992, -1), (key2898, -1), (key2913, -1), (key2654, 1), (key2913, 1), (key2796, 1), (key2883, 1), (key2642, -1), (key2883, -1)]

def rawRow481 : Integer.Sparse Key := [(key2748, -2), (key2748, 1), (key2738, 1), (key2729, 2), (key2729, -1), (key2674, -1), (key2726, -1), (key2706, -1), (key2726, 1), (key2671, 1), (key2961, 2), (key2961, -1), (key2951, -1), (key2832, -2), (key2832, 1), (key2619, 1), (key2829, 1), (key2809, 1), (key2829, -1), (key2616, -1), (key2984, -2), (key2984, 1), (key2939, 1), (key2905, 2), (key2905, -1), (key2649, -1), (key2870, -1), (key2786, -1), (key2870, 1), (key2632, 1), (key2992, 1), (key2977, 1), (key2992, -1), (key2944, -1), (key2913, -1), (key2898, -1), (key2913, 1), (key2654, 1), (key2883, 1), (key2796, 1), (key2883, -1), (key2642, -1)]

def rawRow482 : Integer.Sparse Key := [(key2786, -2), (key2794, 1), (key2796, 1), (key2809, 2), (key2860, -1), (key2898, -1), (key2829, -1), (key2832, -1), (key2870, 1), (key2905, 1), (key2632, 2), (key2640, -1), (key2642, -1), (key2706, -2), (key2860, 1), (key2977, 1), (key2726, 1), (key2729, 1), (key2870, -1), (key2984, -1), (key2616, -2), (key2640, 1), (key2654, 1), (key2671, 2), (key2794, -1), (key2944, -1), (key2726, -1), (key2748, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2619, 1), (key2632, -1), (key2649, -1), (key2671, -1), (key2674, -1), (key2786, 1), (key2939, 1), (key2706, 1), (key2738, 1), (key2809, -1), (key2951, -1)]

def rawRow483 : Integer.Sparse Key := [(key2786, -2), (key2796, 1), (key2794, 1), (key2809, 2), (key2898, -1), (key2860, -1), (key2832, -1), (key2829, -1), (key2905, 1), (key2870, 1), (key2632, 2), (key2642, -1), (key2640, -1), (key2706, -2), (key2977, 1), (key2860, 1), (key2729, 1), (key2726, 1), (key2984, -1), (key2870, -1), (key2616, -2), (key2654, 1), (key2640, 1), (key2671, 2), (key2944, -1), (key2794, -1), (key2748, -1), (key2726, -1), (key2961, 1), (key2829, 1), (key2619, 1), (key2616, 1), (key2649, -1), (key2632, -1), (key2674, -1), (key2671, -1), (key2939, 1), (key2786, 1), (key2738, 1), (key2706, 1), (key2951, -1), (key2809, -1)]

def rawRow484 : Integer.Sparse Key := [(key2796, -2), (key2786, 1), (key2794, 1), (key2898, 2), (key2809, -1), (key2860, -1), (key2905, -1), (key2913, -1), (key2832, 1), (key2883, 1), (key2642, 2), (key2632, -1), (key2640, -1), (key2977, -2), (key2706, 1), (key2860, 1), (key2984, 1), (key2992, 1), (key2729, -1), (key2883, -1), (key2654, -2), (key2616, 1), (key2640, 1), (key2944, 2), (key2671, -1), (key2794, -1), (key2961, -1), (key2992, -1), (key2748, 1), (key2913, 1), (key2649, 1), (key2654, 1), (key2619, -1), (key2642, -1), (key2939, -1), (key2944, -1), (key2674, 1), (key2796, 1), (key2951, 1), (key2977, 1), (key2738, -1), (key2898, -1)]

def rawRow485 : Integer.Sparse Key := [(key2796, -2), (key2794, 1), (key2786, 1), (key2898, 2), (key2860, -1), (key2809, -1), (key2913, -1), (key2905, -1), (key2883, 1), (key2832, 1), (key2642, 2), (key2640, -1), (key2632, -1), (key2977, -2), (key2860, 1), (key2706, 1), (key2992, 1), (key2984, 1), (key2883, -1), (key2729, -1), (key2654, -2), (key2640, 1), (key2616, 1), (key2944, 2), (key2794, -1), (key2671, -1), (key2992, -1), (key2961, -1), (key2913, 1), (key2748, 1), (key2654, 1), (key2649, 1), (key2642, -1), (key2619, -1), (key2944, -1), (key2939, -1), (key2796, 1), (key2674, 1), (key2977, 1), (key2951, 1), (key2898, -1), (key2738, -1)]

def rawRow486 : Integer.Sparse Key := [(key2809, -2), (key2829, 1), (key2832, 1), (key2786, 2), (key2870, -1), (key2905, -1), (key2794, -1), (key2796, -1), (key2860, 1), (key2898, 1), (key2706, 2), (key2726, -1), (key2729, -1), (key2632, -2), (key2870, 1), (key2984, 1), (key2640, 1), (key2642, 1), (key2860, -1), (key2977, -1), (key2671, -2), (key2726, 1), (key2748, 1), (key2616, 2), (key2829, -1), (key2961, -1), (key2640, -1), (key2654, -1), (key2794, 1), (key2944, 1), (key2671, 1), (key2674, 1), (key2706, -1), (key2738, -1), (key2616, -1), (key2619, -1), (key2809, 1), (key2951, 1), (key2632, 1), (key2649, 1), (key2786, -1), (key2939, -1)]

def rawRow487 : Integer.Sparse Key := [(key2809, -2), (key2832, 1), (key2829, 1), (key2786, 2), (key2905, -1), (key2870, -1), (key2796, -1), (key2794, -1), (key2898, 1), (key2860, 1), (key2706, 2), (key2729, -1), (key2726, -1), (key2632, -2), (key2984, 1), (key2870, 1), (key2642, 1), (key2640, 1), (key2977, -1), (key2860, -1), (key2671, -2), (key2748, 1), (key2726, 1), (key2616, 2), (key2961, -1), (key2829, -1), (key2654, -1), (key2640, -1), (key2944, 1), (key2794, 1), (key2674, 1), (key2671, 1), (key2738, -1), (key2706, -1), (key2619, -1), (key2616, -1), (key2951, 1), (key2809, 1), (key2649, 1), (key2632, 1), (key2939, -1), (key2786, -1)]

def rawRow488 : Integer.Sparse Key := [(key2832, -2), (key2809, 1), (key2829, 1), (key2905, 2), (key2786, -1), (key2870, -1), (key2898, -1), (key2913, -1), (key2796, 1), (key2883, 1), (key2729, 2), (key2706, -1), (key2726, -1), (key2984, -2), (key2632, 1), (key2870, 1), (key2977, 1), (key2992, 1), (key2642, -1), (key2883, -1), (key2748, -2), (key2671, 1), (key2726, 1), (key2961, 2), (key2616, -1), (key2829, -1), (key2944, -1), (key2992, -1), (key2654, 1), (key2913, 1), (key2738, 1), (key2748, 1), (key2674, -1), (key2729, -1), (key2951, -1), (key2961, -1), (key2619, 1), (key2832, 1), (key2939, 1), (key2984, 1), (key2649, -1), (key2905, -1)]

def rawRow489 : Integer.Sparse Key := [(key2832, -2), (key2829, 1), (key2809, 1), (key2905, 2), (key2870, -1), (key2786, -1), (key2913, -1), (key2898, -1), (key2883, 1), (key2796, 1), (key2729, 2), (key2726, -1), (key2706, -1), (key2984, -2), (key2870, 1), (key2632, 1), (key2992, 1), (key2977, 1), (key2883, -1), (key2642, -1), (key2748, -2), (key2726, 1), (key2671, 1), (key2961, 2), (key2829, -1), (key2616, -1), (key2992, -1), (key2944, -1), (key2913, 1), (key2654, 1), (key2748, 1), (key2738, 1), (key2729, -1), (key2674, -1), (key2961, -1), (key2951, -1), (key2832, 1), (key2619, 1), (key2984, 1), (key2939, 1), (key2905, -1), (key2649, -1)]

def rawRow490 : Integer.Sparse Key := [(key2898, -2), (key2905, 1), (key2913, 1), (key2796, 2), (key2832, -1), (key2883, -1), (key2786, -1), (key2794, -1), (key2809, 1), (key2860, 1), (key2977, 2), (key2984, -1), (key2992, -1), (key2642, -2), (key2729, 1), (key2883, 1), (key2632, 1), (key2640, 1), (key2706, -1), (key2860, -1), (key2944, -2), (key2961, 1), (key2992, 1), (key2654, 2), (key2748, -1), (key2913, -1), (key2616, -1), (key2640, -1), (key2671, 1), (key2794, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2977, -1), (key2649, -1), (key2654, -1), (key2738, 1), (key2898, 1), (key2619, 1), (key2642, 1), (key2674, -1), (key2796, -1)]

def rawRow491 : Integer.Sparse Key := [(key2898, -2), (key2913, 1), (key2905, 1), (key2796, 2), (key2883, -1), (key2832, -1), (key2794, -1), (key2786, -1), (key2860, 1), (key2809, 1), (key2977, 2), (key2992, -1), (key2984, -1), (key2642, -2), (key2883, 1), (key2729, 1), (key2640, 1), (key2632, 1), (key2860, -1), (key2706, -1), (key2944, -2), (key2992, 1), (key2961, 1), (key2654, 2), (key2913, -1), (key2748, -1), (key2640, -1), (key2616, -1), (key2794, 1), (key2671, 1), (key2944, 1), (key2939, 1), (key2977, -1), (key2951, -1), (key2654, -1), (key2649, -1), (key2898, 1), (key2738, 1), (key2642, 1), (key2619, 1), (key2796, -1), (key2674, -1)]

def rawRow492 : Integer.Sparse Key := [(key2905, -2), (key2898, 1), (key2913, 1), (key2832, 2), (key2796, -1), (key2883, -1), (key2809, -1), (key2829, -1), (key2786, 1), (key2870, 1), (key2984, 2), (key2977, -1), (key2992, -1), (key2729, -2), (key2642, 1), (key2883, 1), (key2706, 1), (key2726, 1), (key2632, -1), (key2870, -1), (key2961, -2), (key2944, 1), (key2992, 1), (key2748, 2), (key2654, -1), (key2913, -1), (key2671, -1), (key2726, -1), (key2616, 1), (key2829, 1), (key2951, 1), (key2961, 1), (key2939, -1), (key2984, -1), (key2738, -1), (key2748, -1), (key2649, 1), (key2905, 1), (key2674, 1), (key2729, 1), (key2619, -1), (key2832, -1)]

def rawRow493 : Integer.Sparse Key := [(key2905, -2), (key2913, 1), (key2898, 1), (key2832, 2), (key2883, -1), (key2796, -1), (key2829, -1), (key2809, -1), (key2870, 1), (key2786, 1), (key2984, 2), (key2992, -1), (key2977, -1), (key2729, -2), (key2883, 1), (key2642, 1), (key2726, 1), (key2706, 1), (key2870, -1), (key2632, -1), (key2961, -2), (key2992, 1), (key2944, 1), (key2748, 2), (key2913, -1), (key2654, -1), (key2726, -1), (key2671, -1), (key2829, 1), (key2616, 1), (key2961, 1), (key2951, 1), (key2984, -1), (key2939, -1), (key2748, -1), (key2738, -1), (key2905, 1), (key2649, 1), (key2729, 1), (key2674, 1), (key2832, -1), (key2619, -1)]

def rawRow494 : Integer.Sparse Key := [(key2939, -2), (key2944, 1), (key2944, 1), (key2951, 2), (key2977, -1), (key2977, -1), (key2961, -1), (key2961, -1), (key2984, 1), (key2984, 1), (key2649, 2), (key2654, -1), (key2654, -1), (key2738, -2), (key2898, 1), (key2898, 1), (key2748, 1), (key2748, 1), (key2905, -1), (key2905, -1), (key2619, -2), (key2642, 1), (key2642, 1), (key2674, 2), (key2796, -1), (key2796, -1), (key2729, -1), (key2729, -1), (key2832, 1), (key2832, 1), (key2616, 1), (key2616, 1), (key2632, -1), (key2632, -1), (key2671, -1), (key2671, -1), (key2786, 1), (key2786, 1), (key2706, 1), (key2706, 1), (key2809, -1), (key2809, -1)]

def rawRow495 : Integer.Sparse Key := [(key2944, -2), (key2939, 1), (key2944, 1), (key2977, 2), (key2951, -1), (key2977, -1), (key2984, -1), (key2992, -1), (key2961, 1), (key2992, 1), (key2654, 2), (key2649, -1), (key2654, -1), (key2898, -2), (key2738, 1), (key2898, 1), (key2905, 1), (key2913, 1), (key2748, -1), (key2913, -1), (key2642, -2), (key2619, 1), (key2642, 1), (key2796, 2), (key2674, -1), (key2796, -1), (key2832, -1), (key2883, -1), (key2729, 1), (key2883, 1), (key2632, 1), (key2640, 1), (key2616, -1), (key2640, -1), (key2786, -1), (key2794, -1), (key2671, 1), (key2794, 1), (key2809, 1), (key2860, 1), (key2706, -1), (key2860, -1)]

def rawRow496 : Integer.Sparse Key := [(key2944, -2), (key2944, 1), (key2939, 1), (key2977, 2), (key2977, -1), (key2951, -1), (key2992, -1), (key2984, -1), (key2992, 1), (key2961, 1), (key2654, 2), (key2654, -1), (key2649, -1), (key2898, -2), (key2898, 1), (key2738, 1), (key2913, 1), (key2905, 1), (key2913, -1), (key2748, -1), (key2642, -2), (key2642, 1), (key2619, 1), (key2796, 2), (key2796, -1), (key2674, -1), (key2883, -1), (key2832, -1), (key2883, 1), (key2729, 1), (key2640, 1), (key2632, 1), (key2640, -1), (key2616, -1), (key2794, -1), (key2786, -1), (key2794, 1), (key2671, 1), (key2860, 1), (key2809, 1), (key2860, -1), (key2706, -1)]

def rawRow497 : Integer.Sparse Key := [(key2951, -2), (key2961, 1), (key2961, 1), (key2939, 2), (key2984, -1), (key2984, -1), (key2944, -1), (key2944, -1), (key2977, 1), (key2977, 1), (key2738, 2), (key2748, -1), (key2748, -1), (key2649, -2), (key2905, 1), (key2905, 1), (key2654, 1), (key2654, 1), (key2898, -1), (key2898, -1), (key2674, -2), (key2729, 1), (key2729, 1), (key2619, 2), (key2832, -1), (key2832, -1), (key2642, -1), (key2642, -1), (key2796, 1), (key2796, 1), (key2671, 1), (key2671, 1), (key2706, -1), (key2706, -1), (key2616, -1), (key2616, -1), (key2809, 1), (key2809, 1), (key2632, 1), (key2632, 1), (key2786, -1), (key2786, -1)]

def rawRow498 : Integer.Sparse Key := [(key2961, -2), (key2951, 1), (key2961, 1), (key2984, 2), (key2939, -1), (key2984, -1), (key2977, -1), (key2992, -1), (key2944, 1), (key2992, 1), (key2748, 2), (key2738, -1), (key2748, -1), (key2905, -2), (key2649, 1), (key2905, 1), (key2898, 1), (key2913, 1), (key2654, -1), (key2913, -1), (key2729, -2), (key2674, 1), (key2729, 1), (key2832, 2), (key2619, -1), (key2832, -1), (key2796, -1), (key2883, -1), (key2642, 1), (key2883, 1), (key2706, 1), (key2726, 1), (key2671, -1), (key2726, -1), (key2809, -1), (key2829, -1), (key2616, 1), (key2829, 1), (key2786, 1), (key2870, 1), (key2632, -1), (key2870, -1)]

def rawRow499 : Integer.Sparse Key := [(key2961, -2), (key2961, 1), (key2951, 1), (key2984, 2), (key2984, -1), (key2939, -1), (key2992, -1), (key2977, -1), (key2992, 1), (key2944, 1), (key2748, 2), (key2748, -1), (key2738, -1), (key2905, -2), (key2905, 1), (key2649, 1), (key2913, 1), (key2898, 1), (key2913, -1), (key2654, -1), (key2729, -2), (key2729, 1), (key2674, 1), (key2832, 2), (key2832, -1), (key2619, -1), (key2883, -1), (key2796, -1), (key2883, 1), (key2642, 1), (key2726, 1), (key2706, 1), (key2726, -1), (key2671, -1), (key2829, -1), (key2809, -1), (key2829, 1), (key2616, 1), (key2870, 1), (key2786, 1), (key2870, -1), (key2632, -1)]

def rawRow500 : Integer.Sparse Key := [(key2977, -2), (key2984, 1), (key2992, 1), (key2944, 2), (key2961, -1), (key2992, -1), (key2939, -1), (key2944, -1), (key2951, 1), (key2977, 1), (key2898, 2), (key2905, -1), (key2913, -1), (key2654, -2), (key2748, 1), (key2913, 1), (key2649, 1), (key2654, 1), (key2738, -1), (key2898, -1), (key2796, -2), (key2832, 1), (key2883, 1), (key2642, 2), (key2729, -1), (key2883, -1), (key2619, -1), (key2642, -1), (key2674, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2809, -1), (key2860, -1), (key2632, -1), (key2640, -1), (key2706, 1), (key2860, 1), (key2616, 1), (key2640, 1), (key2671, -1), (key2794, -1)]

def rawRow501 : Integer.Sparse Key := [(key2977, -2), (key2992, 1), (key2984, 1), (key2944, 2), (key2992, -1), (key2961, -1), (key2944, -1), (key2939, -1), (key2977, 1), (key2951, 1), (key2898, 2), (key2913, -1), (key2905, -1), (key2654, -2), (key2913, 1), (key2748, 1), (key2654, 1), (key2649, 1), (key2898, -1), (key2738, -1), (key2796, -2), (key2883, 1), (key2832, 1), (key2642, 2), (key2883, -1), (key2729, -1), (key2642, -1), (key2619, -1), (key2796, 1), (key2674, 1), (key2794, 1), (key2786, 1), (key2860, -1), (key2809, -1), (key2640, -1), (key2632, -1), (key2860, 1), (key2706, 1), (key2640, 1), (key2616, 1), (key2794, -1), (key2671, -1)]

def rawRow502 : Integer.Sparse Key := [(key2984, -2), (key2977, 1), (key2992, 1), (key2961, 2), (key2944, -1), (key2992, -1), (key2951, -1), (key2961, -1), (key2939, 1), (key2984, 1), (key2905, 2), (key2898, -1), (key2913, -1), (key2748, -2), (key2654, 1), (key2913, 1), (key2738, 1), (key2748, 1), (key2649, -1), (key2905, -1), (key2832, -2), (key2796, 1), (key2883, 1), (key2729, 2), (key2642, -1), (key2883, -1), (key2674, -1), (key2729, -1), (key2619, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2786, -1), (key2870, -1), (key2706, -1), (key2726, -1), (key2632, 1), (key2870, 1), (key2671, 1), (key2726, 1), (key2616, -1), (key2829, -1)]

def rawRow503 : Integer.Sparse Key := [(key2984, -2), (key2992, 1), (key2977, 1), (key2961, 2), (key2992, -1), (key2944, -1), (key2961, -1), (key2951, -1), (key2984, 1), (key2939, 1), (key2905, 2), (key2913, -1), (key2898, -1), (key2748, -2), (key2913, 1), (key2654, 1), (key2748, 1), (key2738, 1), (key2905, -1), (key2649, -1), (key2832, -2), (key2883, 1), (key2796, 1), (key2729, 2), (key2883, -1), (key2642, -1), (key2729, -1), (key2674, -1), (key2832, 1), (key2619, 1), (key2829, 1), (key2809, 1), (key2870, -1), (key2786, -1), (key2726, -1), (key2706, -1), (key2870, 1), (key2632, 1), (key2726, 1), (key2671, 1), (key2829, -1), (key2616, -1)]

def rawRow504 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2613, 2), (key2625, 1), (key2629, 1), (key2629, -1), (key2647, -1), (key2637, -2), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2668, -2), (key2779, -1), (key2783, -1), (key2783, 1), (key2937, 1), (key2791, 2), (key2791, -1), (key2942, -1), (key2699, -1), (key2703, -1), (key2703, 1), (key2736, 1), (key2802, 1), (key2806, 1), (key2806, -1), (key2949, -1), (key2857, -1), (key2896, -1), (key2857, 1), (key2975, 1), (key2723, 2), (key2723, -1), (key2746, -1), (key2826, -2), (key2826, 1), (key2959, 1), (key2867, 1), (key2903, 1), (key2867, -1), (key2982, -1)]

def rawRow505 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2613, 2), (key2629, 1), (key2625, 1), (key2647, -1), (key2629, -1), (key2637, -2), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2668, -2), (key2783, -1), (key2779, -1), (key2937, 1), (key2783, 1), (key2791, 2), (key2942, -1), (key2791, -1), (key2703, -1), (key2699, -1), (key2736, 1), (key2703, 1), (key2806, 1), (key2802, 1), (key2949, -1), (key2806, -1), (key2896, -1), (key2857, -1), (key2975, 1), (key2857, 1), (key2723, 2), (key2746, -1), (key2723, -1), (key2826, -2), (key2959, 1), (key2826, 1), (key2903, 1), (key2867, 1), (key2982, -1), (key2867, -1)]

def rawRow506 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2609, 2), (key2647, 1), (key2647, 1), (key2625, -1), (key2625, -1), (key2652, -2), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2664, -2), (key2937, -1), (key2937, -1), (key2779, 1), (key2779, 1), (key2942, 2), (key2791, -1), (key2791, -1), (key2736, -1), (key2736, -1), (key2699, 1), (key2699, 1), (key2949, 1), (key2949, 1), (key2802, -1), (key2802, -1), (key2975, -1), (key2975, -1), (key2896, 1), (key2896, 1), (key2746, 2), (key2723, -1), (key2723, -1), (key2959, -2), (key2826, 1), (key2826, 1), (key2982, 1), (key2982, 1), (key2903, -1), (key2903, -1)]

def rawRow507 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2637, 2), (key2609, 1), (key2613, 1), (key2637, -1), (key2652, -1), (key2613, -2), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2791, -2), (key2664, -1), (key2668, -1), (key2791, 1), (key2942, 1), (key2668, 2), (key2783, -1), (key2937, -1), (key2802, -1), (key2806, -1), (key2857, 1), (key2896, 1), (key2699, 1), (key2703, 1), (key2857, -1), (key2975, -1), (key2703, -1), (key2736, -1), (key2806, 1), (key2949, 1), (key2826, 2), (key2867, -1), (key2903, -1), (key2723, -2), (key2867, 1), (key2982, 1), (key2723, 1), (key2746, 1), (key2826, -1), (key2959, -1)]

def rawRow508 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2637, 2), (key2613, 1), (key2609, 1), (key2652, -1), (key2637, -1), (key2613, -2), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2791, -2), (key2668, -1), (key2664, -1), (key2942, 1), (key2791, 1), (key2668, 2), (key2937, -1), (key2783, -1), (key2806, -1), (key2802, -1), (key2896, 1), (key2857, 1), (key2703, 1), (key2699, 1), (key2975, -1), (key2857, -1), (key2736, -1), (key2703, -1), (key2949, 1), (key2806, 1), (key2826, 2), (key2903, -1), (key2867, -1), (key2723, -2), (key2982, 1), (key2867, 1), (key2746, 1), (key2723, 1), (key2959, -1), (key2826, -1)]

def rawRow509 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2625, 2), (key2647, 1), (key2652, 1), (key2609, -1), (key2625, -1), (key2647, -2), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2779, -2), (key2937, -1), (key2942, -1), (key2664, 1), (key2779, 1), (key2937, 2), (key2668, -1), (key2783, -1), (key2894, -1), (key2896, -1), (key2802, 1), (key2852, 1), (key2973, 1), (key2975, 1), (key2699, -1), (key2852, -1), (key2949, -1), (key2973, -1), (key2736, 1), (key2894, 1), (key2903, 2), (key2826, -1), (key2867, -1), (key2982, -2), (key2723, 1), (key2867, 1), (key2959, 1), (key2982, 1), (key2746, -1), (key2903, -1)]

def rawRow510 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2625, 2), (key2652, 1), (key2647, 1), (key2625, -1), (key2609, -1), (key2647, -2), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2779, -2), (key2942, -1), (key2937, -1), (key2779, 1), (key2664, 1), (key2937, 2), (key2783, -1), (key2668, -1), (key2896, -1), (key2894, -1), (key2852, 1), (key2802, 1), (key2975, 1), (key2973, 1), (key2852, -1), (key2699, -1), (key2973, -1), (key2949, -1), (key2894, 1), (key2736, 1), (key2903, 2), (key2867, -1), (key2826, -1), (key2982, -2), (key2867, 1), (key2723, 1), (key2982, 1), (key2959, 1), (key2903, -1), (key2746, -1)]

def rawRow511 : Integer.Sparse Key := [(key2647, -1), (key2647, -1), (key2652, 2), (key2613, 1), (key2613, 1), (key2637, -1), (key2637, -1), (key2609, -2), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2942, -2), (key2668, -1), (key2668, -1), (key2791, 1), (key2791, 1), (key2664, 2), (key2779, -1), (key2779, -1), (key2949, -1), (key2949, -1), (key2975, 1), (key2975, 1), (key2736, 1), (key2736, 1), (key2896, -1), (key2896, -1), (key2699, -1), (key2699, -1), (key2802, 1), (key2802, 1), (key2959, 2), (key2982, -1), (key2982, -1), (key2746, -2), (key2903, 1), (key2903, 1), (key2723, 1), (key2723, 1), (key2826, -1), (key2826, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow512 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2647, 2), (key2629, 1), (key2637, 1), (key2613, -1), (key2629, -1), (key2625, -2), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2937, -2), (key2783, -1), (key2791, -1), (key2668, 1), (key2783, 1), (key2779, 2), (key2664, -1), (key2779, -1), (key2973, -1), (key2975, -1), (key2949, 1), (key2973, 1), (key2894, 1), (key2896, 1), (key2736, -1), (key2894, -1), (key2802, -1), (key2852, -1), (key2699, 1), (key2852, 1), (key2982, 2), (key2959, -1), (key2982, -1), (key2903, -2), (key2746, 1), (key2903, 1), (key2826, 1), (key2867, 1), (key2723, -1), (key2867, -1)]

def rawRow513 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2647, 2), (key2637, 1), (key2629, 1), (key2629, -1), (key2613, -1), (key2625, -2), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2937, -2), (key2791, -1), (key2783, -1), (key2783, 1), (key2668, 1), (key2779, 2), (key2779, -1), (key2664, -1), (key2975, -1), (key2973, -1), (key2973, 1), (key2949, 1), (key2896, 1), (key2894, 1), (key2894, -1), (key2736, -1), (key2852, -1), (key2802, -1), (key2852, 1), (key2699, 1), (key2982, 2), (key2982, -1), (key2959, -1), (key2903, -2), (key2903, 1), (key2746, 1), (key2867, 1), (key2826, 1), (key2867, -1), (key2723, -1)]

def rawRow514 : Integer.Sparse Key := [(key2664, -1), (key2668, -1), (key2668, 2), (key2699, 1), (key2703, 1), (key2703, -1), (key2736, -1), (key2723, -2), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2613, -2), (key2802, -1), (key2806, -1), (key2806, 1), (key2949, 1), (key2826, 2), (key2826, -1), (key2959, -1), (key2625, -1), (key2629, -1), (key2629, 1), (key2647, 1), (key2779, 1), (key2783, 1), (key2783, -1), (key2937, -1), (key2867, -1), (key2903, -1), (key2867, 1), (key2982, 1), (key2637, 2), (key2637, -1), (key2652, -1), (key2791, -2), (key2791, 1), (key2942, 1), (key2857, 1), (key2896, 1), (key2857, -1), (key2975, -1)]

def rawRow515 : Integer.Sparse Key := [(key2668, -1), (key2664, -1), (key2668, 2), (key2703, 1), (key2699, 1), (key2736, -1), (key2703, -1), (key2723, -2), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2613, -2), (key2806, -1), (key2802, -1), (key2949, 1), (key2806, 1), (key2826, 2), (key2959, -1), (key2826, -1), (key2629, -1), (key2625, -1), (key2647, 1), (key2629, 1), (key2783, 1), (key2779, 1), (key2937, -1), (key2783, -1), (key2903, -1), (key2867, -1), (key2982, 1), (key2867, 1), (key2637, 2), (key2652, -1), (key2637, -1), (key2791, -2), (key2942, 1), (key2791, 1), (key2896, 1), (key2857, 1), (key2975, -1), (key2857, -1)]

def rawRow516 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2664, 2), (key2736, 1), (key2736, 1), (key2699, -1), (key2699, -1), (key2746, -2), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2609, -2), (key2949, -1), (key2949, -1), (key2802, 1), (key2802, 1), (key2959, 2), (key2826, -1), (key2826, -1), (key2647, -1), (key2647, -1), (key2625, 1), (key2625, 1), (key2937, 1), (key2937, 1), (key2779, -1), (key2779, -1), (key2982, -1), (key2982, -1), (key2903, 1), (key2903, 1), (key2652, 2), (key2637, -1), (key2637, -1), (key2942, -2), (key2791, 1), (key2791, 1), (key2975, 1), (key2975, 1), (key2896, -1), (key2896, -1)]

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

def rawRow688 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2735, 1), (key2737, 1), (key2735, 1), (key2747, 1), (key2737, 1), (key2747, 1), (key2805, 2), (key2805, 2), (key2831, 2), (key2893, -1), (key2897, -1), (key2893, -1), (key2904, -1), (key2897, -1), (key2904, -1), (key2948, -1), (key2950, -1), (key2948, -1), (key2960, -1), (key2950, -1), (key2960, -1), (key2972, 1), (key2976, 1), (key2972, 1), (key2983, 1), (key2976, 1), (key2983, 1)]

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

def rawRow4397 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2958, 1), (key2947, 1), (key2981, 1), (key2935, 1), (key2974, 1), (key2941, 1), (key2902, 2), (key2892, 2), (key2895, 2), (key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2825, -1), (key2804, -1), (key2866, -1), (key2781, -1), (key2856, -1), (key2790, -1), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1)]

def rawRow4398 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2974, 1), (key2981, 1), (key2941, 1), (key2958, 1), (key2935, 1), (key2947, 1), (key2895, 2), (key2902, 2), (key2892, 2), (key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2856, -1), (key2866, -1), (key2790, -1), (key2825, -1), (key2781, -1), (key2804, -1), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1)]

def rawRow4399 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2981, 1), (key2974, 1), (key2958, 1), (key2941, 1), (key2947, 1), (key2935, 1), (key2902, 2), (key2895, 2), (key2892, 2), (key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2866, -1), (key2856, -1), (key2825, -1), (key2790, -1), (key2804, -1), (key2781, -1), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

def rawRow4424 : Integer.Sparse Key := [(key2406, -2), (key2437, -2), (key2440, -2), (key2406, 2), (key2409, 2), (key2440, 2), (key2472, 2), (key2503, 2), (key2506, 2), (key2378, -1), (key2381, -1), (key2472, -1), (key2538, -1), (key2506, -1), (key2554, -1), (key2480, -2), (key2482, -2), (key2522, -2), (key2390, 1), (key2392, 1), (key2480, 1), (key2543, 1), (key2522, 1), (key2563, 1)]

def rawRow4425 : Integer.Sparse Key := [(key2406, -2), (key2440, -2), (key2437, -2), (key2409, 2), (key2406, 2), (key2440, 2), (key2472, 2), (key2506, 2), (key2503, 2), (key2381, -1), (key2378, -1), (key2538, -1), (key2472, -1), (key2554, -1), (key2506, -1), (key2482, -2), (key2480, -2), (key2522, -2), (key2392, 1), (key2390, 1), (key2543, 1), (key2480, 1), (key2563, 1), (key2522, 1)]

def rawRow4426 : Integer.Sparse Key := [(key2437, -2), (key2406, -2), (key2440, -2), (key2406, 2), (key2440, 2), (key2409, 2), (key2503, 2), (key2472, 2), (key2506, 2), (key2472, -1), (key2506, -1), (key2378, -1), (key2554, -1), (key2381, -1), (key2538, -1), (key2480, -2), (key2522, -2), (key2482, -2), (key2480, 1), (key2522, 1), (key2390, 1), (key2563, 1), (key2392, 1), (key2543, 1)]

def rawRow4427 : Integer.Sparse Key := [(key2437, -2), (key2440, -2), (key2406, -2), (key2440, 2), (key2406, 2), (key2409, 2), (key2503, 2), (key2506, 2), (key2472, 2), (key2506, -1), (key2472, -1), (key2554, -1), (key2378, -1), (key2538, -1), (key2381, -1), (key2522, -2), (key2480, -2), (key2482, -2), (key2522, 1), (key2480, 1), (key2563, 1), (key2390, 1), (key2543, 1), (key2392, 1)]

def rawRow4428 : Integer.Sparse Key := [(key2440, -2), (key2406, -2), (key2437, -2), (key2409, 2), (key2440, 2), (key2406, 2), (key2506, 2), (key2472, 2), (key2503, 2), (key2538, -1), (key2554, -1), (key2381, -1), (key2506, -1), (key2378, -1), (key2472, -1), (key2482, -2), (key2522, -2), (key2480, -2), (key2543, 1), (key2563, 1), (key2392, 1), (key2522, 1), (key2390, 1), (key2480, 1)]

def rawRow4429 : Integer.Sparse Key := [(key2440, -2), (key2437, -2), (key2406, -2), (key2440, 2), (key2409, 2), (key2406, 2), (key2506, 2), (key2503, 2), (key2472, 2), (key2554, -1), (key2538, -1), (key2506, -1), (key2381, -1), (key2472, -1), (key2378, -1), (key2522, -2), (key2482, -2), (key2480, -2), (key2563, 1), (key2543, 1), (key2522, 1), (key2392, 1), (key2480, 1), (key2390, 1)]

def rawRow4430 : Integer.Sparse Key := [(key2472, -2), (key2503, -2), (key2506, -2), (key2480, 2), (key2482, 2), (key2522, 2), (key2406, 2), (key2437, 2), (key2440, 2), (key2390, -1), (key2392, -1), (key2480, -1), (key2543, -1), (key2522, -1), (key2563, -1), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, 1), (key2381, 1), (key2472, 1), (key2538, 1), (key2506, 1), (key2554, 1)]

def rawRow4431 : Integer.Sparse Key := [(key2472, -2), (key2506, -2), (key2503, -2), (key2482, 2), (key2480, 2), (key2522, 2), (key2406, 2), (key2440, 2), (key2437, 2), (key2392, -1), (key2390, -1), (key2543, -1), (key2480, -1), (key2563, -1), (key2522, -1), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, 1), (key2378, 1), (key2538, 1), (key2472, 1), (key2554, 1), (key2506, 1)]

def rawRow4432 : Integer.Sparse Key := [(key2503, -2), (key2472, -2), (key2506, -2), (key2480, 2), (key2522, 2), (key2482, 2), (key2437, 2), (key2406, 2), (key2440, 2), (key2480, -1), (key2522, -1), (key2390, -1), (key2563, -1), (key2392, -1), (key2543, -1), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, 1), (key2506, 1), (key2378, 1), (key2554, 1), (key2381, 1), (key2538, 1)]

def rawRow4433 : Integer.Sparse Key := [(key2503, -2), (key2506, -2), (key2472, -2), (key2522, 2), (key2480, 2), (key2482, 2), (key2437, 2), (key2440, 2), (key2406, 2), (key2522, -1), (key2480, -1), (key2563, -1), (key2390, -1), (key2543, -1), (key2392, -1), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, 1), (key2472, 1), (key2554, 1), (key2378, 1), (key2538, 1), (key2381, 1)]

def rawRow4434 : Integer.Sparse Key := [(key2506, -2), (key2472, -2), (key2503, -2), (key2482, 2), (key2522, 2), (key2480, 2), (key2440, 2), (key2406, 2), (key2437, 2), (key2543, -1), (key2563, -1), (key2392, -1), (key2522, -1), (key2390, -1), (key2480, -1), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, 1), (key2554, 1), (key2381, 1), (key2506, 1), (key2378, 1), (key2472, 1)]

def rawRow4435 : Integer.Sparse Key := [(key2506, -2), (key2503, -2), (key2472, -2), (key2522, 2), (key2482, 2), (key2480, 2), (key2440, 2), (key2437, 2), (key2406, 2), (key2563, -1), (key2543, -1), (key2522, -1), (key2392, -1), (key2480, -1), (key2390, -1), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, 1), (key2538, 1), (key2506, 1), (key2381, 1), (key2472, 1), (key2378, 1)]

def rawRow4436 : Integer.Sparse Key := [(key2482, -2), (key2506, -2), (key2522, -2), (key2472, 2), (key2480, 2), (key2503, 2), (key2543, 2), (key2554, 2), (key2563, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2480, -1), (key2437, -1), (key2503, -1), (key2538, -2), (key2543, -2), (key2554, -2), (key2381, 1), (key2392, 1), (key2409, 1), (key2482, 1), (key2440, 1), (key2506, 1)]

def rawRow4437 : Integer.Sparse Key := [(key2482, -2), (key2522, -2), (key2506, -2), (key2480, 2), (key2472, 2), (key2503, 2), (key2543, 2), (key2563, 2), (key2554, 2), (key2390, -1), (key2378, -1), (key2480, -1), (key2406, -1), (key2503, -1), (key2437, -1), (key2543, -2), (key2538, -2), (key2554, -2), (key2392, 1), (key2381, 1), (key2482, 1), (key2409, 1), (key2506, 1), (key2440, 1)]

def rawRow4438 : Integer.Sparse Key := [(key2506, -2), (key2482, -2), (key2522, -2), (key2472, 2), (key2503, 2), (key2480, 2), (key2554, 2), (key2543, 2), (key2563, 2), (key2406, -1), (key2437, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2538, -2), (key2554, -2), (key2543, -2), (key2409, 1), (key2440, 1), (key2381, 1), (key2506, 1), (key2392, 1), (key2482, 1)]

def rawRow4439 : Integer.Sparse Key := [(key2506, -2), (key2522, -2), (key2482, -2), (key2503, 2), (key2472, 2), (key2480, 2), (key2554, 2), (key2563, 2), (key2543, 2), (key2437, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2480, -1), (key2390, -1), (key2554, -2), (key2538, -2), (key2543, -2), (key2440, 1), (key2409, 1), (key2506, 1), (key2381, 1), (key2482, 1), (key2392, 1)]

def rawRow4440 : Integer.Sparse Key := [(key2522, -2), (key2482, -2), (key2506, -2), (key2480, 2), (key2503, 2), (key2472, 2), (key2563, 2), (key2543, 2), (key2554, 2), (key2480, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2378, -1), (key2406, -1), (key2543, -2), (key2554, -2), (key2538, -2), (key2482, 1), (key2506, 1), (key2392, 1), (key2440, 1), (key2381, 1), (key2409, 1)]

def rawRow4441 : Integer.Sparse Key := [(key2522, -2), (key2506, -2), (key2482, -2), (key2503, 2), (key2480, 2), (key2472, 2), (key2563, 2), (key2554, 2), (key2543, 2), (key2503, -1), (key2480, -1), (key2437, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2554, -2), (key2543, -2), (key2538, -2), (key2506, 1), (key2482, 1), (key2440, 1), (key2392, 1), (key2409, 1), (key2381, 1)]

def rawRow4442 : Integer.Sparse Key := [(key2543, -2), (key2554, -2), (key2563, -2), (key2538, 2), (key2543, 2), (key2554, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2381, -1), (key2392, -1), (key2409, -1), (key2482, -1), (key2440, -1), (key2506, -1), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, 1), (key2390, 1), (key2406, 1), (key2480, 1), (key2437, 1), (key2503, 1)]

def rawRow4443 : Integer.Sparse Key := [(key2543, -2), (key2563, -2), (key2554, -2), (key2543, 2), (key2538, 2), (key2554, 2), (key2482, 2), (key2522, 2), (key2506, 2), (key2392, -1), (key2381, -1), (key2482, -1), (key2409, -1), (key2506, -1), (key2440, -1), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, 1), (key2378, 1), (key2480, 1), (key2406, 1), (key2503, 1), (key2437, 1)]

def rawRow4444 : Integer.Sparse Key := [(key2554, -2), (key2543, -2), (key2563, -2), (key2538, 2), (key2554, 2), (key2543, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2409, -1), (key2440, -1), (key2381, -1), (key2506, -1), (key2392, -1), (key2482, -1), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, 1), (key2437, 1), (key2378, 1), (key2503, 1), (key2390, 1), (key2480, 1)]

def rawRow4445 : Integer.Sparse Key := [(key2554, -2), (key2563, -2), (key2543, -2), (key2554, 2), (key2538, 2), (key2543, 2), (key2506, 2), (key2522, 2), (key2482, 2), (key2440, -1), (key2409, -1), (key2506, -1), (key2381, -1), (key2482, -1), (key2392, -1), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, 1), (key2406, 1), (key2503, 1), (key2378, 1), (key2480, 1), (key2390, 1)]

def rawRow4446 : Integer.Sparse Key := [(key2563, -2), (key2543, -2), (key2554, -2), (key2543, 2), (key2554, 2), (key2538, 2), (key2522, 2), (key2482, 2), (key2506, 2), (key2482, -1), (key2506, -1), (key2392, -1), (key2440, -1), (key2381, -1), (key2409, -1), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, 1), (key2503, 1), (key2390, 1), (key2437, 1), (key2378, 1), (key2406, 1)]

def rawRow4447 : Integer.Sparse Key := [(key2563, -2), (key2554, -2), (key2543, -2), (key2554, 2), (key2543, 2), (key2538, 2), (key2522, 2), (key2506, 2), (key2482, 2), (key2506, -1), (key2482, -1), (key2440, -1), (key2392, -1), (key2409, -1), (key2381, -1), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, 1), (key2480, 1), (key2437, 1), (key2390, 1), (key2406, 1), (key2378, 1)]

def rawRow4448 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2613, 2), (key2806, 2), (key2949, 2), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1), (key2629, -1), (key2647, -1), (key2783, -1), (key2937, -1), (key2894, -1), (key2973, -1), (key2637, -2), (key2857, -2), (key2975, -2), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1)]

def rawRow4449 : Integer.Sparse Key := [(key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2613, 2), (key2949, 2), (key2806, 2), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1), (key2647, -1), (key2629, -1), (key2937, -1), (key2783, -1), (key2973, -1), (key2894, -1), (key2637, -2), (key2975, -2), (key2857, -2), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1)]

def rawRow4450 : Integer.Sparse Key := [(key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2806, 2), (key2613, 2), (key2949, 2), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1), (key2783, -1), (key2894, -1), (key2629, -1), (key2973, -1), (key2647, -1), (key2937, -1), (key2857, -2), (key2637, -2), (key2975, -2), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1)]

def rawRow4451 : Integer.Sparse Key := [(key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2806, 2), (key2949, 2), (key2613, 2), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1), (key2894, -1), (key2783, -1), (key2973, -1), (key2629, -1), (key2937, -1), (key2647, -1), (key2857, -2), (key2975, -2), (key2637, -2), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1)]

def rawRow4452 : Integer.Sparse Key := [(key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2949, 2), (key2613, 2), (key2806, 2), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1), (key2937, -1), (key2973, -1), (key2647, -1), (key2894, -1), (key2629, -1), (key2783, -1), (key2975, -2), (key2637, -2), (key2857, -2), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1)]

def rawRow4453 : Integer.Sparse Key := [(key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2949, 2), (key2806, 2), (key2613, 2), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1), (key2973, -1), (key2937, -1), (key2894, -1), (key2647, -1), (key2783, -1), (key2629, -1), (key2975, -2), (key2857, -2), (key2637, -2), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

def rawRow4454 : Integer.Sparse Key := [(key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2637, 2), (key2857, 2), (key2975, 2), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2637, -1), (key2652, -1), (key2791, -1), (key2942, -1), (key2896, -1), (key2975, -1), (key2613, -2), (key2806, -2), (key2949, -2), (key2629, 1), (key2647, 1), (key2783, 1), (key2937, 1), (key2894, 1), (key2973, 1)]

def rawRow4455 : Integer.Sparse Key := [(key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2637, 2), (key2975, 2), (key2857, 2), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2652, -1), (key2637, -1), (key2942, -1), (key2791, -1), (key2975, -1), (key2896, -1), (key2613, -2), (key2949, -2), (key2806, -2), (key2647, 1), (key2629, 1), (key2937, 1), (key2783, 1), (key2973, 1), (key2894, 1)]

def rawRow4456 : Integer.Sparse Key := [(key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2857, 2), (key2637, 2), (key2975, 2), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2791, -1), (key2896, -1), (key2637, -1), (key2975, -1), (key2652, -1), (key2942, -1), (key2806, -2), (key2613, -2), (key2949, -2), (key2783, 1), (key2894, 1), (key2629, 1), (key2973, 1), (key2647, 1), (key2937, 1)]

def rawRow4457 : Integer.Sparse Key := [(key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2857, 2), (key2975, 2), (key2637, 2), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2896, -1), (key2791, -1), (key2975, -1), (key2637, -1), (key2942, -1), (key2652, -1), (key2806, -2), (key2949, -2), (key2613, -2), (key2894, 1), (key2783, 1), (key2973, 1), (key2629, 1), (key2937, 1), (key2647, 1)]

def rawRow4458 : Integer.Sparse Key := [(key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2975, 2), (key2637, 2), (key2857, 2), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2942, -1), (key2975, -1), (key2652, -1), (key2896, -1), (key2637, -1), (key2791, -1), (key2949, -2), (key2613, -2), (key2806, -2), (key2937, 1), (key2973, 1), (key2647, 1), (key2894, 1), (key2629, 1), (key2783, 1)]

def rawRow4459 : Integer.Sparse Key := [(key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2975, 2), (key2857, 2), (key2637, 2), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2975, -1), (key2942, -1), (key2896, -1), (key2652, -1), (key2791, -1), (key2637, -1), (key2949, -2), (key2806, -2), (key2613, -2), (key2973, 1), (key2937, 1), (key2894, 1), (key2647, 1), (key2783, 1), (key2629, 1)]

def rawRow4460 : Integer.Sparse Key := [(key2629, -1), (key2637, -1), (key2703, -1), (key2857, -1), (key2723, -1), (key2867, -1), (key2625, 2), (key2699, 2), (key2852, 2), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2609, -1), (key2625, -1), (key2664, -1), (key2779, -1), (key2699, -1), (key2802, -1), (key2647, -2), (key2736, -2), (key2894, -2), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1)]

def rawRow4461 : Integer.Sparse Key := [(key2637, -1), (key2629, -1), (key2857, -1), (key2703, -1), (key2867, -1), (key2723, -1), (key2625, 2), (key2852, 2), (key2699, 2), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2625, -1), (key2609, -1), (key2779, -1), (key2664, -1), (key2802, -1), (key2699, -1), (key2647, -2), (key2894, -2), (key2736, -2), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1)]

def rawRow4462 : Integer.Sparse Key := [(key2703, -1), (key2723, -1), (key2629, -1), (key2867, -1), (key2637, -1), (key2857, -1), (key2699, 2), (key2625, 2), (key2852, 2), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2664, -1), (key2699, -1), (key2609, -1), (key2802, -1), (key2625, -1), (key2779, -1), (key2736, -2), (key2647, -2), (key2894, -2), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1)]

def rawRow4463 : Integer.Sparse Key := [(key2723, -1), (key2703, -1), (key2867, -1), (key2629, -1), (key2857, -1), (key2637, -1), (key2699, 2), (key2852, 2), (key2625, 2), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2699, -1), (key2664, -1), (key2802, -1), (key2609, -1), (key2779, -1), (key2625, -1), (key2736, -2), (key2894, -2), (key2647, -2), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1)]

def rawRow4464 : Integer.Sparse Key := [(key2857, -1), (key2867, -1), (key2637, -1), (key2723, -1), (key2629, -1), (key2703, -1), (key2852, 2), (key2625, 2), (key2699, 2), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2779, -1), (key2802, -1), (key2625, -1), (key2699, -1), (key2609, -1), (key2664, -1), (key2894, -2), (key2647, -2), (key2736, -2), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1)]

def rawRow4465 : Integer.Sparse Key := [(key2867, -1), (key2857, -1), (key2723, -1), (key2637, -1), (key2703, -1), (key2629, -1), (key2852, 2), (key2699, 2), (key2625, 2), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2802, -1), (key2779, -1), (key2699, -1), (key2625, -1), (key2664, -1), (key2609, -1), (key2894, -2), (key2736, -2), (key2647, -2), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1)]

def rawRow4466 : Integer.Sparse Key := [(key2647, -1), (key2652, -1), (key2736, -1), (key2896, -1), (key2746, -1), (key2903, -1), (key2647, 2), (key2736, 2), (key2894, 2), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, -1), (key2629, -1), (key2668, -1), (key2783, -1), (key2703, -1), (key2806, -1), (key2625, -2), (key2699, -2), (key2852, -2), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1)]

def rawRow4467 : Integer.Sparse Key := [(key2652, -1), (key2647, -1), (key2896, -1), (key2736, -1), (key2903, -1), (key2746, -1), (key2647, 2), (key2894, 2), (key2736, 2), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2629, -1), (key2613, -1), (key2783, -1), (key2668, -1), (key2806, -1), (key2703, -1), (key2625, -2), (key2852, -2), (key2699, -2), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1)]

def rawRow4468 : Integer.Sparse Key := [(key2736, -1), (key2746, -1), (key2647, -1), (key2903, -1), (key2652, -1), (key2896, -1), (key2736, 2), (key2647, 2), (key2894, 2), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, -1), (key2703, -1), (key2613, -1), (key2806, -1), (key2629, -1), (key2783, -1), (key2699, -2), (key2625, -2), (key2852, -2), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1)]

def rawRow4469 : Integer.Sparse Key := [(key2746, -1), (key2736, -1), (key2903, -1), (key2647, -1), (key2896, -1), (key2652, -1), (key2736, 2), (key2894, 2), (key2647, 2), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2703, -1), (key2668, -1), (key2806, -1), (key2613, -1), (key2783, -1), (key2629, -1), (key2699, -2), (key2852, -2), (key2625, -2), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1)]

def rawRow4470 : Integer.Sparse Key := [(key2896, -1), (key2903, -1), (key2652, -1), (key2746, -1), (key2647, -1), (key2736, -1), (key2894, 2), (key2647, 2), (key2736, 2), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2783, -1), (key2806, -1), (key2629, -1), (key2703, -1), (key2613, -1), (key2668, -1), (key2852, -2), (key2625, -2), (key2699, -2), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1)]

def rawRow4471 : Integer.Sparse Key := [(key2903, -1), (key2896, -1), (key2746, -1), (key2652, -1), (key2736, -1), (key2647, -1), (key2894, 2), (key2736, 2), (key2647, 2), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2806, -1), (key2783, -1), (key2703, -1), (key2629, -1), (key2668, -1), (key2613, -1), (key2852, -2), (key2699, -2), (key2625, -2), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1)]

def rawRow4472 : Integer.Sparse Key := [(key2698, -2), (key2701, -2), (key2722, -2), (key2666, 2), (key2701, 2), (key2734, 2), (key2801, 2), (key2804, 2), (key2825, 2), (key2611, -2), (key2804, -2), (key2825, -2), (key2734, -2), (key2892, -2), (key2895, -2), (key2645, 2), (key2892, 2), (key2902, 2)]

def rawRow4473 : Integer.Sparse Key := [(key2701, -2), (key2698, -2), (key2722, -2), (key2666, 2), (key2734, 2), (key2701, 2), (key2804, 2), (key2801, 2), (key2825, 2), (key2611, -2), (key2825, -2), (key2804, -2), (key2734, -2), (key2895, -2), (key2892, -2), (key2645, 2), (key2902, 2), (key2892, 2)]

def rawRow4474 : Integer.Sparse Key := [(key2698, -2), (key2722, -2), (key2701, -2), (key2701, 2), (key2666, 2), (key2734, 2), (key2801, 2), (key2825, 2), (key2804, 2), (key2804, -2), (key2611, -2), (key2825, -2), (key2892, -2), (key2734, -2), (key2895, -2), (key2892, 2), (key2645, 2), (key2902, 2)]

def rawRow4475 : Integer.Sparse Key := [(key2722, -2), (key2698, -2), (key2701, -2), (key2701, 2), (key2734, 2), (key2666, 2), (key2825, 2), (key2801, 2), (key2804, 2), (key2804, -2), (key2825, -2), (key2611, -2), (key2892, -2), (key2895, -2), (key2734, -2), (key2892, 2), (key2902, 2), (key2645, 2)]

def rawRow4476 : Integer.Sparse Key := [(key2701, -2), (key2722, -2), (key2698, -2), (key2734, 2), (key2666, 2), (key2701, 2), (key2804, 2), (key2825, 2), (key2801, 2), (key2825, -2), (key2611, -2), (key2804, -2), (key2895, -2), (key2734, -2), (key2892, -2), (key2902, 2), (key2645, 2), (key2892, 2)]

def rawRow4477 : Integer.Sparse Key := [(key2722, -2), (key2701, -2), (key2698, -2), (key2734, 2), (key2701, 2), (key2666, 2), (key2825, 2), (key2804, 2), (key2801, 2), (key2825, -2), (key2804, -2), (key2611, -2), (key2895, -2), (key2892, -2), (key2734, -2), (key2902, 2), (key2892, 2), (key2645, 2)]

def rawRow4478 : Integer.Sparse Key := [(key2801, -2), (key2804, -2), (key2825, -2), (key2790, 2), (key2856, 2), (key2895, 2), (key2698, 2), (key2701, 2), (key2722, 2), (key2636, -2), (key2856, -2), (key2974, -2), (key2666, -2), (key2781, -2), (key2790, -2), (key2611, 2), (key2804, 2), (key2825, 2)]

def rawRow4479 : Integer.Sparse Key := [(key2804, -2), (key2801, -2), (key2825, -2), (key2790, 2), (key2895, 2), (key2856, 2), (key2701, 2), (key2698, 2), (key2722, 2), (key2636, -2), (key2974, -2), (key2856, -2), (key2666, -2), (key2790, -2), (key2781, -2), (key2611, 2), (key2825, 2), (key2804, 2)]

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

def rawRow4480 : Integer.Sparse Key := [(key2801, -2), (key2825, -2), (key2804, -2), (key2856, 2), (key2790, 2), (key2895, 2), (key2698, 2), (key2722, 2), (key2701, 2), (key2856, -2), (key2636, -2), (key2974, -2), (key2781, -2), (key2666, -2), (key2790, -2), (key2804, 2), (key2611, 2), (key2825, 2)]

def rawRow4481 : Integer.Sparse Key := [(key2825, -2), (key2801, -2), (key2804, -2), (key2856, 2), (key2895, 2), (key2790, 2), (key2722, 2), (key2698, 2), (key2701, 2), (key2856, -2), (key2974, -2), (key2636, -2), (key2781, -2), (key2790, -2), (key2666, -2), (key2804, 2), (key2825, 2), (key2611, 2)]

def rawRow4482 : Integer.Sparse Key := [(key2804, -2), (key2825, -2), (key2801, -2), (key2895, 2), (key2790, 2), (key2856, 2), (key2701, 2), (key2722, 2), (key2698, 2), (key2974, -2), (key2636, -2), (key2856, -2), (key2790, -2), (key2666, -2), (key2781, -2), (key2825, 2), (key2611, 2), (key2804, 2)]

def rawRow4483 : Integer.Sparse Key := [(key2825, -2), (key2804, -2), (key2801, -2), (key2895, 2), (key2856, 2), (key2790, 2), (key2722, 2), (key2701, 2), (key2698, 2), (key2974, -2), (key2856, -2), (key2636, -2), (key2790, -2), (key2781, -2), (key2666, -2), (key2825, 2), (key2804, 2), (key2611, 2)]

def rawRow4484 : Integer.Sparse Key := [(key2892, -2), (key2895, -2), (key2902, -2), (key2778, 2), (key2801, 2), (key2851, 2), (key2971, 2), (key2974, 2), (key2981, 2), (key2624, -2), (key2698, -2), (key2851, -2), (key2722, -2), (key2825, -2), (key2866, -2), (key2636, 2), (key2790, 2), (key2856, 2)]

def rawRow4485 : Integer.Sparse Key := [(key2895, -2), (key2892, -2), (key2902, -2), (key2778, 2), (key2851, 2), (key2801, 2), (key2974, 2), (key2971, 2), (key2981, 2), (key2624, -2), (key2851, -2), (key2698, -2), (key2722, -2), (key2866, -2), (key2825, -2), (key2636, 2), (key2856, 2), (key2790, 2)]

def rawRow4486 : Integer.Sparse Key := [(key2892, -2), (key2902, -2), (key2895, -2), (key2801, 2), (key2778, 2), (key2851, 2), (key2971, 2), (key2981, 2), (key2974, 2), (key2698, -2), (key2624, -2), (key2851, -2), (key2825, -2), (key2722, -2), (key2866, -2), (key2790, 2), (key2636, 2), (key2856, 2)]

def rawRow4487 : Integer.Sparse Key := [(key2902, -2), (key2892, -2), (key2895, -2), (key2801, 2), (key2851, 2), (key2778, 2), (key2981, 2), (key2971, 2), (key2974, 2), (key2698, -2), (key2851, -2), (key2624, -2), (key2825, -2), (key2866, -2), (key2722, -2), (key2790, 2), (key2856, 2), (key2636, 2)]

def rawRow4488 : Integer.Sparse Key := [(key2895, -2), (key2902, -2), (key2892, -2), (key2851, 2), (key2778, 2), (key2801, 2), (key2974, 2), (key2981, 2), (key2971, 2), (key2851, -2), (key2624, -2), (key2698, -2), (key2866, -2), (key2722, -2), (key2825, -2), (key2856, 2), (key2636, 2), (key2790, 2)]

def rawRow4489 : Integer.Sparse Key := [(key2902, -2), (key2895, -2), (key2892, -2), (key2851, 2), (key2801, 2), (key2778, 2), (key2981, 2), (key2974, 2), (key2971, 2), (key2851, -2), (key2698, -2), (key2624, -2), (key2866, -2), (key2825, -2), (key2722, -2), (key2856, 2), (key2790, 2), (key2636, 2)]

def rawRow4490 : Integer.Sparse Key := [(key2971, -2), (key2974, -2), (key2981, -2), (key2935, 2), (key2947, 2), (key2971, 2), (key2892, 2), (key2895, 2), (key2902, 2), (key2645, -2), (key2734, -2), (key2892, -2), (key2778, -2), (key2801, -2), (key2851, -2), (key2624, 2), (key2698, 2), (key2851, 2)]

def rawRow4491 : Integer.Sparse Key := [(key2974, -2), (key2971, -2), (key2981, -2), (key2935, 2), (key2971, 2), (key2947, 2), (key2895, 2), (key2892, 2), (key2902, 2), (key2645, -2), (key2892, -2), (key2734, -2), (key2778, -2), (key2851, -2), (key2801, -2), (key2624, 2), (key2851, 2), (key2698, 2)]

def rawRow4492 : Integer.Sparse Key := [(key2971, -2), (key2981, -2), (key2974, -2), (key2947, 2), (key2935, 2), (key2971, 2), (key2892, 2), (key2902, 2), (key2895, 2), (key2734, -2), (key2645, -2), (key2892, -2), (key2801, -2), (key2778, -2), (key2851, -2), (key2698, 2), (key2624, 2), (key2851, 2)]

def rawRow4493 : Integer.Sparse Key := [(key2981, -2), (key2971, -2), (key2974, -2), (key2947, 2), (key2971, 2), (key2935, 2), (key2902, 2), (key2892, 2), (key2895, 2), (key2734, -2), (key2892, -2), (key2645, -2), (key2801, -2), (key2851, -2), (key2778, -2), (key2698, 2), (key2851, 2), (key2624, 2)]

def rawRow4494 : Integer.Sparse Key := [(key2974, -2), (key2981, -2), (key2971, -2), (key2971, 2), (key2935, 2), (key2947, 2), (key2895, 2), (key2902, 2), (key2892, 2), (key2892, -2), (key2645, -2), (key2734, -2), (key2851, -2), (key2778, -2), (key2801, -2), (key2851, 2), (key2624, 2), (key2698, 2)]

def rawRow4495 : Integer.Sparse Key := [(key2981, -2), (key2974, -2), (key2971, -2), (key2971, 2), (key2947, 2), (key2935, 2), (key2902, 2), (key2895, 2), (key2892, 2), (key2892, -2), (key2734, -2), (key2645, -2), (key2851, -2), (key2801, -2), (key2778, -2), (key2851, 2), (key2698, 2), (key2624, 2)]

def rawRow4502 : Integer.Sparse Key := [(key1295, -1), (key1295, -1), (key1572, -1), (key1572, -1), (key1591, -1), (key1591, -1), (key1291, 2), (key1568, 2), (key1568, 2), (key1336, 1), (key1336, 1), (key1654, 1), (key1654, 1), (key1665, 1), (key1665, 1), (key1311, -1), (key1311, -1), (key1541, -1), (key1541, -1), (key1617, -1), (key1617, -1), (key1343, -2), (key1657, -2), (key1657, -2), (key1324, 1), (key1324, 1), (key1554, 1), (key1554, 1), (key1622, 1), (key1622, 1)]

def rawRow4503 : Integer.Sparse Key := [(key1572, -1), (key1591, -1), (key1295, -1), (key1591, -1), (key1295, -1), (key1572, -1), (key1568, 2), (key1291, 2), (key1568, 2), (key1654, 1), (key1665, 1), (key1336, 1), (key1665, 1), (key1336, 1), (key1654, 1), (key1541, -1), (key1617, -1), (key1311, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1657, -2), (key1343, -2), (key1657, -2), (key1554, 1), (key1622, 1), (key1324, 1), (key1622, 1), (key1324, 1), (key1554, 1)]

def rawRow4504 : Integer.Sparse Key := [(key1591, -1), (key1572, -1), (key1591, -1), (key1295, -1), (key1572, -1), (key1295, -1), (key1568, 2), (key1568, 2), (key1291, 2), (key1665, 1), (key1654, 1), (key1665, 1), (key1336, 1), (key1654, 1), (key1336, 1), (key1617, -1), (key1541, -1), (key1617, -1), (key1311, -1), (key1541, -1), (key1311, -1), (key1657, -2), (key1657, -2), (key1343, -2), (key1622, 1), (key1554, 1), (key1622, 1), (key1324, 1), (key1554, 1), (key1324, 1)]

def rawRow4517 : Integer.Sparse Key := [(key1336, -1), (key1336, -1), (key1654, -1), (key1654, -1), (key1665, -1), (key1665, -1), (key1343, 2), (key1657, 2), (key1657, 2), (key1295, 1), (key1295, 1), (key1572, 1), (key1572, 1), (key1591, 1), (key1591, 1), (key1324, -1), (key1324, -1), (key1554, -1), (key1554, -1), (key1622, -1), (key1622, -1), (key1291, -2), (key1568, -2), (key1568, -2), (key1311, 1), (key1311, 1), (key1541, 1), (key1541, 1), (key1617, 1), (key1617, 1)]

def rawRow4518 : Integer.Sparse Key := [(key1654, -1), (key1665, -1), (key1336, -1), (key1665, -1), (key1336, -1), (key1654, -1), (key1657, 2), (key1343, 2), (key1657, 2), (key1572, 1), (key1591, 1), (key1295, 1), (key1591, 1), (key1295, 1), (key1572, 1), (key1554, -1), (key1622, -1), (key1324, -1), (key1622, -1), (key1324, -1), (key1554, -1), (key1568, -2), (key1291, -2), (key1568, -2), (key1541, 1), (key1617, 1), (key1311, 1), (key1617, 1), (key1311, 1), (key1541, 1)]

def rawRow4519 : Integer.Sparse Key := [(key1665, -1), (key1654, -1), (key1665, -1), (key1336, -1), (key1654, -1), (key1336, -1), (key1657, 2), (key1657, 2), (key1343, 2), (key1591, 1), (key1572, 1), (key1591, 1), (key1295, 1), (key1572, 1), (key1295, 1), (key1622, -1), (key1554, -1), (key1622, -1), (key1324, -1), (key1554, -1), (key1324, -1), (key1568, -2), (key1568, -2), (key1291, -2), (key1617, 1), (key1541, 1), (key1617, 1), (key1311, 1), (key1541, 1), (key1311, 1)]

def rawRow4526 : Integer.Sparse Key := [(key2608, -1), (key2611, -1), (key2801, -1), (key2825, -1), (key2947, -1), (key2958, -1), (key2611, 2), (key2804, 2), (key2825, 2), (key2624, 1), (key2627, 1), (key2851, 1), (key2866, 1), (key2971, 1), (key2981, 1), (key2627, -1), (key2636, -1), (key2701, -1), (key2722, -1), (key2856, -1), (key2866, -1), (key2645, -2), (key2892, -2), (key2902, -2), (key2645, 1), (key2651, 1), (key2734, 1), (key2745, 1), (key2895, 1), (key2902, 1)]

def rawRow4527 : Integer.Sparse Key := [(key2611, -1), (key2608, -1), (key2825, -1), (key2801, -1), (key2958, -1), (key2947, -1), (key2611, 2), (key2825, 2), (key2804, 2), (key2627, 1), (key2624, 1), (key2866, 1), (key2851, 1), (key2981, 1), (key2971, 1), (key2636, -1), (key2627, -1), (key2722, -1), (key2701, -1), (key2866, -1), (key2856, -1), (key2645, -2), (key2902, -2), (key2892, -2), (key2651, 1), (key2645, 1), (key2745, 1), (key2734, 1), (key2902, 1), (key2895, 1)]

def rawRow4528 : Integer.Sparse Key := [(key2801, -1), (key2825, -1), (key2608, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2804, 2), (key2611, 2), (key2825, 2), (key2851, 1), (key2971, 1), (key2624, 1), (key2981, 1), (key2627, 1), (key2866, 1), (key2701, -1), (key2856, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2892, -2), (key2645, -2), (key2902, -2), (key2734, 1), (key2895, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2745, 1)]

def rawRow4529 : Integer.Sparse Key := [(key2825, -1), (key2801, -1), (key2958, -1), (key2608, -1), (key2825, -1), (key2611, -1), (key2804, 2), (key2825, 2), (key2611, 2), (key2971, 1), (key2851, 1), (key2981, 1), (key2624, 1), (key2866, 1), (key2627, 1), (key2856, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2722, -1), (key2636, -1), (key2892, -2), (key2902, -2), (key2645, -2), (key2895, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2745, 1), (key2651, 1)]

def rawRow4530 : Integer.Sparse Key := [(key2947, -1), (key2958, -1), (key2611, -1), (key2825, -1), (key2608, -1), (key2801, -1), (key2825, 2), (key2611, 2), (key2804, 2), (key2866, 1), (key2981, 1), (key2627, 1), (key2971, 1), (key2624, 1), (key2851, 1), (key2722, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2627, -1), (key2701, -1), (key2902, -2), (key2645, -2), (key2892, -2), (key2745, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2645, 1), (key2734, 1)]

def rawRow4531 : Integer.Sparse Key := [(key2958, -1), (key2947, -1), (key2825, -1), (key2611, -1), (key2801, -1), (key2608, -1), (key2825, 2), (key2804, 2), (key2611, 2), (key2981, 1), (key2866, 1), (key2971, 1), (key2627, 1), (key2851, 1), (key2624, 1), (key2866, -1), (key2722, -1), (key2856, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2902, -2), (key2892, -2), (key2645, -2), (key2902, 1), (key2745, 1), (key2895, 1), (key2651, 1), (key2734, 1), (key2645, 1)]

def rawRow4532 : Integer.Sparse Key := [(key2611, -1), (key2611, -1), (key2804, -1), (key2804, -1), (key2825, -1), (key2825, -1), (key2608, 2), (key2801, 2), (key2801, 2), (key2636, 1), (key2636, 1), (key2856, 1), (key2856, 1), (key2974, 1), (key2974, 1), (key2624, -1), (key2624, -1), (key2698, -1), (key2698, -1), (key2851, -1), (key2851, -1), (key2651, -2), (key2895, -2), (key2895, -2), (key2645, 1), (key2645, 1), (key2734, 1), (key2734, 1), (key2892, 1), (key2892, 1)]

def rawRow4533 : Integer.Sparse Key := [(key2804, -1), (key2825, -1), (key2611, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2801, 2), (key2608, 2), (key2801, 2), (key2856, 1), (key2974, 1), (key2636, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2698, -1), (key2851, -1), (key2624, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2895, -2), (key2651, -2), (key2895, -2), (key2734, 1), (key2892, 1), (key2645, 1), (key2892, 1), (key2645, 1), (key2734, 1)]

def rawRow4534 : Integer.Sparse Key := [(key2825, -1), (key2804, -1), (key2825, -1), (key2611, -1), (key2804, -1), (key2611, -1), (key2801, 2), (key2801, 2), (key2608, 2), (key2974, 1), (key2856, 1), (key2974, 1), (key2636, 1), (key2856, 1), (key2636, 1), (key2851, -1), (key2698, -1), (key2851, -1), (key2624, -1), (key2698, -1), (key2624, -1), (key2895, -2), (key2895, -2), (key2651, -2), (key2892, 1), (key2734, 1), (key2892, 1), (key2645, 1), (key2734, 1), (key2645, 1)]

def rawRow4535 : Integer.Sparse Key := [(key2624, -1), (key2627, -1), (key2851, -1), (key2971, -1), (key2866, -1), (key2981, -1), (key2636, 2), (key2856, 2), (key2974, 2), (key2608, 1), (key2611, 1), (key2801, 1), (key2825, 1), (key2947, 1), (key2958, 1), (key2645, -1), (key2651, -1), (key2734, -1), (key2745, -1), (key2895, -1), (key2902, -1), (key2611, -2), (key2804, -2), (key2825, -2), (key2627, 1), (key2636, 1), (key2701, 1), (key2722, 1), (key2856, 1), (key2866, 1)]

def rawRow4536 : Integer.Sparse Key := [(key2627, -1), (key2624, -1), (key2971, -1), (key2851, -1), (key2981, -1), (key2866, -1), (key2636, 2), (key2974, 2), (key2856, 2), (key2611, 1), (key2608, 1), (key2825, 1), (key2801, 1), (key2958, 1), (key2947, 1), (key2651, -1), (key2645, -1), (key2745, -1), (key2734, -1), (key2902, -1), (key2895, -1), (key2611, -2), (key2825, -2), (key2804, -2), (key2636, 1), (key2627, 1), (key2722, 1), (key2701, 1), (key2866, 1), (key2856, 1)]

def rawRow4537 : Integer.Sparse Key := [(key2851, -1), (key2866, -1), (key2624, -1), (key2981, -1), (key2627, -1), (key2971, -1), (key2856, 2), (key2636, 2), (key2974, 2), (key2801, 1), (key2825, 1), (key2608, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2734, -1), (key2895, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2804, -2), (key2611, -2), (key2825, -2), (key2701, 1), (key2856, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2722, 1)]

def rawRow4538 : Integer.Sparse Key := [(key2866, -1), (key2851, -1), (key2981, -1), (key2624, -1), (key2971, -1), (key2627, -1), (key2856, 2), (key2974, 2), (key2636, 2), (key2825, 1), (key2801, 1), (key2958, 1), (key2608, 1), (key2825, 1), (key2611, 1), (key2895, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2745, -1), (key2651, -1), (key2804, -2), (key2825, -2), (key2611, -2), (key2856, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2722, 1), (key2636, 1)]

def rawRow4539 : Integer.Sparse Key := [(key2971, -1), (key2981, -1), (key2627, -1), (key2866, -1), (key2624, -1), (key2851, -1), (key2974, 2), (key2636, 2), (key2856, 2), (key2947, 1), (key2958, 1), (key2611, 1), (key2825, 1), (key2608, 1), (key2801, 1), (key2745, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2645, -1), (key2734, -1), (key2825, -2), (key2611, -2), (key2804, -2), (key2722, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2627, 1), (key2701, 1)]

def rawRow4540 : Integer.Sparse Key := [(key2981, -1), (key2971, -1), (key2866, -1), (key2627, -1), (key2851, -1), (key2624, -1), (key2974, 2), (key2856, 2), (key2636, 2), (key2958, 1), (key2947, 1), (key2825, 1), (key2611, 1), (key2801, 1), (key2608, 1), (key2902, -1), (key2745, -1), (key2895, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2825, -2), (key2804, -2), (key2611, -2), (key2866, 1), (key2722, 1), (key2856, 1), (key2636, 1), (key2701, 1), (key2627, 1)]

def rawRow4541 : Integer.Sparse Key := [(key2627, -1), (key2636, -1), (key2701, -1), (key2856, -1), (key2722, -1), (key2866, -1), (key2624, 2), (key2698, 2), (key2851, 2), (key2645, 1), (key2651, 1), (key2734, 1), (key2895, 1), (key2745, 1), (key2902, 1), (key2608, -1), (key2624, -1), (key2663, -1), (key2698, -1), (key2778, -1), (key2801, -1), (key2636, -2), (key2790, -2), (key2856, -2), (key2611, 1), (key2627, 1), (key2666, 1), (key2701, 1), (key2781, 1), (key2804, 1)]

def rawRow4542 : Integer.Sparse Key := [(key2636, -1), (key2627, -1), (key2856, -1), (key2701, -1), (key2866, -1), (key2722, -1), (key2624, 2), (key2851, 2), (key2698, 2), (key2651, 1), (key2645, 1), (key2895, 1), (key2734, 1), (key2902, 1), (key2745, 1), (key2624, -1), (key2608, -1), (key2698, -1), (key2663, -1), (key2801, -1), (key2778, -1), (key2636, -2), (key2856, -2), (key2790, -2), (key2627, 1), (key2611, 1), (key2701, 1), (key2666, 1), (key2804, 1), (key2781, 1)]

def rawRow4543 : Integer.Sparse Key := [(key2701, -1), (key2722, -1), (key2627, -1), (key2866, -1), (key2636, -1), (key2856, -1), (key2698, 2), (key2624, 2), (key2851, 2), (key2734, 1), (key2745, 1), (key2645, 1), (key2902, 1), (key2651, 1), (key2895, 1), (key2663, -1), (key2698, -1), (key2608, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2790, -2), (key2636, -2), (key2856, -2), (key2666, 1), (key2781, 1), (key2611, 1), (key2804, 1), (key2627, 1), (key2701, 1)]

def rawRow4544 : Integer.Sparse Key := [(key2722, -1), (key2701, -1), (key2866, -1), (key2627, -1), (key2856, -1), (key2636, -1), (key2698, 2), (key2851, 2), (key2624, 2), (key2745, 1), (key2734, 1), (key2902, 1), (key2645, 1), (key2895, 1), (key2651, 1), (key2698, -1), (key2663, -1), (key2801, -1), (key2608, -1), (key2698, -1), (key2624, -1), (key2790, -2), (key2856, -2), (key2636, -2), (key2781, 1), (key2666, 1), (key2804, 1), (key2611, 1), (key2701, 1), (key2627, 1)]

def rawRow4545 : Integer.Sparse Key := [(key2856, -1), (key2866, -1), (key2636, -1), (key2722, -1), (key2627, -1), (key2701, -1), (key2851, 2), (key2624, 2), (key2698, 2), (key2895, 1), (key2902, 1), (key2651, 1), (key2745, 1), (key2645, 1), (key2734, 1), (key2778, -1), (key2801, -1), (key2624, -1), (key2698, -1), (key2608, -1), (key2663, -1), (key2856, -2), (key2636, -2), (key2790, -2), (key2701, 1), (key2804, 1), (key2627, 1), (key2781, 1), (key2611, 1), (key2666, 1)]

def rawRow4546 : Integer.Sparse Key := [(key2866, -1), (key2856, -1), (key2722, -1), (key2636, -1), (key2701, -1), (key2627, -1), (key2851, 2), (key2698, 2), (key2624, 2), (key2902, 1), (key2895, 1), (key2745, 1), (key2651, 1), (key2734, 1), (key2645, 1), (key2801, -1), (key2778, -1), (key2698, -1), (key2624, -1), (key2663, -1), (key2608, -1), (key2856, -2), (key2790, -2), (key2636, -2), (key2804, 1), (key2701, 1), (key2781, 1), (key2627, 1), (key2666, 1), (key2611, 1)]

def rawRow4547 : Integer.Sparse Key := [(key2645, -1), (key2645, -1), (key2892, -1), (key2892, -1), (key2902, -1), (key2902, -1), (key2651, 2), (key2895, 2), (key2895, 2), (key2611, 1), (key2611, 1), (key2804, 1), (key2804, 1), (key2825, 1), (key2825, 1), (key2636, -1), (key2636, -1), (key2790, -1), (key2790, -1), (key2856, -1), (key2856, -1), (key2608, -2), (key2801, -2), (key2801, -2), (key2624, 1), (key2624, 1), (key2698, 1), (key2698, 1), (key2851, 1), (key2851, 1)]

def rawRow4548 : Integer.Sparse Key := [(key2892, -1), (key2902, -1), (key2645, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2895, 2), (key2651, 2), (key2895, 2), (key2804, 1), (key2825, 1), (key2611, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2790, -1), (key2856, -1), (key2636, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2801, -2), (key2608, -2), (key2801, -2), (key2698, 1), (key2851, 1), (key2624, 1), (key2851, 1), (key2624, 1), (key2698, 1)]

def rawRow4549 : Integer.Sparse Key := [(key2902, -1), (key2892, -1), (key2902, -1), (key2645, -1), (key2892, -1), (key2645, -1), (key2895, 2), (key2895, 2), (key2651, 2), (key2825, 1), (key2804, 1), (key2825, 1), (key2611, 1), (key2804, 1), (key2611, 1), (key2856, -1), (key2790, -1), (key2856, -1), (key2636, -1), (key2790, -1), (key2636, -1), (key2801, -2), (key2801, -2), (key2608, -2), (key2851, 1), (key2698, 1), (key2851, 1), (key2624, 1), (key2698, 1), (key2624, 1)]

def rawRow4550 : Integer.Sparse Key := [(key2645, -1), (key2651, -1), (key2734, -1), (key2895, -1), (key2745, -1), (key2902, -1), (key2645, 2), (key2734, 2), (key2892, 2), (key2627, 1), (key2636, 1), (key2701, 1), (key2856, 1), (key2722, 1), (key2866, 1), (key2611, -1), (key2627, -1), (key2666, -1), (key2781, -1), (key2701, -1), (key2804, -1), (key2624, -2), (key2698, -2), (key2851, -2), (key2608, 1), (key2624, 1), (key2663, 1), (key2698, 1), (key2778, 1), (key2801, 1)]

def rawRow4551 : Integer.Sparse Key := [(key2651, -1), (key2645, -1), (key2895, -1), (key2734, -1), (key2902, -1), (key2745, -1), (key2645, 2), (key2892, 2), (key2734, 2), (key2636, 1), (key2627, 1), (key2856, 1), (key2701, 1), (key2866, 1), (key2722, 1), (key2627, -1), (key2611, -1), (key2781, -1), (key2666, -1), (key2804, -1), (key2701, -1), (key2624, -2), (key2851, -2), (key2698, -2), (key2624, 1), (key2608, 1), (key2698, 1), (key2663, 1), (key2801, 1), (key2778, 1)]

def rawRow4552 : Integer.Sparse Key := [(key2734, -1), (key2745, -1), (key2645, -1), (key2902, -1), (key2651, -1), (key2895, -1), (key2734, 2), (key2645, 2), (key2892, 2), (key2701, 1), (key2722, 1), (key2627, 1), (key2866, 1), (key2636, 1), (key2856, 1), (key2666, -1), (key2701, -1), (key2611, -1), (key2804, -1), (key2627, -1), (key2781, -1), (key2698, -2), (key2624, -2), (key2851, -2), (key2663, 1), (key2698, 1), (key2608, 1), (key2801, 1), (key2624, 1), (key2698, 1)]

def rawRow4553 : Integer.Sparse Key := [(key2745, -1), (key2734, -1), (key2902, -1), (key2645, -1), (key2895, -1), (key2651, -1), (key2734, 2), (key2892, 2), (key2645, 2), (key2722, 1), (key2701, 1), (key2866, 1), (key2627, 1), (key2856, 1), (key2636, 1), (key2701, -1), (key2666, -1), (key2804, -1), (key2611, -1), (key2781, -1), (key2627, -1), (key2698, -2), (key2851, -2), (key2624, -2), (key2698, 1), (key2663, 1), (key2801, 1), (key2608, 1), (key2698, 1), (key2624, 1)]

def rawRow4554 : Integer.Sparse Key := [(key2895, -1), (key2902, -1), (key2651, -1), (key2745, -1), (key2645, -1), (key2734, -1), (key2892, 2), (key2645, 2), (key2734, 2), (key2856, 1), (key2866, 1), (key2636, 1), (key2722, 1), (key2627, 1), (key2701, 1), (key2781, -1), (key2804, -1), (key2627, -1), (key2701, -1), (key2611, -1), (key2666, -1), (key2851, -2), (key2624, -2), (key2698, -2), (key2778, 1), (key2801, 1), (key2624, 1), (key2698, 1), (key2608, 1), (key2663, 1)]

def rawRow4555 : Integer.Sparse Key := [(key2902, -1), (key2895, -1), (key2745, -1), (key2651, -1), (key2734, -1), (key2645, -1), (key2892, 2), (key2734, 2), (key2645, 2), (key2866, 1), (key2856, 1), (key2722, 1), (key2636, 1), (key2701, 1), (key2627, 1), (key2804, -1), (key2781, -1), (key2701, -1), (key2627, -1), (key2666, -1), (key2611, -1), (key2851, -2), (key2698, -2), (key2624, -2), (key2801, 1), (key2778, 1), (key2698, 1), (key2624, 1), (key2663, 1), (key2608, 1)]

def rawRow4559 : Integer.Sparse Key := [(key1496, -2), (key1496, -2), (key1496, -2), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1492, 1), (key1728, 2), (key1728, 2), (key1728, 2), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1870, -1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1)]

def rawRow4566 : Integer.Sparse Key := [(key1728, -2), (key1728, -2), (key1728, -2), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1870, 1), (key1496, 2), (key1496, 2), (key1496, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1492, -1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1)]

def rawRow4573 : Integer.Sparse Key := [(key290, -6), (key281, 2), (key281, 2), (key281, 2), (key367, 6), (key350, -2), (key350, -2), (key350, -2), (key538, -2), (key538, -2), (key538, -2), (key516, 2), (key516, 2), (key516, 2)]

def rawRow4580 : Integer.Sparse Key := [(key367, -6), (key538, 2), (key538, 2), (key538, 2), (key290, 6), (key516, -2), (key516, -2), (key516, -2), (key281, -2), (key281, -2), (key281, -2), (key350, 2), (key350, 2), (key350, 2)]

def rawRow4587 : Integer.Sparse Key := [(key1376, -2), (key1376, -2), (key1376, -2), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1367, 1), (key1515, 2), (key1515, 2), (key1515, 2), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1743, -1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1)]

def rawRow4594 : Integer.Sparse Key := [(key1515, -2), (key1515, -2), (key1515, -2), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1743, 1), (key1376, 2), (key1376, 2), (key1376, 2), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1367, -1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1)]

def rawRow4601 : Integer.Sparse Key := [(key33, -2), (key33, -2), (key33, -2), (key29, 6), (key554, 2), (key554, 2), (key554, 2), (key495, -2), (key495, -2), (key495, -2), (key682, -6), (key665, 2), (key665, 2), (key665, 2)]

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

def rawRow4608 : Integer.Sparse Key := [(key175, -2), (key175, -2), (key175, -2), (key185, 6), (key33, 2), (key33, 2), (key33, 2), (key149, -2), (key149, -2), (key149, -2), (key223, -6), (key495, 2), (key495, 2), (key495, 2)]

def rawRow4615 : Integer.Sparse Key := [(key1373, -6), (key1361, 2), (key1361, 2), (key1361, 2), (key1512, 6), (key1487, -2), (key1487, -2), (key1487, -2), (key1740, -2), (key1740, -2), (key1740, -2), (key1722, 2), (key1722, 2), (key1722, 2)]

def rawRow4622 : Integer.Sparse Key := [(key1512, -6), (key1740, 2), (key1740, 2), (key1740, 2), (key1373, 6), (key1722, -2), (key1722, -2), (key1722, -2), (key1361, -2), (key1361, -2), (key1361, -2), (key1487, 2), (key1487, 2), (key1487, 2)]

def rawRow4629 : Integer.Sparse Key := [(key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key351, 2), (key351, 2), (key351, 2), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key672, -2), (key672, -2), (key672, -2), (key668, 1), (key668, 1), (key668, 1), (key668, 1), (key668, 1), (key668, 1)]

def rawRow4636 : Integer.Sparse Key := [(key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key481, 2), (key481, 2), (key481, 2), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key458, -1), (key351, -2), (key351, -2), (key351, -2), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1)]

def rawRow4643 : Integer.Sparse Key := [(key1504, -2), (key1504, -2), (key1504, -2), (key1502, 2), (key1502, 2), (key1502, 2), (key1737, 2), (key1737, 2), (key1737, 2), (key1734, -6), (key1947, -2), (key1947, -2), (key1947, -2), (key1945, 6)]

def rawRow4650 : Integer.Sparse Key := [(key1737, -2), (key1737, -2), (key1737, -2), (key1947, 2), (key1947, 2), (key1947, 2), (key1504, 2), (key1504, 2), (key1504, 2), (key1945, -6), (key1502, -2), (key1502, -2), (key1502, -2), (key1734, 6)]

def rawRow4657 : Integer.Sparse Key := [(key272, -2), (key272, -2), (key272, -2), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key261, 1), (key371, 2), (key371, 2), (key371, 2), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key354, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key543, -1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1), (key523, 1)]

def rawRow4664 : Integer.Sparse Key := [(key573, -2), (key573, -2), (key573, -2), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key596, 1), (key272, 2), (key272, 2), (key272, 2), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key470, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key261, -1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1), (key398, 1)]

def rawRow4671 : Integer.Sparse Key := [(key226, -2), (key226, -2), (key226, -2), (key223, 6), (key552, 2), (key552, 2), (key552, 2), (key495, -2), (key495, -2), (key495, -2), (key646, -6), (key620, 2), (key620, 2), (key620, 2)]

def rawRow4678 : Integer.Sparse Key := [(key552, -2), (key552, -2), (key552, -2), (key646, 6), (key226, 2), (key226, 2), (key226, 2), (key620, -2), (key620, -2), (key620, -2), (key223, -6), (key495, 2), (key495, 2), (key495, 2)]

def rawRow4685 : Integer.Sparse Key := [(key1370, -2), (key1370, -2), (key1370, -2), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1366, 1), (key1747, 2), (key1747, 2), (key1747, 2), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1718, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1880, -1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1), (key1865, 1)]

def rawRow4692 : Integer.Sparse Key := [(key1747, -2), (key1747, -2), (key1747, -2), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1880, 1), (key1370, 2), (key1370, 2), (key1370, 2), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1865, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1366, -1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1), (key1718, 1)]

def rawRow4699 : Integer.Sparse Key := [(key1281, -2), (key1281, -2), (key1281, -2), (key1276, 6), (key1753, 2), (key1753, 2), (key1753, 2), (key1699, -2), (key1699, -2), (key1699, -2), (key1954, -6), (key1934, 2), (key1934, 2), (key1934, 2)]

def rawRow4706 : Integer.Sparse Key := [(key1753, -2), (key1753, -2), (key1753, -2), (key1954, 6), (key1281, 2), (key1281, 2), (key1281, 2), (key1934, -2), (key1934, -2), (key1934, -2), (key1276, -6), (key1699, 2), (key1699, 2), (key1699, 2)]

def rawRow4713 : Integer.Sparse Key := [(key1279, -2), (key1279, -2), (key1279, -2), (key1276, 6), (key1752, 2), (key1752, 2), (key1752, 2), (key1699, -2), (key1699, -2), (key1699, -2), (key1885, -6), (key1853, 2), (key1853, 2), (key1853, 2)]

def rawRow4720 : Integer.Sparse Key := [(key1752, -2), (key1752, -2), (key1752, -2), (key1885, 6), (key1279, 2), (key1279, 2), (key1279, 2), (key1853, -2), (key1853, -2), (key1853, -2), (key1276, -6), (key1699, 2), (key1699, 2), (key1699, 2)]

def rawRow4727 : Integer.Sparse Key := [(key1375, -2), (key1375, -2), (key1375, -2), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1365, 1), (key1514, 2), (key1514, 2), (key1514, 2), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1742, -1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1)]

def rawRow4734 : Integer.Sparse Key := [(key1514, -2), (key1514, -2), (key1514, -2), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1742, 1), (key1375, 2), (key1375, 2), (key1375, 2), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1365, -1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1)]

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

def rawRow4741 : Integer.Sparse Key := [(key742, -2), (key742, -2), (key742, -2), (key741, 6), (key951, 2), (key951, 2), (key951, 2), (key900, -2), (key900, -2), (key900, -2), (key954, -6), (key913, 2), (key913, 2), (key913, 2)]

def rawRow4748 : Integer.Sparse Key := [(key951, -2), (key951, -2), (key951, -2), (key954, 6), (key742, 2), (key742, 2), (key742, 2), (key913, -2), (key913, -2), (key913, -2), (key741, -6), (key900, 2), (key900, 2), (key900, 2)]

def rawRow4755 : Integer.Sparse Key := [(key1284, -2), (key1284, -2), (key1284, -2), (key1280, 2), (key1280, 2), (key1280, 2), (key1757, 2), (key1757, 2), (key1757, 2), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1703, -1), (key1887, -2), (key1887, -2), (key1887, -2), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1), (key1856, 1)]

def rawRow4762 : Integer.Sparse Key := [(key1757, -2), (key1757, -2), (key1757, -2), (key1887, 2), (key1887, 2), (key1887, 2), (key1284, 2), (key1284, 2), (key1284, 2), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1856, -1), (key1280, -2), (key1280, -2), (key1280, -2), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1), (key1703, 1)]

def rawRow4769 : Integer.Sparse Key := [(key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1493, -1), (key1488, 2), (key1488, 2), (key1488, 2), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1725, 1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1941, -2), (key1941, -2), (key1941, -2), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1), (key1938, 1)]

def rawRow4776 : Integer.Sparse Key := [(key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1725, -1), (key1941, 2), (key1941, 2), (key1941, 2), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1493, 1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1938, -1), (key1488, -2), (key1488, -2), (key1488, -2), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1)]

def rawRow4780 : Integer.Sparse Key := [(key1362, -2), (key1365, -2), (key1365, -2), (key1365, 2), (key1365, 2), (key1375, 2), (key1488, 2), (key1491, 2), (key1491, 2), (key1491, -2), (key1491, -2), (key1514, -2), (key1862, -2), (key1862, -2), (key1868, -2), (key1862, 2), (key1862, 2), (key1878, 2)]

def rawRow4781 : Integer.Sparse Key := [(key1365, -2), (key1362, -2), (key1365, -2), (key1365, 2), (key1375, 2), (key1365, 2), (key1491, 2), (key1488, 2), (key1491, 2), (key1491, -2), (key1514, -2), (key1491, -2), (key1862, -2), (key1868, -2), (key1862, -2), (key1862, 2), (key1878, 2), (key1862, 2)]

def rawRow4782 : Integer.Sparse Key := [(key1365, -2), (key1365, -2), (key1362, -2), (key1375, 2), (key1365, 2), (key1365, 2), (key1491, 2), (key1491, 2), (key1488, 2), (key1514, -2), (key1491, -2), (key1491, -2), (key1868, -2), (key1862, -2), (key1862, -2), (key1878, 2), (key1862, 2), (key1862, 2)]

def rawRow4783 : Integer.Sparse Key := [(key1375, -2), (key1375, -2), (key1375, -2), (key1362, 2), (key1362, 2), (key1362, 2), (key1514, 2), (key1514, 2), (key1514, 2), (key1488, -2), (key1488, -2), (key1488, -2), (key1878, -2), (key1878, -2), (key1878, -2), (key1868, 2), (key1868, 2), (key1868, 2)]

def rawRow4784 : Integer.Sparse Key := [(key1488, -2), (key1491, -2), (key1491, -2), (key1862, 2), (key1862, 2), (key1868, 2), (key1362, 2), (key1365, 2), (key1365, 2), (key1862, -2), (key1862, -2), (key1878, -2), (key1365, -2), (key1365, -2), (key1375, -2), (key1491, 2), (key1491, 2), (key1514, 2)]

def rawRow4785 : Integer.Sparse Key := [(key1491, -2), (key1488, -2), (key1491, -2), (key1862, 2), (key1868, 2), (key1862, 2), (key1365, 2), (key1362, 2), (key1365, 2), (key1862, -2), (key1878, -2), (key1862, -2), (key1365, -2), (key1375, -2), (key1365, -2), (key1491, 2), (key1514, 2), (key1491, 2)]

def rawRow4786 : Integer.Sparse Key := [(key1491, -2), (key1491, -2), (key1488, -2), (key1868, 2), (key1862, 2), (key1862, 2), (key1365, 2), (key1365, 2), (key1362, 2), (key1878, -2), (key1862, -2), (key1862, -2), (key1375, -2), (key1365, -2), (key1365, -2), (key1514, 2), (key1491, 2), (key1491, 2)]

def rawRow4787 : Integer.Sparse Key := [(key1724, -2), (key1724, -2), (key1868, -2), (key1488, 2), (key1714, 2), (key1714, 2), (key1742, 2), (key1742, 2), (key1878, 2), (key1362, -2), (key1714, -2), (key1714, -2), (key1514, -2), (key1742, -2), (key1742, -2), (key1375, 2), (key1724, 2), (key1724, 2)]

def rawRow4788 : Integer.Sparse Key := [(key1724, -2), (key1868, -2), (key1724, -2), (key1714, 2), (key1488, 2), (key1714, 2), (key1742, 2), (key1878, 2), (key1742, 2), (key1714, -2), (key1362, -2), (key1714, -2), (key1742, -2), (key1514, -2), (key1742, -2), (key1724, 2), (key1375, 2), (key1724, 2)]

def rawRow4789 : Integer.Sparse Key := [(key1868, -2), (key1724, -2), (key1724, -2), (key1714, 2), (key1714, 2), (key1488, 2), (key1878, 2), (key1742, 2), (key1742, 2), (key1714, -2), (key1714, -2), (key1362, -2), (key1742, -2), (key1742, -2), (key1514, -2), (key1724, 2), (key1724, 2), (key1375, 2)]

def rawRow4790 : Integer.Sparse Key := [(key1514, -2), (key1514, -2), (key1514, -2), (key1878, 2), (key1878, 2), (key1878, 2), (key1375, 2), (key1375, 2), (key1375, 2), (key1868, -2), (key1868, -2), (key1868, -2), (key1362, -2), (key1362, -2), (key1362, -2), (key1488, 2), (key1488, 2), (key1488, 2)]

def rawRow4791 : Integer.Sparse Key := [(key1742, -2), (key1742, -2), (key1878, -2), (key1514, 2), (key1742, 2), (key1742, 2), (key1724, 2), (key1724, 2), (key1868, 2), (key1375, -2), (key1724, -2), (key1724, -2), (key1488, -2), (key1714, -2), (key1714, -2), (key1362, 2), (key1714, 2), (key1714, 2)]

def rawRow4792 : Integer.Sparse Key := [(key1742, -2), (key1878, -2), (key1742, -2), (key1742, 2), (key1514, 2), (key1742, 2), (key1724, 2), (key1868, 2), (key1724, 2), (key1724, -2), (key1375, -2), (key1724, -2), (key1714, -2), (key1488, -2), (key1714, -2), (key1714, 2), (key1362, 2), (key1714, 2)]

def rawRow4793 : Integer.Sparse Key := [(key1878, -2), (key1742, -2), (key1742, -2), (key1742, 2), (key1742, 2), (key1514, 2), (key1868, 2), (key1724, 2), (key1724, 2), (key1724, -2), (key1724, -2), (key1375, -2), (key1714, -2), (key1714, -2), (key1488, -2), (key1714, 2), (key1714, 2), (key1362, 2)]

def rawRow4797 : Integer.Sparse Key := [(key353, -1), (key353, -1), (key353, -1), (key353, -1), (key353, -1), (key353, -1), (key351, 2), (key351, 2), (key351, 2), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key521, 1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key508, -1), (key630, -2), (key630, -2), (key630, -2), (key628, 1), (key628, 1), (key628, 1), (key628, 1), (key628, 1), (key628, 1)]

def rawRow4804 : Integer.Sparse Key := [(key521, -1), (key521, -1), (key521, -1), (key521, -1), (key521, -1), (key521, -1), (key630, 2), (key630, 2), (key630, 2), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key353, 1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key628, -1), (key351, -2), (key351, -2), (key351, -2), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1), (key508, 1)]

def rawRow4811 : Integer.Sparse Key := [(key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1491, -1), (key1488, 2), (key1488, 2), (key1488, 2), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1724, 1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1714, -1), (key1868, -2), (key1868, -2), (key1868, -2), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1), (key1862, 1)]

def rawRow4818 : Integer.Sparse Key := [(key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1724, -1), (key1868, 2), (key1868, 2), (key1868, 2), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1491, 1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1862, -1), (key1488, -2), (key1488, -2), (key1488, -2), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1), (key1714, 1)]

def rawRow4825 : Integer.Sparse Key := [(key294, -2), (key294, -2), (key294, -2), (key291, 6), (key553, 2), (key553, 2), (key553, 2), (key518, -2), (key518, -2), (key518, -2), (key647, -6), (key631, 2), (key631, 2), (key631, 2)]

def rawRow4832 : Integer.Sparse Key := [(key631, -2), (key631, -2), (key631, -2), (key647, 6), (key294, 2), (key294, 2), (key294, 2), (key553, -2), (key553, -2), (key553, -2), (key291, -6), (key518, 2), (key518, 2), (key518, 2)]

def rawRow4848 : Integer.Sparse Key := [(key1422, -6), (key1389, 2), (key1453, 2), (key1453, 2), (key1571, 6), (key1294, -2), (key1786, -2), (key1786, -2), (key1544, -2), (key1653, -2), (key1653, -2), (key1314, 2), (key1811, 2), (key1811, 2)]

def rawRow4849 : Integer.Sparse Key := [(key1422, -6), (key1453, 2), (key1389, 2), (key1453, 2), (key1571, 6), (key1786, -2), (key1294, -2), (key1786, -2), (key1653, -2), (key1544, -2), (key1653, -2), (key1811, 2), (key1314, 2), (key1811, 2)]

def rawRow4850 : Integer.Sparse Key := [(key1422, -6), (key1453, 2), (key1453, 2), (key1389, 2), (key1571, 6), (key1786, -2), (key1786, -2), (key1294, -2), (key1653, -2), (key1653, -2), (key1544, -2), (key1811, 2), (key1811, 2), (key1314, 2)]

def rawRow4851 : Integer.Sparse Key := [(key1571, -6), (key1544, 2), (key1653, 2), (key1653, 2), (key1422, 6), (key1314, -2), (key1811, -2), (key1811, -2), (key1389, -2), (key1453, -2), (key1453, -2), (key1294, 2), (key1786, 2), (key1786, 2)]

def rawRow4852 : Integer.Sparse Key := [(key1571, -6), (key1653, 2), (key1544, 2), (key1653, 2), (key1422, 6), (key1811, -2), (key1314, -2), (key1811, -2), (key1453, -2), (key1389, -2), (key1453, -2), (key1786, 2), (key1294, 2), (key1786, 2)]

def rawRow4853 : Integer.Sparse Key := [(key1571, -6), (key1653, 2), (key1653, 2), (key1544, 2), (key1422, 6), (key1811, -2), (key1811, -2), (key1314, -2), (key1453, -2), (key1453, -2), (key1389, -2), (key1786, 2), (key1786, 2), (key1294, 2)]

def rawRow4854 : Integer.Sparse Key := [(key2612, -2), (key2616, -2), (key2621, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2644, 1), (key2644, 1), (key2671, 2), (key2671, 2), (key2676, 2), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2732, -1), (key2732, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2798, -1), (key2798, -1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2835, 1), (key2835, 1)]

def rawRow4855 : Integer.Sparse Key := [(key2612, -2), (key2618, -2), (key2616, -2), (key2640, 1), (key2644, 1), (key2632, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2671, 2), (key2676, 2), (key2671, 2), (key2726, -1), (key2732, -1), (key2706, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2794, -1), (key2798, -1), (key2786, -1), (key2798, -1), (key2786, -1), (key2794, -1), (key2829, 1), (key2835, 1), (key2809, 1), (key2835, 1), (key2809, 1), (key2829, 1)]

def rawRow4856 : Integer.Sparse Key := [(key2618, -2), (key2612, -2), (key2616, -2), (key2644, 1), (key2640, 1), (key2644, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2676, 2), (key2671, 2), (key2671, 2), (key2732, -1), (key2726, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2798, -1), (key2794, -1), (key2798, -1), (key2786, -1), (key2794, -1), (key2786, -1), (key2835, 1), (key2829, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2809, 1)]

def rawRow4857 : Integer.Sparse Key := [(key2667, -2), (key2667, -2), (key2673, -2), (key2702, 1), (key2702, 1), (key2735, 1), (key2735, 1), (key2737, 1), (key2737, 1), (key2612, 2), (key2616, 2), (key2621, 2), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2835, -1), (key2835, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2644, -1), (key2644, -1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1)]

def rawRow4858 : Integer.Sparse Key := [(key2667, -2), (key2673, -2), (key2667, -2), (key2735, 1), (key2737, 1), (key2702, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2612, 2), (key2618, 2), (key2616, 2), (key2829, -1), (key2835, -1), (key2809, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2640, -1), (key2644, -1), (key2632, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1)]

def rawRow4859 : Integer.Sparse Key := [(key2673, -2), (key2667, -2), (key2667, -2), (key2737, 1), (key2735, 1), (key2737, 1), (key2702, 1), (key2735, 1), (key2702, 1), (key2618, 2), (key2612, 2), (key2616, 2), (key2835, -1), (key2829, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2644, -1), (key2640, -1), (key2644, -1), (key2632, -1), (key2640, -1), (key2632, -1), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1)]

def rawRow4860 : Integer.Sparse Key := [(key2702, -2), (key2702, -2), (key2728, -2), (key2667, 1), (key2667, 1), (key2735, 1), (key2735, 1), (key2747, 1), (key2747, 1), (key2805, 2), (key2805, 2), (key2831, 2), (key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key3023, -1), (key3023, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1)]

def rawRow4861 : Integer.Sparse Key := [(key2702, -2), (key2728, -2), (key2702, -2), (key2735, 1), (key2747, 1), (key2667, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2805, 2), (key2831, 2), (key2805, 2), (key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1)]

def rawRow4862 : Integer.Sparse Key := [(key2728, -2), (key2702, -2), (key2702, -2), (key2747, 1), (key2735, 1), (key2747, 1), (key2667, 1), (key2735, 1), (key2667, 1), (key2831, 2), (key2805, 2), (key2805, 2), (key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key3023, -1), (key2860, -1), (key3023, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1)]

def rawRow4863 : Integer.Sparse Key := [(key2805, -2), (key2805, -2), (key2831, -2), (key2782, 1), (key2782, 1), (key2893, 1), (key2893, 1), (key2904, 1), (key2904, 1), (key2702, 2), (key2702, 2), (key2728, 2), (key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2667, -1), (key2667, -1), (key2735, -1), (key2735, -1), (key2747, -1), (key2747, -1), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1)]

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

def rawRow4864 : Integer.Sparse Key := [(key2805, -2), (key2831, -2), (key2805, -2), (key2893, 1), (key2904, 1), (key2782, 1), (key2904, 1), (key2782, 1), (key2893, 1), (key2702, 2), (key2728, 2), (key2702, 2), (key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1)]

def rawRow4865 : Integer.Sparse Key := [(key2831, -2), (key2805, -2), (key2805, -2), (key2904, 1), (key2893, 1), (key2904, 1), (key2782, 1), (key2893, 1), (key2782, 1), (key2728, 2), (key2702, 2), (key2702, 2), (key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2747, -1), (key2735, -1), (key2747, -1), (key2667, -1), (key2735, -1), (key2667, -1), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1)]

def rawRow4872 : Integer.Sparse Key := [(key1033, -2), (key1033, -2), (key1076, -2), (key1041, 6), (key1111, 2), (key1111, 2), (key1155, 2), (key1006, -2), (key1193, -2), (key1193, -2), (key1127, -6), (key1019, 2), (key1199, 2), (key1199, 2)]

def rawRow4873 : Integer.Sparse Key := [(key1033, -2), (key1076, -2), (key1033, -2), (key1041, 6), (key1111, 2), (key1155, 2), (key1111, 2), (key1193, -2), (key1006, -2), (key1193, -2), (key1127, -6), (key1199, 2), (key1019, 2), (key1199, 2)]

def rawRow4874 : Integer.Sparse Key := [(key1076, -2), (key1033, -2), (key1033, -2), (key1041, 6), (key1155, 2), (key1111, 2), (key1111, 2), (key1193, -2), (key1193, -2), (key1006, -2), (key1127, -6), (key1199, 2), (key1199, 2), (key1019, 2)]

def rawRow4875 : Integer.Sparse Key := [(key1111, -2), (key1111, -2), (key1155, -2), (key1127, 6), (key1033, 2), (key1033, 2), (key1076, 2), (key1019, -2), (key1199, -2), (key1199, -2), (key1041, -6), (key1006, 2), (key1193, 2), (key1193, 2)]

def rawRow4876 : Integer.Sparse Key := [(key1111, -2), (key1155, -2), (key1111, -2), (key1127, 6), (key1033, 2), (key1076, 2), (key1033, 2), (key1199, -2), (key1019, -2), (key1199, -2), (key1041, -6), (key1193, 2), (key1006, 2), (key1193, 2)]

def rawRow4877 : Integer.Sparse Key := [(key1155, -2), (key1111, -2), (key1111, -2), (key1127, 6), (key1076, 2), (key1033, 2), (key1033, 2), (key1199, -2), (key1199, -2), (key1019, -2), (key1041, -6), (key1193, 2), (key1193, 2), (key1006, 2)]

def rawRow4884 : Integer.Sparse Key := [(key2785, -6), (key2670, 2), (key2793, 2), (key2793, 2), (key2808, 6), (key2615, -2), (key2828, -2), (key2828, -2), (key2705, -2), (key2859, -2), (key2859, -2), (key2631, 2), (key2869, 2), (key2869, 2)]

def rawRow4885 : Integer.Sparse Key := [(key2785, -6), (key2793, 2), (key2670, 2), (key2793, 2), (key2808, 6), (key2828, -2), (key2615, -2), (key2828, -2), (key2859, -2), (key2705, -2), (key2859, -2), (key2869, 2), (key2631, 2), (key2869, 2)]

def rawRow4886 : Integer.Sparse Key := [(key2785, -6), (key2793, 2), (key2793, 2), (key2670, 2), (key2808, 6), (key2828, -2), (key2828, -2), (key2615, -2), (key2859, -2), (key2859, -2), (key2705, -2), (key2869, 2), (key2869, 2), (key2631, 2)]

def rawRow4887 : Integer.Sparse Key := [(key2808, -6), (key2705, 2), (key2859, 2), (key2859, 2), (key2785, 6), (key2631, -2), (key2869, -2), (key2869, -2), (key2670, -2), (key2793, -2), (key2793, -2), (key2615, 2), (key2828, 2), (key2828, 2)]

def rawRow4888 : Integer.Sparse Key := [(key2808, -6), (key2859, 2), (key2705, 2), (key2859, 2), (key2785, 6), (key2869, -2), (key2631, -2), (key2869, -2), (key2793, -2), (key2670, -2), (key2793, -2), (key2828, 2), (key2615, 2), (key2828, 2)]

def rawRow4889 : Integer.Sparse Key := [(key2808, -6), (key2859, 2), (key2859, 2), (key2705, 2), (key2785, 6), (key2869, -2), (key2869, -2), (key2631, -2), (key2793, -2), (key2793, -2), (key2670, -2), (key2828, 2), (key2828, 2), (key2615, 2)]

def rawRow4896 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1799, -1), (key1799, -1), (key1303, 2), (key1791, 2), (key1791, 2), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1826, 1), (key1826, 1), (key1340, -1), (key1340, -1), (key1775, -1), (key1775, -1), (key1840, -1), (key1840, -1), (key1330, -2), (key1818, -2), (key1818, -2), (key1346, 1), (key1346, 1), (key1781, 1), (key1781, 1), (key1842, 1), (key1842, 1)]

def rawRow4897 : Integer.Sparse Key := [(key1788, -1), (key1799, -1), (key1296, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1791, 2), (key1303, 2), (key1791, 2), (key1813, 1), (key1826, 1), (key1316, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1775, -1), (key1840, -1), (key1340, -1), (key1840, -1), (key1340, -1), (key1775, -1), (key1818, -2), (key1330, -2), (key1818, -2), (key1781, 1), (key1842, 1), (key1346, 1), (key1842, 1), (key1346, 1), (key1781, 1)]

def rawRow4898 : Integer.Sparse Key := [(key1799, -1), (key1788, -1), (key1799, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1791, 2), (key1791, 2), (key1303, 2), (key1826, 1), (key1813, 1), (key1826, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1840, -1), (key1775, -1), (key1840, -1), (key1340, -1), (key1775, -1), (key1340, -1), (key1818, -2), (key1818, -2), (key1330, -2), (key1842, 1), (key1781, 1), (key1842, 1), (key1346, 1), (key1781, 1), (key1346, 1)]

def rawRow4899 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1826, -1), (key1826, -1), (key1330, 2), (key1818, 2), (key1818, 2), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1799, 1), (key1799, 1), (key1346, -1), (key1346, -1), (key1781, -1), (key1781, -1), (key1842, -1), (key1842, -1), (key1303, -2), (key1791, -2), (key1791, -2), (key1340, 1), (key1340, 1), (key1775, 1), (key1775, 1), (key1840, 1), (key1840, 1)]

def rawRow4900 : Integer.Sparse Key := [(key1813, -1), (key1826, -1), (key1316, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1818, 2), (key1330, 2), (key1818, 2), (key1788, 1), (key1799, 1), (key1296, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1781, -1), (key1842, -1), (key1346, -1), (key1842, -1), (key1346, -1), (key1781, -1), (key1791, -2), (key1303, -2), (key1791, -2), (key1775, 1), (key1840, 1), (key1340, 1), (key1840, 1), (key1340, 1), (key1775, 1)]

def rawRow4901 : Integer.Sparse Key := [(key1826, -1), (key1813, -1), (key1826, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1818, 2), (key1818, 2), (key1330, 2), (key1799, 1), (key1788, 1), (key1799, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1842, -1), (key1781, -1), (key1842, -1), (key1346, -1), (key1781, -1), (key1346, -1), (key1791, -2), (key1791, -2), (key1303, -2), (key1840, 1), (key1775, 1), (key1840, 1), (key1340, 1), (key1775, 1), (key1340, 1)]

def rawRow4902 : Integer.Sparse Key := [(key2719, -2), (key2719, -2), (key2733, -2), (key2756, 2), (key2756, 2), (key2759, 2), (key2822, 2), (key2822, 2), (key2836, 2), (key2924, -6), (key3015, -2), (key3015, -2), (key3018, -2), (key3027, 6)]

def rawRow4903 : Integer.Sparse Key := [(key2719, -2), (key2733, -2), (key2719, -2), (key2756, 2), (key2759, 2), (key2756, 2), (key2822, 2), (key2836, 2), (key2822, 2), (key2924, -6), (key3015, -2), (key3018, -2), (key3015, -2), (key3027, 6)]

def rawRow4904 : Integer.Sparse Key := [(key2733, -2), (key2719, -2), (key2719, -2), (key2759, 2), (key2756, 2), (key2756, 2), (key2836, 2), (key2822, 2), (key2822, 2), (key2924, -6), (key3018, -2), (key3015, -2), (key3015, -2), (key3027, 6)]

def rawRow4905 : Integer.Sparse Key := [(key2822, -2), (key2822, -2), (key2836, -2), (key3015, 2), (key3015, 2), (key3018, 2), (key2719, 2), (key2719, 2), (key2733, 2), (key3027, -6), (key2756, -2), (key2756, -2), (key2759, -2), (key2924, 6)]

def rawRow4906 : Integer.Sparse Key := [(key2822, -2), (key2836, -2), (key2822, -2), (key3015, 2), (key3018, 2), (key3015, 2), (key2719, 2), (key2733, 2), (key2719, 2), (key3027, -6), (key2756, -2), (key2759, -2), (key2756, -2), (key2924, 6)]

def rawRow4907 : Integer.Sparse Key := [(key2836, -2), (key2822, -2), (key2822, -2), (key3018, 2), (key3015, 2), (key3015, 2), (key2733, 2), (key2719, 2), (key2719, 2), (key3027, -6), (key2759, -2), (key2756, -2), (key2756, -2), (key2924, 6)]

def rawRow4950 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2380, -2), (key2391, 6), (key2770, 2), (key2770, 2), (key2775, 2), (key2917, -2), (key2926, -2), (key2926, -2), (key3006, -6), (key3020, 2), (key3029, 2), (key3029, 2)]

def rawRow4951 : Integer.Sparse Key := [(key2374, -2), (key2380, -2), (key2374, -2), (key2391, 6), (key2770, 2), (key2775, 2), (key2770, 2), (key2926, -2), (key2917, -2), (key2926, -2), (key3006, -6), (key3029, 2), (key3020, 2), (key3029, 2)]

def rawRow4952 : Integer.Sparse Key := [(key2380, -2), (key2374, -2), (key2374, -2), (key2391, 6), (key2775, 2), (key2770, 2), (key2770, 2), (key2926, -2), (key2926, -2), (key2917, -2), (key3006, -6), (key3029, 2), (key3029, 2), (key3020, 2)]

def rawRow4953 : Integer.Sparse Key := [(key2374, -2), (key2374, -2), (key2391, -2), (key2380, 6), (key2847, 2), (key2847, 2), (key2917, 2), (key2775, -2), (key2884, -2), (key2884, -2), (key3020, -6), (key3006, 2), (key3029, 2), (key3029, 2)]

def rawRow4954 : Integer.Sparse Key := [(key2374, -2), (key2391, -2), (key2374, -2), (key2380, 6), (key2847, 2), (key2917, 2), (key2847, 2), (key2884, -2), (key2775, -2), (key2884, -2), (key3020, -6), (key3029, 2), (key3006, 2), (key3029, 2)]

def rawRow4955 : Integer.Sparse Key := [(key2391, -2), (key2374, -2), (key2374, -2), (key2380, 6), (key2917, 2), (key2847, 2), (key2847, 2), (key2884, -2), (key2884, -2), (key2775, -2), (key3020, -6), (key3029, 2), (key3029, 2), (key3006, 2)]

def rawRow4956 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2408, -2), (key2439, 6), (key2591, 2), (key2591, 2), (key2596, 2), (key3020, -2), (key3029, -2), (key3029, -2), (key2605, -6), (key2917, 2), (key2926, 2), (key2926, 2)]

def rawRow4957 : Integer.Sparse Key := [(key2402, -2), (key2408, -2), (key2402, -2), (key2439, 6), (key2591, 2), (key2596, 2), (key2591, 2), (key3029, -2), (key3020, -2), (key3029, -2), (key2605, -6), (key2926, 2), (key2917, 2), (key2926, 2)]

def rawRow4958 : Integer.Sparse Key := [(key2408, -2), (key2402, -2), (key2402, -2), (key2439, 6), (key2596, 2), (key2591, 2), (key2591, 2), (key3029, -2), (key3029, -2), (key3020, -2), (key2605, -6), (key2926, 2), (key2926, 2), (key2917, 2)]

def rawRow4959 : Integer.Sparse Key := [(key2402, -2), (key2402, -2), (key2439, -2), (key2408, 6), (key2847, 2), (key2847, 2), (key3020, 2), (key2596, -2), (key2884, -2), (key2884, -2), (key2917, -6), (key2605, 2), (key2926, 2), (key2926, 2)]

def rawRow4960 : Integer.Sparse Key := [(key2402, -2), (key2439, -2), (key2402, -2), (key2408, 6), (key2847, 2), (key3020, 2), (key2847, 2), (key2884, -2), (key2596, -2), (key2884, -2), (key2917, -6), (key2926, 2), (key2605, 2), (key2926, 2)]

def rawRow4961 : Integer.Sparse Key := [(key2439, -2), (key2402, -2), (key2402, -2), (key2408, 6), (key3020, 2), (key2847, 2), (key2847, 2), (key2884, -2), (key2884, -2), (key2596, -2), (key2917, -6), (key2926, 2), (key2926, 2), (key2605, 2)]

def rawRow4962 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2481, -2), (key2505, 6), (key2374, 2), (key2374, 2), (key2391, 2), (key3006, -2), (key3029, -2), (key3029, -2), (key2596, -6), (key2775, 2), (key2884, 2), (key2884, 2)]

def rawRow4963 : Integer.Sparse Key := [(key2468, -2), (key2481, -2), (key2468, -2), (key2505, 6), (key2374, 2), (key2391, 2), (key2374, 2), (key3029, -2), (key3006, -2), (key3029, -2), (key2596, -6), (key2884, 2), (key2775, 2), (key2884, 2)]

def rawRow4964 : Integer.Sparse Key := [(key2481, -2), (key2468, -2), (key2468, -2), (key2505, 6), (key2391, 2), (key2374, 2), (key2374, 2), (key3029, -2), (key3029, -2), (key3006, -2), (key2596, -6), (key2884, 2), (key2884, 2), (key2775, 2)]

def rawRow4965 : Integer.Sparse Key := [(key2468, -2), (key2468, -2), (key2505, -2), (key2481, 6), (key2402, 2), (key2402, 2), (key2439, 2), (key2605, -2), (key2926, -2), (key2926, -2), (key2775, -6), (key2596, 2), (key2884, 2), (key2884, 2)]

def rawRow4966 : Integer.Sparse Key := [(key2468, -2), (key2505, -2), (key2468, -2), (key2481, 6), (key2402, 2), (key2439, 2), (key2402, 2), (key2926, -2), (key2605, -2), (key2926, -2), (key2775, -6), (key2884, 2), (key2596, 2), (key2884, 2)]

def rawRow4967 : Integer.Sparse Key := [(key2505, -2), (key2468, -2), (key2468, -2), (key2481, 6), (key2439, 2), (key2402, 2), (key2402, 2), (key2926, -2), (key2926, -2), (key2605, -2), (key2775, -6), (key2884, 2), (key2884, 2), (key2596, 2)]

def rawRow4968 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2594, -2), (key2601, 6), (key2770, 2), (key2770, 2), (key2773, 2), (key2890, -2), (key2911, -2), (key2911, -2), (key2932, -6), (key2969, 2), (key2990, 2), (key2990, 2)]

def rawRow4969 : Integer.Sparse Key := [(key2591, -2), (key2594, -2), (key2591, -2), (key2601, 6), (key2770, 2), (key2773, 2), (key2770, 2), (key2911, -2), (key2890, -2), (key2911, -2), (key2932, -6), (key2990, 2), (key2969, 2), (key2990, 2)]

def rawRow4970 : Integer.Sparse Key := [(key2594, -2), (key2591, -2), (key2591, -2), (key2601, 6), (key2773, 2), (key2770, 2), (key2770, 2), (key2911, -2), (key2911, -2), (key2890, -2), (key2932, -6), (key2990, 2), (key2990, 2), (key2969, 2)]

def rawRow4971 : Integer.Sparse Key := [(key2591, -2), (key2591, -2), (key2601, -2), (key2594, 6), (key2847, 2), (key2847, 2), (key2890, 2), (key2773, -2), (key2881, -2), (key2881, -2), (key2969, -6), (key2932, 2), (key2990, 2), (key2990, 2)]

def rawRow4972 : Integer.Sparse Key := [(key2591, -2), (key2601, -2), (key2591, -2), (key2594, 6), (key2847, 2), (key2890, 2), (key2847, 2), (key2881, -2), (key2773, -2), (key2881, -2), (key2969, -6), (key2990, 2), (key2932, 2), (key2990, 2)]

def rawRow4973 : Integer.Sparse Key := [(key2601, -2), (key2591, -2), (key2591, -2), (key2594, 6), (key2890, 2), (key2847, 2), (key2847, 2), (key2881, -2), (key2881, -2), (key2773, -2), (key2969, -6), (key2990, 2), (key2990, 2), (key2932, 2)]

def rawRow4974 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2773, -2), (key2932, 6), (key2591, 2), (key2591, 2), (key2594, 2), (key2969, -2), (key2990, -2), (key2990, -2), (key2601, -6), (key2890, 2), (key2911, 2), (key2911, 2)]

def rawRow4975 : Integer.Sparse Key := [(key2770, -2), (key2773, -2), (key2770, -2), (key2932, 6), (key2591, 2), (key2594, 2), (key2591, 2), (key2990, -2), (key2969, -2), (key2990, -2), (key2601, -6), (key2911, 2), (key2890, 2), (key2911, 2)]

def rawRow4976 : Integer.Sparse Key := [(key2773, -2), (key2770, -2), (key2770, -2), (key2932, 6), (key2594, 2), (key2591, 2), (key2591, 2), (key2990, -2), (key2990, -2), (key2969, -2), (key2601, -6), (key2911, 2), (key2911, 2), (key2890, 2)]

def rawRow4977 : Integer.Sparse Key := [(key2770, -2), (key2770, -2), (key2932, -2), (key2773, 6), (key2847, 2), (key2847, 2), (key2969, 2), (key2594, -2), (key2881, -2), (key2881, -2), (key2890, -6), (key2601, 2), (key2911, 2), (key2911, 2)]

def rawRow4978 : Integer.Sparse Key := [(key2770, -2), (key2932, -2), (key2770, -2), (key2773, 6), (key2847, 2), (key2969, 2), (key2847, 2), (key2881, -2), (key2594, -2), (key2881, -2), (key2890, -6), (key2911, 2), (key2601, 2), (key2911, 2)]

def rawRow4979 : Integer.Sparse Key := [(key2932, -2), (key2770, -2), (key2770, -2), (key2773, 6), (key2969, 2), (key2847, 2), (key2847, 2), (key2881, -2), (key2881, -2), (key2594, -2), (key2890, -6), (key2911, 2), (key2911, 2), (key2601, 2)]

def rawRow4980 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2890, -2), (key2969, 6), (key2591, 2), (key2591, 2), (key2601, 2), (key2932, -2), (key2990, -2), (key2990, -2), (key2594, -6), (key2773, 2), (key2881, 2), (key2881, 2)]

def rawRow4981 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2847, -2), (key2969, 6), (key2591, 2), (key2601, 2), (key2591, 2), (key2990, -2), (key2932, -2), (key2990, -2), (key2594, -6), (key2881, 2), (key2773, 2), (key2881, 2)]

def rawRow4982 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2847, -2), (key2969, 6), (key2601, 2), (key2591, 2), (key2591, 2), (key2990, -2), (key2990, -2), (key2932, -2), (key2594, -6), (key2881, 2), (key2881, 2), (key2773, 2)]

def rawRow4983 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2969, -2), (key2890, 6), (key2770, 2), (key2770, 2), (key2932, 2), (key2601, -2), (key2911, -2), (key2911, -2), (key2773, -6), (key2594, 2), (key2881, 2), (key2881, 2)]

def rawRow4984 : Integer.Sparse Key := [(key2847, -2), (key2969, -2), (key2847, -2), (key2890, 6), (key2770, 2), (key2932, 2), (key2770, 2), (key2911, -2), (key2601, -2), (key2911, -2), (key2773, -6), (key2881, 2), (key2594, 2), (key2881, 2)]

def rawRow4985 : Integer.Sparse Key := [(key2969, -2), (key2847, -2), (key2847, -2), (key2890, 6), (key2932, 2), (key2770, 2), (key2770, 2), (key2911, -2), (key2911, -2), (key2601, -2), (key2773, -6), (key2881, 2), (key2881, 2), (key2594, 2)]

def rawRow4986 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2632, 1), (key2632, 1), (key2640, 1), (key2640, 1), (key2642, 1), (key2642, 1), (key2671, 2), (key2671, 2), (key2674, 2), (key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2729, -1), (key2729, -1), (key2786, -1), (key2786, -1), (key2794, -1), (key2794, -1), (key2796, -1), (key2796, -1), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2832, 1), (key2832, 1)]

def rawRow4987 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2640, 1), (key2642, 1), (key2632, 1), (key2642, 1), (key2632, 1), (key2640, 1), (key2671, 2), (key2674, 2), (key2671, 2), (key2726, -1), (key2729, -1), (key2706, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2794, -1), (key2796, -1), (key2786, -1), (key2796, -1), (key2786, -1), (key2794, -1), (key2829, 1), (key2832, 1), (key2809, 1), (key2832, 1), (key2809, 1), (key2829, 1)]

def rawRow4988 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2642, 1), (key2640, 1), (key2642, 1), (key2632, 1), (key2640, 1), (key2632, 1), (key2674, 2), (key2671, 2), (key2671, 2), (key2729, -1), (key2726, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2796, -1), (key2794, -1), (key2796, -1), (key2786, -1), (key2794, -1), (key2786, -1), (key2832, 1), (key2829, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2809, 1)]

def rawRow4989 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2616, 1), (key2616, 1), (key2640, 1), (key2640, 1), (key2654, 1), (key2654, 1), (key2706, 2), (key2706, 2), (key2738, 2), (key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2748, -1), (key2748, -1), (key2809, -1), (key2809, -1), (key2860, -1), (key2860, -1), (key2898, -1), (key2898, -1), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2905, 1), (key2905, 1)]

def rawRow4990 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2640, 1), (key2654, 1), (key2616, 1), (key2654, 1), (key2616, 1), (key2640, 1), (key2706, 2), (key2738, 2), (key2706, 2), (key2726, -1), (key2748, -1), (key2671, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2860, -1), (key2898, -1), (key2809, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2870, 1), (key2905, 1), (key2786, 1), (key2905, 1), (key2786, 1), (key2870, 1)]

def rawRow4991 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2654, 1), (key2640, 1), (key2654, 1), (key2616, 1), (key2640, 1), (key2616, 1), (key2738, 2), (key2706, 2), (key2706, 2), (key2748, -1), (key2726, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2898, -1), (key2860, -1), (key2898, -1), (key2809, -1), (key2860, -1), (key2809, -1), (key2905, 1), (key2870, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2786, 1)]

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

def rawRow4992 : Integer.Sparse Key := [(key2671, -2), (key2671, -2), (key2674, -2), (key2786, 1), (key2786, 1), (key2794, 1), (key2794, 1), (key2796, 1), (key2796, 1), (key2616, 2), (key2616, 2), (key2619, 2), (key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2832, -1), (key2832, -1), (key2632, -1), (key2632, -1), (key2640, -1), (key2640, -1), (key2642, -1), (key2642, -1), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2729, 1), (key2729, 1)]

def rawRow4993 : Integer.Sparse Key := [(key2671, -2), (key2674, -2), (key2671, -2), (key2794, 1), (key2796, 1), (key2786, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2616, 2), (key2619, 2), (key2616, 2), (key2829, -1), (key2832, -1), (key2809, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2640, -1), (key2642, -1), (key2632, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2726, 1), (key2729, 1), (key2706, 1), (key2729, 1), (key2706, 1), (key2726, 1)]

def rawRow4994 : Integer.Sparse Key := [(key2674, -2), (key2671, -2), (key2671, -2), (key2796, 1), (key2794, 1), (key2796, 1), (key2786, 1), (key2794, 1), (key2786, 1), (key2619, 2), (key2616, 2), (key2616, 2), (key2832, -1), (key2829, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2642, -1), (key2640, -1), (key2642, -1), (key2632, -1), (key2640, -1), (key2632, -1), (key2729, 1), (key2726, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2706, 1)]

def rawRow4995 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2671, 1), (key2671, 1), (key2794, 1), (key2794, 1), (key2944, 1), (key2944, 1), (key2809, 2), (key2809, 2), (key2951, 2), (key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2706, -1), (key2706, -1), (key2860, -1), (key2860, -1), (key2977, -1), (key2977, -1), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1)]

def rawRow4996 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2794, 1), (key2944, 1), (key2671, 1), (key2944, 1), (key2671, 1), (key2794, 1), (key2809, 2), (key2951, 2), (key2809, 2), (key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1)]

def rawRow4997 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2944, 1), (key2794, 1), (key2944, 1), (key2671, 1), (key2794, 1), (key2671, 1), (key2951, 2), (key2809, 2), (key2809, 2), (key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2706, -1), (key2860, -1), (key2706, -1), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1)]

def rawRow4998 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2809, 1), (key2809, 1), (key2860, 1), (key2860, 1), (key2898, 1), (key2898, 1), (key2632, 2), (key2632, 2), (key2649, 2), (key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2905, -1), (key2905, -1), (key2616, -1), (key2616, -1), (key2640, -1), (key2640, -1), (key2654, -1), (key2654, -1), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2748, 1), (key2748, 1)]

def rawRow4999 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2860, 1), (key2898, 1), (key2809, 1), (key2898, 1), (key2809, 1), (key2860, 1), (key2632, 2), (key2649, 2), (key2632, 2), (key2870, -1), (key2905, -1), (key2786, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2640, -1), (key2654, -1), (key2616, -1), (key2654, -1), (key2616, -1), (key2640, -1), (key2726, 1), (key2748, 1), (key2671, 1), (key2748, 1), (key2671, 1), (key2726, 1)]

def rawRow5000 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2898, 1), (key2860, 1), (key2898, 1), (key2809, 1), (key2860, 1), (key2809, 1), (key2649, 2), (key2632, 2), (key2632, 2), (key2905, -1), (key2870, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2786, -1), (key2654, -1), (key2640, -1), (key2654, -1), (key2616, -1), (key2640, -1), (key2616, -1), (key2748, 1), (key2726, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2671, 1)]

def rawRow5001 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2706, 1), (key2706, 1), (key2860, 1), (key2860, 1), (key2977, 1), (key2977, 1), (key2786, 2), (key2786, 2), (key2939, 2), (key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2671, -1), (key2671, -1), (key2794, -1), (key2794, -1), (key2944, -1), (key2944, -1), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1)]

def rawRow5002 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2860, 1), (key2977, 1), (key2706, 1), (key2977, 1), (key2706, 1), (key2860, 1), (key2786, 2), (key2939, 2), (key2786, 2), (key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1)]

def rawRow5003 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2977, 1), (key2860, 1), (key2977, 1), (key2706, 1), (key2860, 1), (key2706, 1), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2944, -1), (key2794, -1), (key2944, -1), (key2671, -1), (key2794, -1), (key2671, -1), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1)]

def rawRow5004 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2082, -2), (key2087, 6), (key2175, 2), (key2175, 2), (key2179, 2), (key2281, -2), (key2330, -2), (key2330, -2), (key2189, -6), (key2289, 2), (key2333, 2), (key2333, 2)]

def rawRow5005 : Integer.Sparse Key := [(key2078, -2), (key2082, -2), (key2078, -2), (key2087, 6), (key2175, 2), (key2179, 2), (key2175, 2), (key2330, -2), (key2281, -2), (key2330, -2), (key2189, -6), (key2333, 2), (key2289, 2), (key2333, 2)]

def rawRow5006 : Integer.Sparse Key := [(key2082, -2), (key2078, -2), (key2078, -2), (key2087, 6), (key2179, 2), (key2175, 2), (key2175, 2), (key2330, -2), (key2330, -2), (key2281, -2), (key2189, -6), (key2333, 2), (key2333, 2), (key2289, 2)]

def rawRow5007 : Integer.Sparse Key := [(key2078, -2), (key2078, -2), (key2087, -2), (key2082, 6), (key2275, 2), (key2275, 2), (key2281, 2), (key2179, -2), (key2328, -2), (key2328, -2), (key2289, -6), (key2189, 2), (key2333, 2), (key2333, 2)]

def rawRow5008 : Integer.Sparse Key := [(key2078, -2), (key2087, -2), (key2078, -2), (key2082, 6), (key2275, 2), (key2281, 2), (key2275, 2), (key2328, -2), (key2179, -2), (key2328, -2), (key2289, -6), (key2333, 2), (key2189, 2), (key2333, 2)]

def rawRow5009 : Integer.Sparse Key := [(key2087, -2), (key2078, -2), (key2078, -2), (key2082, 6), (key2281, 2), (key2275, 2), (key2275, 2), (key2328, -2), (key2328, -2), (key2179, -2), (key2289, -6), (key2333, 2), (key2333, 2), (key2189, 2)]

def rawRow5010 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2179, -2), (key2189, 6), (key2078, 2), (key2078, 2), (key2082, 2), (key2289, -2), (key2333, -2), (key2333, -2), (key2087, -6), (key2281, 2), (key2330, 2), (key2330, 2)]

def rawRow5011 : Integer.Sparse Key := [(key2175, -2), (key2179, -2), (key2175, -2), (key2189, 6), (key2078, 2), (key2082, 2), (key2078, 2), (key2333, -2), (key2289, -2), (key2333, -2), (key2087, -6), (key2330, 2), (key2281, 2), (key2330, 2)]

def rawRow5012 : Integer.Sparse Key := [(key2179, -2), (key2175, -2), (key2175, -2), (key2189, 6), (key2082, 2), (key2078, 2), (key2078, 2), (key2333, -2), (key2333, -2), (key2289, -2), (key2087, -6), (key2330, 2), (key2330, 2), (key2281, 2)]

def rawRow5013 : Integer.Sparse Key := [(key2175, -2), (key2175, -2), (key2189, -2), (key2179, 6), (key2275, 2), (key2275, 2), (key2289, 2), (key2082, -2), (key2328, -2), (key2328, -2), (key2281, -6), (key2087, 2), (key2330, 2), (key2330, 2)]

def rawRow5014 : Integer.Sparse Key := [(key2175, -2), (key2189, -2), (key2175, -2), (key2179, 6), (key2275, 2), (key2289, 2), (key2275, 2), (key2328, -2), (key2082, -2), (key2328, -2), (key2281, -6), (key2330, 2), (key2087, 2), (key2330, 2)]

def rawRow5015 : Integer.Sparse Key := [(key2189, -2), (key2175, -2), (key2175, -2), (key2179, 6), (key2289, 2), (key2275, 2), (key2275, 2), (key2328, -2), (key2328, -2), (key2082, -2), (key2281, -6), (key2330, 2), (key2330, 2), (key2087, 2)]

def rawRow5016 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2281, -2), (key2289, 6), (key2078, 2), (key2078, 2), (key2087, 2), (key2189, -2), (key2333, -2), (key2333, -2), (key2082, -6), (key2179, 2), (key2328, 2), (key2328, 2)]

def rawRow5017 : Integer.Sparse Key := [(key2275, -2), (key2281, -2), (key2275, -2), (key2289, 6), (key2078, 2), (key2087, 2), (key2078, 2), (key2333, -2), (key2189, -2), (key2333, -2), (key2082, -6), (key2328, 2), (key2179, 2), (key2328, 2)]

def rawRow5018 : Integer.Sparse Key := [(key2281, -2), (key2275, -2), (key2275, -2), (key2289, 6), (key2087, 2), (key2078, 2), (key2078, 2), (key2333, -2), (key2333, -2), (key2189, -2), (key2082, -6), (key2328, 2), (key2328, 2), (key2179, 2)]

def rawRow5019 : Integer.Sparse Key := [(key2275, -2), (key2275, -2), (key2289, -2), (key2281, 6), (key2175, 2), (key2175, 2), (key2189, 2), (key2087, -2), (key2330, -2), (key2330, -2), (key2179, -6), (key2082, 2), (key2328, 2), (key2328, 2)]

def rawRow5020 : Integer.Sparse Key := [(key2275, -2), (key2289, -2), (key2275, -2), (key2281, 6), (key2175, 2), (key2189, 2), (key2175, 2), (key2330, -2), (key2087, -2), (key2330, -2), (key2179, -6), (key2328, 2), (key2082, 2), (key2328, 2)]

def rawRow5021 : Integer.Sparse Key := [(key2289, -2), (key2275, -2), (key2275, -2), (key2281, 6), (key2189, 2), (key2175, 2), (key2175, 2), (key2330, -2), (key2330, -2), (key2087, -2), (key2179, -6), (key2328, 2), (key2328, 2), (key2082, 2)]

def rawRow5022 : Integer.Sparse Key := [(key2379, -2), (key2382, -2), (key2382, -2), (key2393, 2), (key2393, 2), (key2395, 2), (key2771, 2), (key2774, 2), (key2774, 2), (key2891, -1), (key2891, -1), (key2912, -1), (key2912, -1), (key2914, -1), (key2914, -1), (key2933, -2), (key2933, -2), (key2934, -2), (key2970, 1), (key2970, 1), (key2991, 1), (key2991, 1), (key2993, 1), (key2993, 1)]

def rawRow5023 : Integer.Sparse Key := [(key2382, -2), (key2379, -2), (key2382, -2), (key2393, 2), (key2395, 2), (key2393, 2), (key2774, 2), (key2771, 2), (key2774, 2), (key2912, -1), (key2914, -1), (key2891, -1), (key2914, -1), (key2891, -1), (key2912, -1), (key2933, -2), (key2934, -2), (key2933, -2), (key2991, 1), (key2993, 1), (key2970, 1), (key2993, 1), (key2970, 1), (key2991, 1)]

def rawRow5024 : Integer.Sparse Key := [(key2382, -2), (key2382, -2), (key2379, -2), (key2395, 2), (key2393, 2), (key2393, 2), (key2774, 2), (key2774, 2), (key2771, 2), (key2914, -1), (key2912, -1), (key2914, -1), (key2891, -1), (key2912, -1), (key2891, -1), (key2934, -2), (key2933, -2), (key2933, -2), (key2993, 1), (key2991, 1), (key2993, 1), (key2970, 1), (key2991, 1), (key2970, 1)]

def rawRow5025 : Integer.Sparse Key := [(key2379, -2), (key2393, -2), (key2393, -2), (key2382, 2), (key2382, 2), (key2395, 2), (key2848, 2), (key2891, 2), (key2891, 2), (key2774, -1), (key2774, -1), (key2882, -1), (key2882, -1), (key2914, -1), (key2914, -1), (key2970, -2), (key2970, -2), (key2996, -2), (key2933, 1), (key2933, 1), (key2991, 1), (key2991, 1), (key3003, 1), (key3003, 1)]

def rawRow5026 : Integer.Sparse Key := [(key2393, -2), (key2379, -2), (key2393, -2), (key2382, 2), (key2395, 2), (key2382, 2), (key2891, 2), (key2848, 2), (key2891, 2), (key2882, -1), (key2914, -1), (key2774, -1), (key2914, -1), (key2774, -1), (key2882, -1), (key2970, -2), (key2996, -2), (key2970, -2), (key2991, 1), (key3003, 1), (key2933, 1), (key3003, 1), (key2933, 1), (key2991, 1)]

def rawRow5027 : Integer.Sparse Key := [(key2393, -2), (key2393, -2), (key2379, -2), (key2395, 2), (key2382, 2), (key2382, 2), (key2891, 2), (key2891, 2), (key2848, 2), (key2914, -1), (key2882, -1), (key2914, -1), (key2774, -1), (key2882, -1), (key2774, -1), (key2996, -2), (key2970, -2), (key2970, -2), (key3003, 1), (key2991, 1), (key3003, 1), (key2933, 1), (key2991, 1), (key2933, 1)]

def rawRow5028 : Integer.Sparse Key := [(key2407, -2), (key2410, -2), (key2410, -2), (key2441, 2), (key2441, 2), (key2445, 2), (key2592, 2), (key2595, 2), (key2595, 2), (key2970, -1), (key2970, -1), (key2991, -1), (key2991, -1), (key2993, -1), (key2993, -1), (key2602, -2), (key2602, -2), (key2603, -2), (key2891, 1), (key2891, 1), (key2912, 1), (key2912, 1), (key2914, 1), (key2914, 1)]

def rawRow5029 : Integer.Sparse Key := [(key2410, -2), (key2407, -2), (key2410, -2), (key2441, 2), (key2445, 2), (key2441, 2), (key2595, 2), (key2592, 2), (key2595, 2), (key2991, -1), (key2993, -1), (key2970, -1), (key2993, -1), (key2970, -1), (key2991, -1), (key2602, -2), (key2603, -2), (key2602, -2), (key2912, 1), (key2914, 1), (key2891, 1), (key2914, 1), (key2891, 1), (key2912, 1)]

def rawRow5030 : Integer.Sparse Key := [(key2410, -2), (key2410, -2), (key2407, -2), (key2445, 2), (key2441, 2), (key2441, 2), (key2595, 2), (key2595, 2), (key2592, 2), (key2993, -1), (key2991, -1), (key2993, -1), (key2970, -1), (key2991, -1), (key2970, -1), (key2603, -2), (key2602, -2), (key2602, -2), (key2914, 1), (key2912, 1), (key2914, 1), (key2891, 1), (key2912, 1), (key2891, 1)]

def rawRow5031 : Integer.Sparse Key := [(key2407, -2), (key2441, -2), (key2441, -2), (key2410, 2), (key2410, 2), (key2445, 2), (key2848, 2), (key2970, 2), (key2970, 2), (key2595, -1), (key2595, -1), (key2882, -1), (key2882, -1), (key2993, -1), (key2993, -1), (key2891, -2), (key2891, -2), (key2996, -2), (key2602, 1), (key2602, 1), (key2912, 1), (key2912, 1), (key3003, 1), (key3003, 1)]

def rawRow5032 : Integer.Sparse Key := [(key2441, -2), (key2407, -2), (key2441, -2), (key2410, 2), (key2445, 2), (key2410, 2), (key2970, 2), (key2848, 2), (key2970, 2), (key2882, -1), (key2993, -1), (key2595, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2891, -2), (key2996, -2), (key2891, -2), (key2912, 1), (key3003, 1), (key2602, 1), (key3003, 1), (key2602, 1), (key2912, 1)]

def rawRow5033 : Integer.Sparse Key := [(key2441, -2), (key2441, -2), (key2407, -2), (key2445, 2), (key2410, 2), (key2410, 2), (key2970, 2), (key2970, 2), (key2848, 2), (key2993, -1), (key2882, -1), (key2993, -1), (key2595, -1), (key2882, -1), (key2595, -1), (key2996, -2), (key2891, -2), (key2891, -2), (key3003, 1), (key2912, 1), (key3003, 1), (key2602, 1), (key2912, 1), (key2602, 1)]

def rawRow5034 : Integer.Sparse Key := [(key2473, -2), (key2483, -2), (key2483, -2), (key2507, 2), (key2507, 2), (key2526, 2), (key2379, 2), (key2393, 2), (key2393, 2), (key2933, -1), (key2933, -1), (key2991, -1), (key2991, -1), (key3003, -1), (key3003, -1), (key2595, -2), (key2595, -2), (key2603, -2), (key2774, 1), (key2774, 1), (key2882, 1), (key2882, 1), (key2914, 1), (key2914, 1)]

def rawRow5035 : Integer.Sparse Key := [(key2483, -2), (key2473, -2), (key2483, -2), (key2507, 2), (key2526, 2), (key2507, 2), (key2393, 2), (key2379, 2), (key2393, 2), (key2991, -1), (key3003, -1), (key2933, -1), (key3003, -1), (key2933, -1), (key2991, -1), (key2595, -2), (key2603, -2), (key2595, -2), (key2882, 1), (key2914, 1), (key2774, 1), (key2914, 1), (key2774, 1), (key2882, 1)]

def rawRow5036 : Integer.Sparse Key := [(key2483, -2), (key2483, -2), (key2473, -2), (key2526, 2), (key2507, 2), (key2507, 2), (key2393, 2), (key2393, 2), (key2379, 2), (key3003, -1), (key2991, -1), (key3003, -1), (key2933, -1), (key2991, -1), (key2933, -1), (key2603, -2), (key2595, -2), (key2595, -2), (key2914, 1), (key2882, 1), (key2914, 1), (key2774, 1), (key2882, 1), (key2774, 1)]

def rawRow5037 : Integer.Sparse Key := [(key2473, -2), (key2507, -2), (key2507, -2), (key2483, 2), (key2483, 2), (key2526, 2), (key2407, 2), (key2441, 2), (key2441, 2), (key2602, -1), (key2602, -1), (key2912, -1), (key2912, -1), (key3003, -1), (key3003, -1), (key2774, -2), (key2774, -2), (key2934, -2), (key2595, 1), (key2595, 1), (key2882, 1), (key2882, 1), (key2993, 1), (key2993, 1)]

def rawRow5038 : Integer.Sparse Key := [(key2507, -2), (key2473, -2), (key2507, -2), (key2483, 2), (key2526, 2), (key2483, 2), (key2441, 2), (key2407, 2), (key2441, 2), (key2912, -1), (key3003, -1), (key2602, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2774, -2), (key2934, -2), (key2774, -2), (key2882, 1), (key2993, 1), (key2595, 1), (key2993, 1), (key2595, 1), (key2882, 1)]

def rawRow5039 : Integer.Sparse Key := [(key2507, -2), (key2507, -2), (key2473, -2), (key2526, 2), (key2483, 2), (key2483, 2), (key2441, 2), (key2441, 2), (key2407, 2), (key3003, -1), (key2912, -1), (key3003, -1), (key2602, -1), (key2912, -1), (key2602, -1), (key2934, -2), (key2774, -2), (key2774, -2), (key2993, 1), (key2882, 1), (key2993, 1), (key2595, 1), (key2882, 1), (key2595, 1)]

def rawRow5040 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2732, -1), (key2732, -1), (key2753, 2), (key2758, 2), (key2758, 2), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2835, 1), (key2835, 1), (key2920, -1), (key2920, -1), (key2923, -1), (key2923, -1), (key2927, -1), (key2927, -1), (key3012, -2), (key3017, -2), (key3017, -2), (key3023, 1), (key3023, 1), (key3026, 1), (key3026, 1), (key3030, 1), (key3030, 1)]

def rawRow5041 : Integer.Sparse Key := [(key2726, -1), (key2732, -1), (key2706, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2758, 2), (key2753, 2), (key2758, 2), (key2829, 1), (key2835, 1), (key2809, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2923, -1), (key2927, -1), (key2920, -1), (key2927, -1), (key2920, -1), (key2923, -1), (key3017, -2), (key3012, -2), (key3017, -2), (key3026, 1), (key3030, 1), (key3023, 1), (key3030, 1), (key3023, 1), (key3026, 1)]

def rawRow5042 : Integer.Sparse Key := [(key2732, -1), (key2726, -1), (key2732, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2758, 2), (key2758, 2), (key2753, 2), (key2835, 1), (key2829, 1), (key2835, 1), (key2809, 1), (key2829, 1), (key2809, 1), (key2927, -1), (key2923, -1), (key2927, -1), (key2920, -1), (key2923, -1), (key2920, -1), (key3017, -2), (key3017, -2), (key3012, -2), (key3030, 1), (key3026, 1), (key3030, 1), (key3023, 1), (key3026, 1), (key3023, 1)]

def rawRow5043 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2758, -1), (key2758, -1), (key2676, 2), (key2732, 2), (key2732, 2), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2923, 1), (key2923, 1), (key2798, -1), (key2798, -1), (key2835, -1), (key2835, -1), (key2885, -1), (key2885, -1), (key3008, -2), (key3026, -2), (key3026, -2), (key3010, 1), (key3010, 1), (key3017, 1), (key3017, 1), (key3030, 1), (key3030, 1)]

def rawRow5044 : Integer.Sparse Key := [(key2726, -1), (key2758, -1), (key2671, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2732, 2), (key2676, 2), (key2732, 2), (key2870, 1), (key2923, 1), (key2786, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2835, -1), (key2885, -1), (key2798, -1), (key2885, -1), (key2798, -1), (key2835, -1), (key3026, -2), (key3008, -2), (key3026, -2), (key3017, 1), (key3030, 1), (key3010, 1), (key3030, 1), (key3010, 1), (key3017, 1)]

def rawRow5045 : Integer.Sparse Key := [(key2758, -1), (key2726, -1), (key2758, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2732, 2), (key2732, 2), (key2676, 2), (key2923, 1), (key2870, 1), (key2923, 1), (key2786, 1), (key2870, 1), (key2786, 1), (key2885, -1), (key2835, -1), (key2885, -1), (key2798, -1), (key2835, -1), (key2798, -1), (key3026, -2), (key3026, -2), (key3008, -2), (key3030, 1), (key3017, 1), (key3030, 1), (key3010, 1), (key3017, 1), (key3010, 1)]

def rawRow5046 : Integer.Sparse Key := [(key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2835, -1), (key2835, -1), (key3012, 2), (key3017, 2), (key3017, 2), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2732, 1), (key2732, 1), (key3023, -1), (key3023, -1), (key3026, -1), (key3026, -1), (key3030, -1), (key3030, -1), (key2753, -2), (key2758, -2), (key2758, -2), (key2920, 1), (key2920, 1), (key2923, 1), (key2923, 1), (key2927, 1), (key2927, 1)]

def rawRow5047 : Integer.Sparse Key := [(key2829, -1), (key2835, -1), (key2809, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key3017, 2), (key3012, 2), (key3017, 2), (key2726, 1), (key2732, 1), (key2706, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key3026, -1), (key3030, -1), (key3023, -1), (key3030, -1), (key3023, -1), (key3026, -1), (key2758, -2), (key2753, -2), (key2758, -2), (key2923, 1), (key2927, 1), (key2920, 1), (key2927, 1), (key2920, 1), (key2923, 1)]

def rawRow5048 : Integer.Sparse Key := [(key2835, -1), (key2829, -1), (key2835, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key3017, 2), (key3017, 2), (key3012, 2), (key2732, 1), (key2726, 1), (key2732, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key3030, -1), (key3026, -1), (key3030, -1), (key3023, -1), (key3026, -1), (key3023, -1), (key2758, -2), (key2758, -2), (key2753, -2), (key2927, 1), (key2923, 1), (key2927, 1), (key2920, 1), (key2923, 1), (key2920, 1)]

def rawRow5049 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key3017, -1), (key3017, -1), (key2621, 2), (key2835, 2), (key2835, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key3026, 1), (key3026, 1), (key2644, -1), (key2644, -1), (key2732, -1), (key2732, -1), (key2885, -1), (key2885, -1), (key2658, -2), (key2923, -2), (key2923, -2), (key2660, 1), (key2660, 1), (key2758, 1), (key2758, 1), (key2927, 1), (key2927, 1)]

def rawRow5050 : Integer.Sparse Key := [(key2948, -1), (key2960, -1), (key2612, -1), (key2960, -1), (key2616, -1), (key2829, -1), (key2835, 2), (key2621, 2), (key2835, 2), (key2870, 1), (key3026, 1), (key2632, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2732, -1), (key2885, -1), (key2644, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2923, -2), (key2658, -2), (key2923, -2), (key2758, 1), (key2927, 1), (key2660, 1), (key2927, 1), (key2660, 1), (key2758, 1)]

def rawRow5051 : Integer.Sparse Key := [(key2960, -1), (key2948, -1), (key2960, -1), (key2612, -1), (key2829, -1), (key2616, -1), (key2835, 2), (key2835, 2), (key2621, 2), (key3026, 1), (key2870, 1), (key3026, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2885, -1), (key2732, -1), (key2885, -1), (key2644, -1), (key2732, -1), (key2644, -1), (key2923, -2), (key2923, -2), (key2658, -2), (key2927, 1), (key2758, 1), (key2927, 1), (key2660, 1), (key2758, 1), (key2660, 1)]

def rawRow5052 : Integer.Sparse Key := [(key2702, -1), (key2702, -1), (key2972, -1), (key2972, -1), (key2976, -1), (key2976, -1), (key2728, 2), (key2983, 2), (key2983, 2), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2758, 1), (key2758, 1), (key3010, -1), (key3010, -1), (key3017, -1), (key3017, -1), (key3030, -1), (key3030, -1), (key2676, -2), (key2732, -2), (key2732, -2), (key2798, 1), (key2798, 1), (key2835, 1), (key2835, 1), (key2885, 1), (key2885, 1)]

def rawRow5053 : Integer.Sparse Key := [(key2972, -1), (key2976, -1), (key2702, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2983, 2), (key2728, 2), (key2983, 2), (key2726, 1), (key2758, 1), (key2671, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key3017, -1), (key3030, -1), (key3010, -1), (key3030, -1), (key3010, -1), (key3017, -1), (key2732, -2), (key2676, -2), (key2732, -2), (key2835, 1), (key2885, 1), (key2798, 1), (key2885, 1), (key2798, 1), (key2835, 1)]

def rawRow5054 : Integer.Sparse Key := [(key2976, -1), (key2972, -1), (key2976, -1), (key2702, -1), (key2972, -1), (key2702, -1), (key2983, 2), (key2983, 2), (key2728, 2), (key2758, 1), (key2726, 1), (key2758, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key3030, -1), (key3017, -1), (key3030, -1), (key3010, -1), (key3017, -1), (key3010, -1), (key2732, -2), (key2732, -2), (key2676, -2), (key2885, 1), (key2835, 1), (key2885, 1), (key2798, 1), (key2835, 1), (key2798, 1)]

def rawRow5055 : Integer.Sparse Key := [(key2628, -1), (key2628, -1), (key2972, -1), (key2972, -1), (key2983, -1), (key2983, -1), (key2641, 2), (key2976, 2), (key2976, 2), (key2612, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key3017, 1), (key3017, 1), (key2660, -1), (key2660, -1), (key2758, -1), (key2758, -1), (key2927, -1), (key2927, -1), (key2621, -2), (key2835, -2), (key2835, -2), (key2644, 1), (key2644, 1), (key2732, 1), (key2732, 1), (key2885, 1), (key2885, 1)]

def rawRow5056 : Integer.Sparse Key := [(key2972, -1), (key2983, -1), (key2628, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2976, 2), (key2641, 2), (key2976, 2), (key2948, 1), (key2960, 1), (key2612, 1), (key2960, 1), (key2616, 1), (key2829, 1), (key2758, -1), (key2927, -1), (key2660, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2835, -2), (key2621, -2), (key2835, -2), (key2732, 1), (key2885, 1), (key2644, 1), (key2885, 1), (key2644, 1), (key2732, 1)]

def rawRow5057 : Integer.Sparse Key := [(key2983, -1), (key2972, -1), (key2983, -1), (key2628, -1), (key2972, -1), (key2628, -1), (key2976, 2), (key2976, 2), (key2641, 2), (key2960, 1), (key2948, 1), (key2960, 1), (key2612, 1), (key2829, 1), (key2616, 1), (key2927, -1), (key2758, -1), (key2927, -1), (key2660, -1), (key2758, -1), (key2660, -1), (key2835, -2), (key2835, -2), (key2621, -2), (key2885, 1), (key2732, 1), (key2885, 1), (key2644, 1), (key2732, 1), (key2644, 1)]

def rawRow5058 : Integer.Sparse Key := [(key2616, -2), (key2616, -2), (key2619, -2), (key2649, 2), (key2654, 2), (key2654, 2), (key2671, 2), (key2671, 2), (key2674, 2), (key2738, -2), (key2748, -2), (key2748, -2), (key2939, -2), (key2944, -2), (key2944, -2), (key2951, 2), (key2961, 2), (key2961, 2)]

def rawRow5059 : Integer.Sparse Key := [(key2616, -2), (key2619, -2), (key2616, -2), (key2654, 2), (key2649, 2), (key2654, 2), (key2671, 2), (key2674, 2), (key2671, 2), (key2748, -2), (key2738, -2), (key2748, -2), (key2944, -2), (key2939, -2), (key2944, -2), (key2961, 2), (key2951, 2), (key2961, 2)]

def rawRow5060 : Integer.Sparse Key := [(key2619, -2), (key2616, -2), (key2616, -2), (key2654, 2), (key2654, 2), (key2649, 2), (key2674, 2), (key2671, 2), (key2671, 2), (key2748, -2), (key2748, -2), (key2738, -2), (key2944, -2), (key2944, -2), (key2939, -2), (key2961, 2), (key2961, 2), (key2951, 2)]

def rawRow5061 : Integer.Sparse Key := [(key2632, -2), (key2632, -2), (key2649, -2), (key2619, 2), (key2642, 2), (key2642, 2), (key2706, 2), (key2706, 2), (key2738, 2), (key2674, -2), (key2729, -2), (key2729, -2), (key2951, -2), (key2977, -2), (key2977, -2), (key2939, 2), (key2984, 2), (key2984, 2)]

def rawRow5062 : Integer.Sparse Key := [(key2632, -2), (key2649, -2), (key2632, -2), (key2642, 2), (key2619, 2), (key2642, 2), (key2706, 2), (key2738, 2), (key2706, 2), (key2729, -2), (key2674, -2), (key2729, -2), (key2977, -2), (key2951, -2), (key2977, -2), (key2984, 2), (key2939, 2), (key2984, 2)]

def rawRow5063 : Integer.Sparse Key := [(key2649, -2), (key2632, -2), (key2632, -2), (key2642, 2), (key2642, 2), (key2619, 2), (key2738, 2), (key2706, 2), (key2706, 2), (key2729, -2), (key2729, -2), (key2674, -2), (key2977, -2), (key2977, -2), (key2951, -2), (key2984, 2), (key2984, 2), (key2939, 2)]

def rawRow5064 : Integer.Sparse Key := [(key2671, -2), (key2671, -2), (key2674, -2), (key2939, 2), (key2944, 2), (key2944, 2), (key2616, 2), (key2616, 2), (key2619, 2), (key2951, -2), (key2961, -2), (key2961, -2), (key2649, -2), (key2654, -2), (key2654, -2), (key2738, 2), (key2748, 2), (key2748, 2)]

def rawRow5065 : Integer.Sparse Key := [(key2671, -2), (key2674, -2), (key2671, -2), (key2944, 2), (key2939, 2), (key2944, 2), (key2616, 2), (key2619, 2), (key2616, 2), (key2961, -2), (key2951, -2), (key2961, -2), (key2654, -2), (key2649, -2), (key2654, -2), (key2748, 2), (key2738, 2), (key2748, 2)]

def rawRow5066 : Integer.Sparse Key := [(key2674, -2), (key2671, -2), (key2671, -2), (key2944, 2), (key2944, 2), (key2939, 2), (key2619, 2), (key2616, 2), (key2616, 2), (key2961, -2), (key2961, -2), (key2951, -2), (key2654, -2), (key2654, -2), (key2649, -2), (key2748, 2), (key2748, 2), (key2738, 2)]

def rawRow5067 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2674, 2), (key2796, 2), (key2796, 2), (key2809, 2), (key2809, 2), (key2951, 2), (key2619, -2), (key2832, -2), (key2832, -2), (key2738, -2), (key2898, -2), (key2898, -2), (key2649, 2), (key2905, 2), (key2905, 2)]

def rawRow5068 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2796, 2), (key2674, 2), (key2796, 2), (key2809, 2), (key2951, 2), (key2809, 2), (key2832, -2), (key2619, -2), (key2832, -2), (key2898, -2), (key2738, -2), (key2898, -2), (key2905, 2), (key2649, 2), (key2905, 2)]

def rawRow5069 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2796, 2), (key2796, 2), (key2674, 2), (key2951, 2), (key2809, 2), (key2809, 2), (key2832, -2), (key2832, -2), (key2619, -2), (key2898, -2), (key2898, -2), (key2738, -2), (key2905, 2), (key2905, 2), (key2649, 2)]

def rawRow5070 : Integer.Sparse Key := [(key2706, -2), (key2706, -2), (key2738, -2), (key2951, 2), (key2977, 2), (key2977, 2), (key2632, 2), (key2632, 2), (key2649, 2), (key2939, -2), (key2984, -2), (key2984, -2), (key2619, -2), (key2642, -2), (key2642, -2), (key2674, 2), (key2729, 2), (key2729, 2)]

def rawRow5071 : Integer.Sparse Key := [(key2706, -2), (key2738, -2), (key2706, -2), (key2977, 2), (key2951, 2), (key2977, 2), (key2632, 2), (key2649, 2), (key2632, 2), (key2984, -2), (key2939, -2), (key2984, -2), (key2642, -2), (key2619, -2), (key2642, -2), (key2729, 2), (key2674, 2), (key2729, 2)]

def rawRow5072 : Integer.Sparse Key := [(key2738, -2), (key2706, -2), (key2706, -2), (key2977, 2), (key2977, 2), (key2951, 2), (key2649, 2), (key2632, 2), (key2632, 2), (key2984, -2), (key2984, -2), (key2939, -2), (key2642, -2), (key2642, -2), (key2619, -2), (key2729, 2), (key2729, 2), (key2674, 2)]

def rawRow5073 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2738, 2), (key2898, 2), (key2898, 2), (key2786, 2), (key2786, 2), (key2939, 2), (key2649, -2), (key2905, -2), (key2905, -2), (key2674, -2), (key2796, -2), (key2796, -2), (key2619, 2), (key2832, 2), (key2832, 2)]

def rawRow5074 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2898, 2), (key2738, 2), (key2898, 2), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, -2), (key2649, -2), (key2905, -2), (key2796, -2), (key2674, -2), (key2796, -2), (key2832, 2), (key2619, 2), (key2832, 2)]

def rawRow5075 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2898, 2), (key2898, 2), (key2738, 2), (key2939, 2), (key2786, 2), (key2786, 2), (key2905, -2), (key2905, -2), (key2649, -2), (key2796, -2), (key2796, -2), (key2674, -2), (key2832, 2), (key2832, 2), (key2619, 2)]

def rawRow5076 : Integer.Sparse Key := [(key1546, -1), (key1546, -1), (key1772, -1), (key1772, -1), (key1774, -1), (key1774, -1), (key1559, 2), (key1780, 2), (key1780, 2), (key1573, 1), (key1573, 1), (key1788, 1), (key1788, 1), (key1790, 1), (key1790, 1), (key1659, -1), (key1659, -1), (key1817, -1), (key1817, -1), (key1841, -1), (key1841, -1), (key1596, -2), (key1798, -2), (key1798, -2), (key1667, 1), (key1667, 1), (key1825, 1), (key1825, 1), (key1844, 1), (key1844, 1)]

def rawRow5077 : Integer.Sparse Key := [(key1772, -1), (key1774, -1), (key1546, -1), (key1774, -1), (key1546, -1), (key1772, -1), (key1780, 2), (key1559, 2), (key1780, 2), (key1788, 1), (key1790, 1), (key1573, 1), (key1790, 1), (key1573, 1), (key1788, 1), (key1817, -1), (key1841, -1), (key1659, -1), (key1841, -1), (key1659, -1), (key1817, -1), (key1798, -2), (key1596, -2), (key1798, -2), (key1825, 1), (key1844, 1), (key1667, 1), (key1844, 1), (key1667, 1), (key1825, 1)]

def rawRow5078 : Integer.Sparse Key := [(key1774, -1), (key1772, -1), (key1774, -1), (key1546, -1), (key1772, -1), (key1546, -1), (key1780, 2), (key1780, 2), (key1559, 2), (key1790, 1), (key1788, 1), (key1790, 1), (key1573, 1), (key1788, 1), (key1573, 1), (key1841, -1), (key1817, -1), (key1841, -1), (key1659, -1), (key1817, -1), (key1659, -1), (key1798, -2), (key1798, -2), (key1596, -2), (key1844, 1), (key1825, 1), (key1844, 1), (key1667, 1), (key1825, 1), (key1667, 1)]

def rawRow5079 : Integer.Sparse Key := [(key1391, -1), (key1391, -1), (key1772, -1), (key1772, -1), (key1780, -1), (key1780, -1), (key1397, 2), (key1774, 2), (key1774, 2), (key1424, 1), (key1424, 1), (key1813, 1), (key1813, 1), (key1817, 1), (key1817, 1), (key1457, -1), (key1457, -1), (key1790, -1), (key1790, -1), (key1839, -1), (key1839, -1), (key1447, -2), (key1825, -2), (key1825, -2), (key1466, 1), (key1466, 1), (key1798, 1), (key1798, 1), (key1844, 1), (key1844, 1)]

def rawRow5080 : Integer.Sparse Key := [(key1772, -1), (key1780, -1), (key1391, -1), (key1780, -1), (key1391, -1), (key1772, -1), (key1774, 2), (key1397, 2), (key1774, 2), (key1813, 1), (key1817, 1), (key1424, 1), (key1817, 1), (key1424, 1), (key1813, 1), (key1790, -1), (key1839, -1), (key1457, -1), (key1839, -1), (key1457, -1), (key1790, -1), (key1825, -2), (key1447, -2), (key1825, -2), (key1798, 1), (key1844, 1), (key1466, 1), (key1844, 1), (key1466, 1), (key1798, 1)]

def rawRow5081 : Integer.Sparse Key := [(key1780, -1), (key1772, -1), (key1780, -1), (key1391, -1), (key1772, -1), (key1391, -1), (key1774, 2), (key1774, 2), (key1397, 2), (key1817, 1), (key1813, 1), (key1817, 1), (key1424, 1), (key1813, 1), (key1424, 1), (key1839, -1), (key1790, -1), (key1839, -1), (key1457, -1), (key1790, -1), (key1457, -1), (key1825, -2), (key1825, -2), (key1447, -2), (key1844, 1), (key1798, 1), (key1844, 1), (key1466, 1), (key1798, 1), (key1466, 1)]

def rawRow5082 : Integer.Sparse Key := [(key1573, -1), (key1573, -1), (key1788, -1), (key1788, -1), (key1790, -1), (key1790, -1), (key1596, 2), (key1798, 2), (key1798, 2), (key1546, 1), (key1546, 1), (key1772, 1), (key1772, 1), (key1774, 1), (key1774, 1), (key1667, -1), (key1667, -1), (key1825, -1), (key1825, -1), (key1844, -1), (key1844, -1), (key1559, -2), (key1780, -2), (key1780, -2), (key1659, 1), (key1659, 1), (key1817, 1), (key1817, 1), (key1841, 1), (key1841, 1)]

def rawRow5083 : Integer.Sparse Key := [(key1788, -1), (key1790, -1), (key1573, -1), (key1790, -1), (key1573, -1), (key1788, -1), (key1798, 2), (key1596, 2), (key1798, 2), (key1772, 1), (key1774, 1), (key1546, 1), (key1774, 1), (key1546, 1), (key1772, 1), (key1825, -1), (key1844, -1), (key1667, -1), (key1844, -1), (key1667, -1), (key1825, -1), (key1780, -2), (key1559, -2), (key1780, -2), (key1817, 1), (key1841, 1), (key1659, 1), (key1841, 1), (key1659, 1), (key1817, 1)]

def rawRow5084 : Integer.Sparse Key := [(key1790, -1), (key1788, -1), (key1790, -1), (key1573, -1), (key1788, -1), (key1573, -1), (key1798, 2), (key1798, 2), (key1596, 2), (key1774, 1), (key1772, 1), (key1774, 1), (key1546, 1), (key1772, 1), (key1546, 1), (key1844, -1), (key1825, -1), (key1844, -1), (key1667, -1), (key1825, -1), (key1667, -1), (key1780, -2), (key1780, -2), (key1559, -2), (key1841, 1), (key1817, 1), (key1841, 1), (key1659, 1), (key1817, 1), (key1659, 1)]

def rawRow5085 : Integer.Sparse Key := [(key1296, -1), (key1296, -1), (key1788, -1), (key1788, -1), (key1798, -1), (key1798, -1), (key1302, 2), (key1790, 2), (key1790, 2), (key1316, 1), (key1316, 1), (key1813, 1), (key1813, 1), (key1825, 1), (key1825, 1), (key1339, -1), (key1339, -1), (key1774, -1), (key1774, -1), (key1839, -1), (key1839, -1), (key1329, -2), (key1817, -2), (key1817, -2), (key1345, 1), (key1345, 1), (key1780, 1), (key1780, 1), (key1841, 1), (key1841, 1)]

def rawRow5086 : Integer.Sparse Key := [(key1788, -1), (key1798, -1), (key1296, -1), (key1798, -1), (key1296, -1), (key1788, -1), (key1790, 2), (key1302, 2), (key1790, 2), (key1813, 1), (key1825, 1), (key1316, 1), (key1825, 1), (key1316, 1), (key1813, 1), (key1774, -1), (key1839, -1), (key1339, -1), (key1839, -1), (key1339, -1), (key1774, -1), (key1817, -2), (key1329, -2), (key1817, -2), (key1780, 1), (key1841, 1), (key1345, 1), (key1841, 1), (key1345, 1), (key1780, 1)]

def rawRow5087 : Integer.Sparse Key := [(key1798, -1), (key1788, -1), (key1798, -1), (key1296, -1), (key1788, -1), (key1296, -1), (key1790, 2), (key1790, 2), (key1302, 2), (key1825, 1), (key1813, 1), (key1825, 1), (key1316, 1), (key1813, 1), (key1316, 1), (key1839, -1), (key1774, -1), (key1839, -1), (key1339, -1), (key1774, -1), (key1339, -1), (key1817, -2), (key1817, -2), (key1329, -2), (key1841, 1), (key1780, 1), (key1841, 1), (key1345, 1), (key1780, 1), (key1345, 1)]

def rawRow5088 : Integer.Sparse Key := [(key1424, -1), (key1424, -1), (key1813, -1), (key1813, -1), (key1817, -1), (key1817, -1), (key1447, 2), (key1825, 2), (key1825, 2), (key1391, 1), (key1391, 1), (key1772, 1), (key1772, 1), (key1780, 1), (key1780, 1), (key1466, -1), (key1466, -1), (key1798, -1), (key1798, -1), (key1844, -1), (key1844, -1), (key1397, -2), (key1774, -2), (key1774, -2), (key1457, 1), (key1457, 1), (key1790, 1), (key1790, 1), (key1839, 1), (key1839, 1)]

def rawRow5089 : Integer.Sparse Key := [(key1813, -1), (key1817, -1), (key1424, -1), (key1817, -1), (key1424, -1), (key1813, -1), (key1825, 2), (key1447, 2), (key1825, 2), (key1772, 1), (key1780, 1), (key1391, 1), (key1780, 1), (key1391, 1), (key1772, 1), (key1798, -1), (key1844, -1), (key1466, -1), (key1844, -1), (key1466, -1), (key1798, -1), (key1774, -2), (key1397, -2), (key1774, -2), (key1790, 1), (key1839, 1), (key1457, 1), (key1839, 1), (key1457, 1), (key1790, 1)]

def rawRow5090 : Integer.Sparse Key := [(key1817, -1), (key1813, -1), (key1817, -1), (key1424, -1), (key1813, -1), (key1424, -1), (key1825, 2), (key1825, 2), (key1447, 2), (key1780, 1), (key1772, 1), (key1780, 1), (key1391, 1), (key1772, 1), (key1391, 1), (key1844, -1), (key1798, -1), (key1844, -1), (key1466, -1), (key1798, -1), (key1466, -1), (key1774, -2), (key1774, -2), (key1397, -2), (key1839, 1), (key1790, 1), (key1839, 1), (key1457, 1), (key1790, 1), (key1457, 1)]

def rawRow5091 : Integer.Sparse Key := [(key1316, -1), (key1316, -1), (key1813, -1), (key1813, -1), (key1825, -1), (key1825, -1), (key1329, 2), (key1817, 2), (key1817, 2), (key1296, 1), (key1296, 1), (key1788, 1), (key1788, 1), (key1798, 1), (key1798, 1), (key1345, -1), (key1345, -1), (key1780, -1), (key1780, -1), (key1841, -1), (key1841, -1), (key1302, -2), (key1790, -2), (key1790, -2), (key1339, 1), (key1339, 1), (key1774, 1), (key1774, 1), (key1839, 1), (key1839, 1)]

def rawRow5092 : Integer.Sparse Key := [(key1813, -1), (key1825, -1), (key1316, -1), (key1825, -1), (key1316, -1), (key1813, -1), (key1817, 2), (key1329, 2), (key1817, 2), (key1788, 1), (key1798, 1), (key1296, 1), (key1798, 1), (key1296, 1), (key1788, 1), (key1780, -1), (key1841, -1), (key1345, -1), (key1841, -1), (key1345, -1), (key1780, -1), (key1790, -2), (key1302, -2), (key1790, -2), (key1774, 1), (key1839, 1), (key1339, 1), (key1839, 1), (key1339, 1), (key1774, 1)]

def rawRow5093 : Integer.Sparse Key := [(key1825, -1), (key1813, -1), (key1825, -1), (key1316, -1), (key1813, -1), (key1316, -1), (key1817, 2), (key1817, 2), (key1329, 2), (key1798, 1), (key1788, 1), (key1798, 1), (key1296, 1), (key1788, 1), (key1296, 1), (key1841, -1), (key1780, -1), (key1841, -1), (key1345, -1), (key1780, -1), (key1345, -1), (key1790, -2), (key1790, -2), (key1302, -2), (key1839, 1), (key1774, 1), (key1839, 1), (key1339, 1), (key1774, 1), (key1339, 1)]

def rawRow5094 : Integer.Sparse Key := [(key2706, -1), (key2706, -1), (key2726, -1), (key2726, -1), (key2729, -1), (key2729, -1), (key2738, 2), (key2748, 2), (key2748, 2), (key2809, 1), (key2809, 1), (key2829, 1), (key2829, 1), (key2832, 1), (key2832, 1), (key2898, -1), (key2898, -1), (key2905, -1), (key2905, -1), (key2913, -1), (key2913, -1), (key2951, -2), (key2961, -2), (key2961, -2), (key2977, 1), (key2977, 1), (key2984, 1), (key2984, 1), (key2992, 1), (key2992, 1)]

def rawRow5095 : Integer.Sparse Key := [(key2726, -1), (key2729, -1), (key2706, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2748, 2), (key2738, 2), (key2748, 2), (key2829, 1), (key2832, 1), (key2809, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2905, -1), (key2913, -1), (key2898, -1), (key2913, -1), (key2898, -1), (key2905, -1), (key2961, -2), (key2951, -2), (key2961, -2), (key2984, 1), (key2992, 1), (key2977, 1), (key2992, 1), (key2977, 1), (key2984, 1)]

def rawRow5096 : Integer.Sparse Key := [(key2729, -1), (key2726, -1), (key2729, -1), (key2706, -1), (key2726, -1), (key2706, -1), (key2748, 2), (key2748, 2), (key2738, 2), (key2832, 1), (key2829, 1), (key2832, 1), (key2809, 1), (key2829, 1), (key2809, 1), (key2913, -1), (key2905, -1), (key2913, -1), (key2898, -1), (key2905, -1), (key2898, -1), (key2961, -2), (key2961, -2), (key2951, -2), (key2992, 1), (key2984, 1), (key2992, 1), (key2977, 1), (key2984, 1), (key2977, 1)]

def rawRow5097 : Integer.Sparse Key := [(key2671, -1), (key2671, -1), (key2726, -1), (key2726, -1), (key2748, -1), (key2748, -1), (key2674, 2), (key2729, 2), (key2729, 2), (key2786, 1), (key2786, 1), (key2870, 1), (key2870, 1), (key2905, 1), (key2905, 1), (key2796, -1), (key2796, -1), (key2832, -1), (key2832, -1), (key2883, -1), (key2883, -1), (key2939, -2), (key2984, -2), (key2984, -2), (key2944, 1), (key2944, 1), (key2961, 1), (key2961, 1), (key2992, 1), (key2992, 1)]

def rawRow5098 : Integer.Sparse Key := [(key2726, -1), (key2748, -1), (key2671, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2729, 2), (key2674, 2), (key2729, 2), (key2870, 1), (key2905, 1), (key2786, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2832, -1), (key2883, -1), (key2796, -1), (key2883, -1), (key2796, -1), (key2832, -1), (key2984, -2), (key2939, -2), (key2984, -2), (key2961, 1), (key2992, 1), (key2944, 1), (key2992, 1), (key2944, 1), (key2961, 1)]

def rawRow5099 : Integer.Sparse Key := [(key2748, -1), (key2726, -1), (key2748, -1), (key2671, -1), (key2726, -1), (key2671, -1), (key2729, 2), (key2729, 2), (key2674, 2), (key2905, 1), (key2870, 1), (key2905, 1), (key2786, 1), (key2870, 1), (key2786, 1), (key2883, -1), (key2832, -1), (key2883, -1), (key2796, -1), (key2832, -1), (key2796, -1), (key2984, -2), (key2984, -2), (key2939, -2), (key2992, 1), (key2961, 1), (key2992, 1), (key2944, 1), (key2961, 1), (key2944, 1)]

def rawRow5100 : Integer.Sparse Key := [(key2809, -1), (key2809, -1), (key2829, -1), (key2829, -1), (key2832, -1), (key2832, -1), (key2951, 2), (key2961, 2), (key2961, 2), (key2706, 1), (key2706, 1), (key2726, 1), (key2726, 1), (key2729, 1), (key2729, 1), (key2977, -1), (key2977, -1), (key2984, -1), (key2984, -1), (key2992, -1), (key2992, -1), (key2738, -2), (key2748, -2), (key2748, -2), (key2898, 1), (key2898, 1), (key2905, 1), (key2905, 1), (key2913, 1), (key2913, 1)]

def rawRow5101 : Integer.Sparse Key := [(key2829, -1), (key2832, -1), (key2809, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2961, 2), (key2951, 2), (key2961, 2), (key2726, 1), (key2729, 1), (key2706, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2984, -1), (key2992, -1), (key2977, -1), (key2992, -1), (key2977, -1), (key2984, -1), (key2748, -2), (key2738, -2), (key2748, -2), (key2905, 1), (key2913, 1), (key2898, 1), (key2913, 1), (key2898, 1), (key2905, 1)]

def rawRow5102 : Integer.Sparse Key := [(key2832, -1), (key2829, -1), (key2832, -1), (key2809, -1), (key2829, -1), (key2809, -1), (key2961, 2), (key2961, 2), (key2951, 2), (key2729, 1), (key2726, 1), (key2729, 1), (key2706, 1), (key2726, 1), (key2706, 1), (key2992, -1), (key2984, -1), (key2992, -1), (key2977, -1), (key2984, -1), (key2977, -1), (key2748, -2), (key2748, -2), (key2738, -2), (key2913, 1), (key2905, 1), (key2913, 1), (key2898, 1), (key2905, 1), (key2898, 1)]

def rawRow5103 : Integer.Sparse Key := [(key2616, -1), (key2616, -1), (key2829, -1), (key2829, -1), (key2961, -1), (key2961, -1), (key2619, 2), (key2832, 2), (key2832, 2), (key2632, 1), (key2632, 1), (key2870, 1), (key2870, 1), (key2984, 1), (key2984, 1), (key2642, -1), (key2642, -1), (key2729, -1), (key2729, -1), (key2883, -1), (key2883, -1), (key2649, -2), (key2905, -2), (key2905, -2), (key2654, 1), (key2654, 1), (key2748, 1), (key2748, 1), (key2913, 1), (key2913, 1)]

def rawRow5104 : Integer.Sparse Key := [(key2829, -1), (key2961, -1), (key2616, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2832, 2), (key2619, 2), (key2832, 2), (key2870, 1), (key2984, 1), (key2632, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2729, -1), (key2883, -1), (key2642, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2905, -2), (key2649, -2), (key2905, -2), (key2748, 1), (key2913, 1), (key2654, 1), (key2913, 1), (key2654, 1), (key2748, 1)]

def rawRow5105 : Integer.Sparse Key := [(key2961, -1), (key2829, -1), (key2961, -1), (key2616, -1), (key2829, -1), (key2616, -1), (key2832, 2), (key2832, 2), (key2619, 2), (key2984, 1), (key2870, 1), (key2984, 1), (key2632, 1), (key2870, 1), (key2632, 1), (key2883, -1), (key2729, -1), (key2883, -1), (key2642, -1), (key2729, -1), (key2642, -1), (key2905, -2), (key2905, -2), (key2649, -2), (key2913, 1), (key2748, 1), (key2913, 1), (key2654, 1), (key2748, 1), (key2654, 1)]

def rawRow5106 : Integer.Sparse Key := [(key2786, -1), (key2786, -1), (key2870, -1), (key2870, -1), (key2905, -1), (key2905, -1), (key2939, 2), (key2984, 2), (key2984, 2), (key2671, 1), (key2671, 1), (key2726, 1), (key2726, 1), (key2748, 1), (key2748, 1), (key2944, -1), (key2944, -1), (key2961, -1), (key2961, -1), (key2992, -1), (key2992, -1), (key2674, -2), (key2729, -2), (key2729, -2), (key2796, 1), (key2796, 1), (key2832, 1), (key2832, 1), (key2883, 1), (key2883, 1)]

def rawRow5107 : Integer.Sparse Key := [(key2870, -1), (key2905, -1), (key2786, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2984, 2), (key2939, 2), (key2984, 2), (key2726, 1), (key2748, 1), (key2671, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2961, -1), (key2992, -1), (key2944, -1), (key2992, -1), (key2944, -1), (key2961, -1), (key2729, -2), (key2674, -2), (key2729, -2), (key2832, 1), (key2883, 1), (key2796, 1), (key2883, 1), (key2796, 1), (key2832, 1)]

def rawRow5108 : Integer.Sparse Key := [(key2905, -1), (key2870, -1), (key2905, -1), (key2786, -1), (key2870, -1), (key2786, -1), (key2984, 2), (key2984, 2), (key2939, 2), (key2748, 1), (key2726, 1), (key2748, 1), (key2671, 1), (key2726, 1), (key2671, 1), (key2992, -1), (key2961, -1), (key2992, -1), (key2944, -1), (key2961, -1), (key2944, -1), (key2729, -2), (key2729, -2), (key2674, -2), (key2883, 1), (key2832, 1), (key2883, 1), (key2796, 1), (key2832, 1), (key2796, 1)]

def rawRow5109 : Integer.Sparse Key := [(key2632, -1), (key2632, -1), (key2870, -1), (key2870, -1), (key2984, -1), (key2984, -1), (key2649, 2), (key2905, 2), (key2905, 2), (key2616, 1), (key2616, 1), (key2829, 1), (key2829, 1), (key2961, 1), (key2961, 1), (key2654, -1), (key2654, -1), (key2748, -1), (key2748, -1), (key2913, -1), (key2913, -1), (key2619, -2), (key2832, -2), (key2832, -2), (key2642, 1), (key2642, 1), (key2729, 1), (key2729, 1), (key2883, 1), (key2883, 1)]

def rawRow5110 : Integer.Sparse Key := [(key2870, -1), (key2984, -1), (key2632, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2905, 2), (key2649, 2), (key2905, 2), (key2829, 1), (key2961, 1), (key2616, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2748, -1), (key2913, -1), (key2654, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2832, -2), (key2619, -2), (key2832, -2), (key2729, 1), (key2883, 1), (key2642, 1), (key2883, 1), (key2642, 1), (key2729, 1)]

def rawRow5111 : Integer.Sparse Key := [(key2984, -1), (key2870, -1), (key2984, -1), (key2632, -1), (key2870, -1), (key2632, -1), (key2905, 2), (key2905, 2), (key2649, 2), (key2961, 1), (key2829, 1), (key2961, 1), (key2616, 1), (key2829, 1), (key2616, 1), (key2913, -1), (key2748, -1), (key2913, -1), (key2654, -1), (key2748, -1), (key2654, -1), (key2832, -2), (key2832, -2), (key2619, -2), (key2883, 1), (key2729, 1), (key2883, 1), (key2642, 1), (key2729, 1), (key2642, 1)]

def rawRow5112 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1370, -2), (key1379, 6), (key1492, 2), (key1492, 2), (key1496, 2), (key1728, -2), (key1870, -2), (key1870, -2), (key1519, -6), (key1747, 2), (key1880, 2), (key1880, 2)]

def rawRow5113 : Integer.Sparse Key := [(key1366, -2), (key1370, -2), (key1366, -2), (key1379, 6), (key1492, 2), (key1496, 2), (key1492, 2), (key1870, -2), (key1728, -2), (key1870, -2), (key1519, -6), (key1880, 2), (key1747, 2), (key1880, 2)]

def rawRow5114 : Integer.Sparse Key := [(key1370, -2), (key1366, -2), (key1366, -2), (key1379, 6), (key1496, 2), (key1492, 2), (key1492, 2), (key1870, -2), (key1870, -2), (key1728, -2), (key1519, -6), (key1880, 2), (key1880, 2), (key1747, 2)]

def rawRow5115 : Integer.Sparse Key := [(key1366, -2), (key1366, -2), (key1379, -2), (key1370, 6), (key1718, 2), (key1718, 2), (key1728, 2), (key1496, -2), (key1865, -2), (key1865, -2), (key1747, -6), (key1519, 2), (key1880, 2), (key1880, 2)]

def rawRow5116 : Integer.Sparse Key := [(key1366, -2), (key1379, -2), (key1366, -2), (key1370, 6), (key1718, 2), (key1728, 2), (key1718, 2), (key1865, -2), (key1496, -2), (key1865, -2), (key1747, -6), (key1880, 2), (key1519, 2), (key1880, 2)]

def rawRow5117 : Integer.Sparse Key := [(key1379, -2), (key1366, -2), (key1366, -2), (key1370, 6), (key1728, 2), (key1718, 2), (key1718, 2), (key1865, -2), (key1865, -2), (key1496, -2), (key1747, -6), (key1880, 2), (key1880, 2), (key1519, 2)]

def rawRow5118 : Integer.Sparse Key := [(key1492, -2), (key1492, -2), (key1496, -2), (key1519, 6), (key1366, 2), (key1366, 2), (key1370, 2), (key1747, -2), (key1880, -2), (key1880, -2), (key1379, -6), (key1728, 2), (key1870, 2), (key1870, 2)]

def rawRow5119 : Integer.Sparse Key := [(key1492, -2), (key1496, -2), (key1492, -2), (key1519, 6), (key1366, 2), (key1370, 2), (key1366, 2), (key1880, -2), (key1747, -2), (key1880, -2), (key1379, -6), (key1870, 2), (key1728, 2), (key1870, 2)]

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

def rawRow5120 : Integer.Sparse Key := [(key1496, -2), (key1492, -2), (key1492, -2), (key1519, 6), (key1370, 2), (key1366, 2), (key1366, 2), (key1880, -2), (key1880, -2), (key1747, -2), (key1379, -6), (key1870, 2), (key1870, 2), (key1728, 2)]

def rawRow5121 : Integer.Sparse Key := [(key1492, -2), (key1492, -2), (key1519, -2), (key1496, 6), (key1718, 2), (key1718, 2), (key1747, 2), (key1370, -2), (key1865, -2), (key1865, -2), (key1728, -6), (key1379, 2), (key1870, 2), (key1870, 2)]

def rawRow5122 : Integer.Sparse Key := [(key1492, -2), (key1519, -2), (key1492, -2), (key1496, 6), (key1718, 2), (key1747, 2), (key1718, 2), (key1865, -2), (key1370, -2), (key1865, -2), (key1728, -6), (key1870, 2), (key1379, 2), (key1870, 2)]

def rawRow5123 : Integer.Sparse Key := [(key1519, -2), (key1492, -2), (key1492, -2), (key1496, 6), (key1747, 2), (key1718, 2), (key1718, 2), (key1865, -2), (key1865, -2), (key1370, -2), (key1728, -6), (key1870, 2), (key1870, 2), (key1379, 2)]

def rawRow5124 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1728, -2), (key1747, 6), (key1366, 2), (key1366, 2), (key1379, 2), (key1519, -2), (key1880, -2), (key1880, -2), (key1370, -6), (key1496, 2), (key1865, 2), (key1865, 2)]

def rawRow5125 : Integer.Sparse Key := [(key1718, -2), (key1728, -2), (key1718, -2), (key1747, 6), (key1366, 2), (key1379, 2), (key1366, 2), (key1880, -2), (key1519, -2), (key1880, -2), (key1370, -6), (key1865, 2), (key1496, 2), (key1865, 2)]

def rawRow5126 : Integer.Sparse Key := [(key1728, -2), (key1718, -2), (key1718, -2), (key1747, 6), (key1379, 2), (key1366, 2), (key1366, 2), (key1880, -2), (key1880, -2), (key1519, -2), (key1370, -6), (key1865, 2), (key1865, 2), (key1496, 2)]

def rawRow5127 : Integer.Sparse Key := [(key1718, -2), (key1718, -2), (key1747, -2), (key1728, 6), (key1492, 2), (key1492, 2), (key1519, 2), (key1379, -2), (key1870, -2), (key1870, -2), (key1496, -6), (key1370, 2), (key1865, 2), (key1865, 2)]

def rawRow5128 : Integer.Sparse Key := [(key1718, -2), (key1747, -2), (key1718, -2), (key1728, 6), (key1492, 2), (key1519, 2), (key1492, 2), (key1870, -2), (key1379, -2), (key1870, -2), (key1496, -6), (key1865, 2), (key1370, 2), (key1865, 2)]

def rawRow5129 : Integer.Sparse Key := [(key1747, -2), (key1718, -2), (key1718, -2), (key1728, 6), (key1519, 2), (key1492, 2), (key1492, 2), (key1870, -2), (key1870, -2), (key1379, -2), (key1496, -6), (key1865, 2), (key1865, 2), (key1370, 2)]

def rawRow5130 : Integer.Sparse Key := [(key2617, -2), (key2620, -2), (key2620, -2), (key2633, 2), (key2643, 2), (key2643, 2), (key2672, 2), (key2675, 2), (key2675, 2), (key2707, -2), (key2730, -2), (key2730, -2), (key2787, -2), (key2797, -2), (key2797, -2), (key2810, 2), (key2833, 2), (key2833, 2)]

def rawRow5131 : Integer.Sparse Key := [(key2620, -2), (key2617, -2), (key2620, -2), (key2643, 2), (key2633, 2), (key2643, 2), (key2675, 2), (key2672, 2), (key2675, 2), (key2730, -2), (key2707, -2), (key2730, -2), (key2797, -2), (key2787, -2), (key2797, -2), (key2833, 2), (key2810, 2), (key2833, 2)]

def rawRow5132 : Integer.Sparse Key := [(key2620, -2), (key2620, -2), (key2617, -2), (key2643, 2), (key2643, 2), (key2633, 2), (key2675, 2), (key2675, 2), (key2672, 2), (key2730, -2), (key2730, -2), (key2707, -2), (key2797, -2), (key2797, -2), (key2787, -2), (key2833, 2), (key2833, 2), (key2810, 2)]

def rawRow5133 : Integer.Sparse Key := [(key2633, -2), (key2643, -2), (key2643, -2), (key2617, 2), (key2655, 2), (key2655, 2), (key2707, 2), (key2739, 2), (key2739, 2), (key2672, -2), (key2749, -2), (key2749, -2), (key2810, -2), (key2899, -2), (key2899, -2), (key2787, 2), (key2906, 2), (key2906, 2)]

def rawRow5134 : Integer.Sparse Key := [(key2643, -2), (key2633, -2), (key2643, -2), (key2655, 2), (key2617, 2), (key2655, 2), (key2739, 2), (key2707, 2), (key2739, 2), (key2749, -2), (key2672, -2), (key2749, -2), (key2899, -2), (key2810, -2), (key2899, -2), (key2906, 2), (key2787, 2), (key2906, 2)]

def rawRow5135 : Integer.Sparse Key := [(key2643, -2), (key2643, -2), (key2633, -2), (key2655, 2), (key2655, 2), (key2617, 2), (key2739, 2), (key2739, 2), (key2707, 2), (key2749, -2), (key2749, -2), (key2672, -2), (key2899, -2), (key2899, -2), (key2810, -2), (key2906, 2), (key2906, 2), (key2787, 2)]

def rawRow5136 : Integer.Sparse Key := [(key2672, -2), (key2675, -2), (key2675, -2), (key2707, 2), (key2739, 2), (key2739, 2), (key2617, 2), (key2620, 2), (key2620, 2), (key2810, -2), (key2833, -2), (key2833, -2), (key2633, -2), (key2643, -2), (key2643, -2), (key2707, 2), (key2730, 2), (key2730, 2)]

def rawRow5137 : Integer.Sparse Key := [(key2675, -2), (key2672, -2), (key2675, -2), (key2739, 2), (key2707, 2), (key2739, 2), (key2620, 2), (key2617, 2), (key2620, 2), (key2833, -2), (key2810, -2), (key2833, -2), (key2643, -2), (key2633, -2), (key2643, -2), (key2730, 2), (key2707, 2), (key2730, 2)]

def rawRow5138 : Integer.Sparse Key := [(key2675, -2), (key2675, -2), (key2672, -2), (key2739, 2), (key2739, 2), (key2707, 2), (key2620, 2), (key2620, 2), (key2617, 2), (key2833, -2), (key2833, -2), (key2810, -2), (key2643, -2), (key2643, -2), (key2633, -2), (key2730, 2), (key2730, 2), (key2707, 2)]

def rawRow5139 : Integer.Sparse Key := [(key2707, -2), (key2730, -2), (key2730, -2), (key2672, 2), (key2749, 2), (key2749, 2), (key2810, 2), (key2833, 2), (key2833, 2), (key2617, -2), (key2962, -2), (key2962, -2), (key2707, -2), (key2978, -2), (key2978, -2), (key2633, 2), (key2985, 2), (key2985, 2)]

def rawRow5140 : Integer.Sparse Key := [(key2730, -2), (key2707, -2), (key2730, -2), (key2749, 2), (key2672, 2), (key2749, 2), (key2833, 2), (key2810, 2), (key2833, 2), (key2962, -2), (key2617, -2), (key2962, -2), (key2978, -2), (key2707, -2), (key2978, -2), (key2985, 2), (key2633, 2), (key2985, 2)]

def rawRow5141 : Integer.Sparse Key := [(key2730, -2), (key2730, -2), (key2707, -2), (key2749, 2), (key2749, 2), (key2672, 2), (key2833, 2), (key2833, 2), (key2810, 2), (key2962, -2), (key2962, -2), (key2617, -2), (key2978, -2), (key2978, -2), (key2707, -2), (key2985, 2), (key2985, 2), (key2633, 2)]

def rawRow5142 : Integer.Sparse Key := [(key2787, -2), (key2797, -2), (key2797, -2), (key2810, 2), (key2899, 2), (key2899, 2), (key2633, 2), (key2643, 2), (key2643, 2), (key2707, -2), (key2978, -2), (key2978, -2), (key2617, -2), (key2655, -2), (key2655, -2), (key2672, 2), (key2749, 2), (key2749, 2)]

def rawRow5143 : Integer.Sparse Key := [(key2797, -2), (key2787, -2), (key2797, -2), (key2899, 2), (key2810, 2), (key2899, 2), (key2643, 2), (key2633, 2), (key2643, 2), (key2978, -2), (key2707, -2), (key2978, -2), (key2655, -2), (key2617, -2), (key2655, -2), (key2749, 2), (key2672, 2), (key2749, 2)]

def rawRow5144 : Integer.Sparse Key := [(key2797, -2), (key2797, -2), (key2787, -2), (key2899, 2), (key2899, 2), (key2810, 2), (key2643, 2), (key2643, 2), (key2633, 2), (key2978, -2), (key2978, -2), (key2707, -2), (key2655, -2), (key2655, -2), (key2617, -2), (key2749, 2), (key2749, 2), (key2672, 2)]

def rawRow5145 : Integer.Sparse Key := [(key2810, -2), (key2833, -2), (key2833, -2), (key2787, 2), (key2906, 2), (key2906, 2), (key2707, 2), (key2730, 2), (key2730, 2), (key2633, -2), (key2985, -2), (key2985, -2), (key2672, -2), (key2749, -2), (key2749, -2), (key2617, 2), (key2962, 2), (key2962, 2)]

def rawRow5146 : Integer.Sparse Key := [(key2833, -2), (key2810, -2), (key2833, -2), (key2906, 2), (key2787, 2), (key2906, 2), (key2730, 2), (key2707, 2), (key2730, 2), (key2985, -2), (key2633, -2), (key2985, -2), (key2749, -2), (key2672, -2), (key2749, -2), (key2962, 2), (key2617, 2), (key2962, 2)]

def rawRow5147 : Integer.Sparse Key := [(key2833, -2), (key2833, -2), (key2810, -2), (key2906, 2), (key2906, 2), (key2787, 2), (key2730, 2), (key2730, 2), (key2707, 2), (key2985, -2), (key2985, -2), (key2633, -2), (key2749, -2), (key2749, -2), (key2672, -2), (key2962, 2), (key2962, 2), (key2617, 2)]

def rawRow5148 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2614, 2), (key2624, -1), (key2630, -1), (key2624, 2), (key2638, 2), (key2630, -1), (key2638, -1), (key2657, 2), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2669, -2), (key2698, 1), (key2704, 1), (key2698, -2), (key2724, -2), (key2704, 1), (key2724, 1), (key2752, -2), (key2752, 1), (key2757, 1), (key2778, -1), (key2792, -1), (key2784, 1), (key2792, 1), (key2801, 1), (key2827, 1), (key2807, -1), (key2827, -1), (key2851, -1), (key2858, -1), (key2851, 1), (key2868, 1), (key2918, 1), (key2919, 1), (key2918, -1), (key2922, -1)]

def rawRow5149 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2614, 2), (key2630, -1), (key2624, -1), (key2638, 2), (key2624, 2), (key2638, -1), (key2630, -1), (key2657, 2), (key2659, -1), (key2657, -1), (key2669, 1), (key2663, 1), (key2669, -2), (key2704, 1), (key2698, 1), (key2724, -2), (key2698, -2), (key2724, 1), (key2704, 1), (key2752, -2), (key2757, 1), (key2752, 1), (key2792, -1), (key2778, -1), (key2792, 1), (key2784, 1), (key2827, 1), (key2801, 1), (key2827, -1), (key2807, -1), (key2858, -1), (key2851, -1), (key2868, 1), (key2851, 1), (key2919, 1), (key2918, 1), (key2922, -1), (key2918, -1)]

def rawRow5150 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2608, 2), (key2638, -1), (key2638, -1), (key2630, 2), (key2630, 2), (key2624, -1), (key2624, -1), (key2659, 2), (key2657, -1), (key2657, -1), (key2669, 1), (key2669, 1), (key2663, -2), (key2724, 1), (key2724, 1), (key2704, -2), (key2704, -2), (key2698, 1), (key2698, 1), (key2757, -2), (key2752, 1), (key2752, 1), (key2784, -1), (key2784, -1), (key2778, 1), (key2778, 1), (key2807, 1), (key2807, 1), (key2801, -1), (key2801, -1), (key2868, -1), (key2868, -1), (key2858, 1), (key2858, 1), (key2922, 1), (key2922, 1), (key2919, -1), (key2919, -1)]

def rawRow5151 : Integer.Sparse Key := [(key2624, -1), (key2630, -1), (key2638, 2), (key2608, -1), (key2614, -1), (key2624, 2), (key2638, 2), (key2657, -1), (key2659, -1), (key2614, 2), (key2630, -1), (key2638, -1), (key2698, 1), (key2704, 1), (key2752, -2), (key2663, 1), (key2669, 1), (key2698, -2), (key2724, -2), (key2752, 1), (key2757, 1), (key2669, -2), (key2704, 1), (key2724, 1), (key2851, -1), (key2858, -1), (key2918, 1), (key2919, 1), (key2851, 1), (key2868, 1), (key2918, -1), (key2922, -1), (key2778, -1), (key2792, -1), (key2801, 1), (key2827, 1), (key2784, 1), (key2792, 1), (key2807, -1), (key2827, -1)]

def rawRow5152 : Integer.Sparse Key := [(key2630, -1), (key2624, -1), (key2638, 2), (key2614, -1), (key2608, -1), (key2638, 2), (key2624, 2), (key2659, -1), (key2657, -1), (key2614, 2), (key2638, -1), (key2630, -1), (key2704, 1), (key2698, 1), (key2752, -2), (key2669, 1), (key2663, 1), (key2724, -2), (key2698, -2), (key2757, 1), (key2752, 1), (key2669, -2), (key2724, 1), (key2704, 1), (key2858, -1), (key2851, -1), (key2919, 1), (key2918, 1), (key2868, 1), (key2851, 1), (key2922, -1), (key2918, -1), (key2792, -1), (key2778, -1), (key2827, 1), (key2801, 1), (key2792, 1), (key2784, 1), (key2827, -1), (key2807, -1)]

def rawRow5153 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2630, 2), (key2624, -1), (key2638, -1), (key2608, 2), (key2659, 2), (key2614, -1), (key2638, -1), (key2630, 2), (key2614, -1), (key2638, -1), (key2698, 1), (key2752, 1), (key2704, -2), (key2698, 1), (key2752, 1), (key2663, -2), (key2757, -2), (key2669, 1), (key2724, 1), (key2704, -2), (key2669, 1), (key2724, 1), (key2801, -1), (key2919, -1), (key2807, 1), (key2858, 1), (key2778, 1), (key2922, 1), (key2784, -1), (key2868, -1), (key2801, -1), (key2919, -1), (key2778, 1), (key2922, 1), (key2807, 1), (key2858, 1), (key2784, -1), (key2868, -1)]

def rawRow5154 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key2630, 2), (key2638, -1), (key2624, -1), (key2659, 2), (key2608, 2), (key2638, -1), (key2614, -1), (key2630, 2), (key2638, -1), (key2614, -1), (key2752, 1), (key2698, 1), (key2704, -2), (key2752, 1), (key2698, 1), (key2757, -2), (key2663, -2), (key2724, 1), (key2669, 1), (key2704, -2), (key2724, 1), (key2669, 1), (key2919, -1), (key2801, -1), (key2858, 1), (key2807, 1), (key2922, 1), (key2778, 1), (key2868, -1), (key2784, -1), (key2919, -1), (key2801, -1), (key2922, 1), (key2778, 1), (key2858, 1), (key2807, 1), (key2868, -1), (key2784, -1)]

def rawRow5155 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2624, 2), (key2657, -1), (key2659, -1), (key2614, 2), (key2638, 2), (key2608, -1), (key2624, -1), (key2638, 2), (key2614, -1), (key2630, -1), (key2704, 1), (key2752, 1), (key2698, -2), (key2724, 1), (key2757, 1), (key2669, -2), (key2752, -2), (key2663, 1), (key2698, 1), (key2724, -2), (key2669, 1), (key2704, 1), (key2807, -1), (key2918, -1), (key2801, 1), (key2851, 1), (key2784, 1), (key2918, 1), (key2778, -1), (key2851, -1), (key2827, -1), (key2922, -1), (key2792, 1), (key2919, 1), (key2827, 1), (key2868, 1), (key2792, -1), (key2858, -1)]

def rawRow5156 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2624, 2), (key2659, -1), (key2657, -1), (key2638, 2), (key2614, 2), (key2624, -1), (key2608, -1), (key2638, 2), (key2630, -1), (key2614, -1), (key2752, 1), (key2704, 1), (key2698, -2), (key2757, 1), (key2724, 1), (key2752, -2), (key2669, -2), (key2698, 1), (key2663, 1), (key2724, -2), (key2704, 1), (key2669, 1), (key2918, -1), (key2807, -1), (key2851, 1), (key2801, 1), (key2918, 1), (key2784, 1), (key2851, -1), (key2778, -1), (key2922, -1), (key2827, -1), (key2919, 1), (key2792, 1), (key2868, 1), (key2827, 1), (key2858, -1), (key2792, -1)]

def rawRow5157 : Integer.Sparse Key := [(key2657, -1), (key2657, -1), (key2659, 2), (key2614, -1), (key2614, -1), (key2630, 2), (key2630, 2), (key2638, -1), (key2638, -1), (key2608, 2), (key2624, -1), (key2624, -1), (key2724, 1), (key2724, 1), (key2757, -2), (key2669, 1), (key2669, 1), (key2704, -2), (key2704, -2), (key2752, 1), (key2752, 1), (key2663, -2), (key2698, 1), (key2698, 1), (key2868, -1), (key2868, -1), (key2922, 1), (key2922, 1), (key2858, 1), (key2858, 1), (key2919, -1), (key2919, -1), (key2784, -1), (key2784, -1), (key2807, 1), (key2807, 1), (key2778, 1), (key2778, 1), (key2801, -1), (key2801, -1)]

def rawRow5158 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2657, 2), (key2630, -1), (key2638, -1), (key2614, 2), (key2638, 2), (key2614, -1), (key2630, -1), (key2624, 2), (key2608, -1), (key2624, -1), (key2724, 1), (key2757, 1), (key2724, -2), (key2704, 1), (key2752, 1), (key2669, -2), (key2752, -2), (key2669, 1), (key2704, 1), (key2698, -2), (key2663, 1), (key2698, 1), (key2827, -1), (key2922, -1), (key2827, 1), (key2868, 1), (key2792, 1), (key2919, 1), (key2792, -1), (key2858, -1), (key2807, -1), (key2918, -1), (key2784, 1), (key2918, 1), (key2801, 1), (key2851, 1), (key2778, -1), (key2851, -1)]

def rawRow5159 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2657, 2), (key2638, -1), (key2630, -1), (key2638, 2), (key2614, 2), (key2630, -1), (key2614, -1), (key2624, 2), (key2624, -1), (key2608, -1), (key2757, 1), (key2724, 1), (key2724, -2), (key2752, 1), (key2704, 1), (key2752, -2), (key2669, -2), (key2704, 1), (key2669, 1), (key2698, -2), (key2698, 1), (key2663, 1), (key2922, -1), (key2827, -1), (key2868, 1), (key2827, 1), (key2919, 1), (key2792, 1), (key2858, -1), (key2792, -1), (key2918, -1), (key2807, -1), (key2918, 1), (key2784, 1), (key2851, 1), (key2801, 1), (key2851, -1), (key2778, -1)]

def rawRow5160 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2669, 2), (key2698, -1), (key2704, -1), (key2698, 2), (key2752, 2), (key2704, -1), (key2752, -1), (key2724, 2), (key2724, -1), (key2757, -1), (key2608, 1), (key2614, 1), (key2614, -2), (key2801, 1), (key2807, 1), (key2801, -2), (key2827, -2), (key2807, 1), (key2827, 1), (key3011, -2), (key3011, 1), (key3016, 1), (key2624, -1), (key2638, -1), (key2630, 1), (key2638, 1), (key2698, 1), (key2724, 1), (key2704, -1), (key2724, -1), (key2851, -1), (key2858, -1), (key2851, 1), (key2868, 1), (key3021, 1), (key3022, 1), (key3021, -1), (key3025, -1)]

def rawRow5161 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2669, 2), (key2704, -1), (key2698, -1), (key2752, 2), (key2698, 2), (key2752, -1), (key2704, -1), (key2724, 2), (key2757, -1), (key2724, -1), (key2614, 1), (key2608, 1), (key2614, -2), (key2807, 1), (key2801, 1), (key2827, -2), (key2801, -2), (key2827, 1), (key2807, 1), (key3011, -2), (key3016, 1), (key3011, 1), (key2638, -1), (key2624, -1), (key2638, 1), (key2630, 1), (key2724, 1), (key2698, 1), (key2724, -1), (key2704, -1), (key2858, -1), (key2851, -1), (key2868, 1), (key2851, 1), (key3022, 1), (key3021, 1), (key3025, -1), (key3021, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Source8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def row1028 : Integer.Sparse (Fin 3237) := [(476, 1), (789, 2), (818, 2), (1145, 1), (2817, -1)]

end MUB6.Certificate.MixedData

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

def nodeValue1154 : Sparse Master := [(Sum.inr 1154, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


