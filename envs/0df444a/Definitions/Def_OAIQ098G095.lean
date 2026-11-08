-- Prove2me | Definitions.Def_OAIQ098G095
-- name    : OAIQ098G095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:10:21.426475+00:00
-- url     : https://prove2.me/theorems/2512a090-ce1b-415e-b7d4-8b0aa0d3c6fa
-- title:
--   Definitions bundle OAIQ098G095 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.IntegerRoots.mid11`, `OAI.SharpPlanar.IntegerRoots.mid13`, `OAI.SharpPlanar.IntegerRoots.mid513`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Roots`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Roots.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G059` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.IntegerCompact.weightRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_g` and `OAI.SharpPlanar.IntegerGrid.row5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G059

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar
namespace IntegerRoots
open IntegerIntervals
def mid11 : CBox := root10
def mid13 : CBox := root12
def mid513 : CBox := root512
end IntegerRoots
end SharpPlanar

end OAI
end


