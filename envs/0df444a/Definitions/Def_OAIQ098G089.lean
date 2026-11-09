-- Prove2me | Definitions.Def_OAIQ098G089
-- name    : OAIQ098G089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:59:08.143021+00:00
-- url     : https://prove2.me/theorems/adfe871b-7927-4d2d-8867-c977dc1ecf40
-- title:
--   Definitions bundle OAIQ098G089 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.IntegerIntervals.quarterArgBox`, `OAI.SharpPlanar.IntegerIntervals.zBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G076` and `OAIQ098G087` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G090` and `OAIQ098G093`; the statements `OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g` and `OAI.SharpPlanar.IntegerIntervals.zBox_contains_g`; the proofs of `OAI.SharpPlanar.IntegerIntervals.quarterArgBox_contains_g` and `OAI.SharpPlanar.IntegerIntervals.zBox_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G087

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar.IntegerIntervals

def zBox (a : RBox) : CBox := ((denBox a).inv.scale (-4) 3).add (CBox.rat 0 1 (-2) 5)
def quarterArgBox (a : RBox) : CBox := (piI.mul (zBox a)).scale 1 4

end SharpPlanar.IntegerIntervals

end OAI
end


