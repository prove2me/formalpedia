-- Prove2me | Definitions.Def_OAIQ098G075
-- name    : OAIQ098G075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:01:25.6095+00:00
-- url     : https://prove2.me/theorems/50155f3d-efb7-4447-9227-2f6c80e5a026
-- title:
--   Definitions bundle OAIQ098G075 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.IntegerBasis.phaseBase`, `OAI.SharpPlanar.IntegerIntervals.CBox.exp`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_BasisIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BasisIntervals.lean), [`PlanarPacking_Intervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Intervals.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G059`, `OAIQ098G073` and `OAIQ098G074` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G077` and `OAIQ098G093`; the statements `OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g` and `OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_g`; the proofs of `OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g` and `OAI.SharpPlanar.IntegerIntervals.CBox.contains_exp_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G059
import Definitions.Def_OAIQ098G073
import Definitions.Def_OAIQ098G074

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

def CBox.exp (a : CBox) (k : ℕ := 11) : CBox :=
  (((a.scale 1 (2^k)).horner 0 32).widen 1).squareIter k

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def phaseBase : CBox := (piI.scale 1 6).exp 1

end SharpPlanar.IntegerBasis

end OAI
end


