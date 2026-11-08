-- Prove2me | Definitions.Def_OAIQ098G364
-- name    : OAIQ098G364
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:16:35.315726+00:00
-- url     : https://prove2.me/theorems/7220f61e-0b29-42ea-a12e-a0d6a7fe4eb7
-- title:
--   Definitions bundle OAIQ098G364 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.IntegerBasis.DensityCheck`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_CanonicalRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G047`, `OAIQ098G198`, `OAIQ098G202`, `OAIQ098G231`, `OAIQ098G235` and `OAIQ098G250` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G367`; the statements `OAI.SharpPlanar.IntegerBasis.density_check_g` and `OAI.SharpPlanar.IntegerBasis.density_finite_check_g`; the proofs of `OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_g` and `OAI.SharpPlanar.IntegerBasis.density_check_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G198
import Definitions.Def_OAIQ098G202
import Definitions.Def_OAIQ098G231
import Definitions.Def_OAIQ098G235
import Definitions.Def_OAIQ098G250

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

def DensityCheck (n : ℕ) (j : Fin 6) : Prop :=
  (uAmplitudeBox (RBox.rat j.val 6) (aLookup n j) (bLookup n j)).SqNormCheck (densityNum j) (densityDen j) ∧
  (uAmplitudeBox (RBox.rat (j.val+1) 6) (aLookup n j) (bLookup n j)).SqNormCheck (densityNum j) (densityDen j) ∧
  (vAmplitudeBox (aLookup n j)).SqNormCheck (densityNum j) (densityDen j)

end SharpPlanar.IntegerBasis

end OAI
end


