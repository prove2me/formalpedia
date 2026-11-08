-- Prove2me | Definitions.Def_OAIQ098G415
-- name    : OAIQ098G415
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:45:47.047263+00:00
-- url     : https://prove2.me/theorems/45978b21-50fd-466c-82de-fcccce93b86e
-- title:
--   Definitions bundle OAIQ098G415 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G413` and `OAIQ098G414` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1468`, `OAIQ098G416` and `OAIQ098G540`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G413
import Definitions.Def_OAIQ098G414

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def mpower0_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_1_r0,mpower0_1_r1,mpower0_1_r2,mpower0_1_r3,mpower0_1_r4,mpower0_1_r5]
end SharpPlanar.CachedData

end OAI
end


