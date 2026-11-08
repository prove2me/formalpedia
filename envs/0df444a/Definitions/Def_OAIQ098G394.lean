-- Prove2me | Definitions.Def_OAIQ098G394
-- name    : OAIQ098G394
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:38:15.849371+00:00
-- url     : https://prove2.me/theorems/6f6dd12e-1a47-4ce0-91d2-5a7b7d0b666f
-- title:
--   Definitions bundle OAIQ098G394 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.density0_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableDensity0Panel5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableDensity0Panel5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G391` and `OAIQ098G393` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G395`; the statement `OAI.SharpPlanar.CachedData.density0_r5_eq_g`; the proof of `OAI.SharpPlanar.CachedData.density0_r5_eq_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G391
import Definitions.Def_OAIQ098G393

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel5
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
noncomputable def density0_r5 : Fin 16 → Fin 16 → CBox := ![density0_r5_0,density0_r5_1,density0_r5_2,density0_r5_3,density0_r5_4,density0_r5_5,density0_r5_6,density0_r5_7,density0_r5_8,density0_r5_9,density0_r5_10,density0_r5_11,density0_r5_12,density0_r5_13,density0_r5_14,density0_r5_15]
end SharpPlanar.CachedData

end OAI
end


