-- Prove2me | Definitions.Def_OAIQ098G405
-- name    : OAIQ098G405
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:39:18.464198+00:00
-- url     : https://prove2.me/theorems/8a7f5eb0-35af-4a2b-889f-d5196b344c9c
-- title:
--   Definitions bundle OAIQ098G405 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.density1_r3`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableDensity1Panel3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableDensity1Panel3.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G402` and `OAIQ098G404` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G410`; the statement `OAI.SharpPlanar.CachedData.density1_r3_eq_g`; the proof of `OAI.SharpPlanar.CachedData.density1_r3_eq_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G402
import Definitions.Def_OAIQ098G404

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel3
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
noncomputable def density1_r3 : Fin 16 → Fin 16 → CBox := ![density1_r3_0,density1_r3_1,density1_r3_2,density1_r3_3,density1_r3_4,density1_r3_5,density1_r3_6,density1_r3_7,density1_r3_8,density1_r3_9,density1_r3_10,density1_r3_11,density1_r3_12,density1_r3_13,density1_r3_14,density1_r3_15]
end SharpPlanar.CachedData

end OAI
end


