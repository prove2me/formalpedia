-- Prove2me | Definitions.Def_OAIQ098G024
-- name    : OAIQ098G024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:31:05.771964+00:00
-- url     : https://prove2.me/theorems/e51c1a93-ba41-4ce4-ba9c-fee97ebfbb3d
-- title:
--   Definitions bundle OAIQ098G024 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column1_0`, `OAI.SharpPlanar.CachedData.column1_0_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G021` and `OAIQ098G023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G025`, `OAIQ098G030`, `OAIQ098G033`, `OAIQ098G034`, `OAIQ098G118`, `OAIQ098G121`, `OAIQ098G123` and `OAIQ098G385`; the statement `OAI.SharpPlanar.CachedData.column1_0_contains_g`; the proof of `OAI.SharpPlanar.CachedData.column1_0_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G021
import Definitions.Def_OAIQ098G023

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
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
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def column1_0_r5 : Fin 16 → Fin 16 → CBox := ![column1_0_r5_0,column1_0_r5_1,column1_0_r5_2,column1_0_r5_3,column1_0_r5_4,column1_0_r5_5,column1_0_r5_6,column1_0_r5_7,column1_0_r5_8,column1_0_r5_9,column1_0_r5_10,column1_0_r5_11,column1_0_r5_12,column1_0_r5_13,column1_0_r5_14,column1_0_r5_15]
noncomputable def column1_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column1_0_r0,column1_0_r1,column1_0_r2,column1_0_r3,column1_0_r4,column1_0_r5]
end SharpPlanar.CachedData

end OAI
end


