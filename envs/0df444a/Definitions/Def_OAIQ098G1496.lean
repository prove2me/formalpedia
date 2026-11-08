-- Prove2me | Definitions.Def_OAIQ098G1496
-- name    : OAIQ098G1496
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:27:21.380464+00:00
-- url     : https://prove2.me/theorems/644ce3ba-5ff5-438b-ac4f-06a7fbf899e3
-- title:
--   Definitions bundle OAIQ098G1496 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.tm0_100_0.s2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableMoments100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1411`, `OAIQ098G1415`, `OAIQ098G1418`, `OAIQ098G1422` and `OAIQ098G1456` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1497`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1411
import Definitions.Def_OAIQ098G1415
import Definitions.Def_OAIQ098G1418
import Definitions.Def_OAIQ098G1422
import Definitions.Def_OAIQ098G1456

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments100
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
namespace tm0_100_0
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
end tm0_100_0

end SharpPlanar.CachedData

end OAI
end


