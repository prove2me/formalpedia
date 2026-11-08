-- Prove2me | Definitions.Def_OAIQ098G1494
-- name    : OAIQ098G1494
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:29:15.625103+00:00
-- url     : https://prove2.me/theorems/61cf50ab-5c2f-4d96-a59b-b0dede39a9c0
-- title:
--   Definitions bundle OAIQ098G1494 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.tm0_100_0.s0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableMoments100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G937`, `OAIQ098G1060`, `OAIQ098G1269`, `OAIQ098G1295`, `OAIQ098G1319`, `OAIQ098G1363`, `OAIQ098G1446` and `OAIQ098G1452` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1497`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G937
import Definitions.Def_OAIQ098G1060
import Definitions.Def_OAIQ098G1269
import Definitions.Def_OAIQ098G1295
import Definitions.Def_OAIQ098G1319
import Definitions.Def_OAIQ098G1363
import Definitions.Def_OAIQ098G1446
import Definitions.Def_OAIQ098G1452

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
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
end tm0_100_0

end SharpPlanar.CachedData

end OAI
end


