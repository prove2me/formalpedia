-- Prove2me | Definitions.Def_OAIQ098G1626
-- name    : OAIQ098G1626
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:35:32.144029+00:00
-- url     : https://prove2.me/theorems/d0afc7a2-cde2-4a2c-a3b3-1ab441bf243e
-- title:
--   Definitions bundle OAIQ098G1626 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans68`, `OAI.SharpPlanar.CachedData.trans68_r4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1616` and `OAIQ098G1625` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1627`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1616
import Definitions.Def_OAIQ098G1625

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers70
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
noncomputable def trans68_r4 : Fin 16 → Fin 16 → CBox := ![trans68_r4_0,trans68_r4_1,trans68_r4_2,trans68_r4_3,trans68_r4_4,trans68_r4_5,trans68_r4_6,trans68_r4_7,trans68_r4_8,trans68_r4_9,trans68_r4_10,trans68_r4_11,trans68_r4_12,trans68_r4_13,trans68_r4_14,trans68_r4_15]
noncomputable def trans68 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans68_r0,trans68_r1,trans68_r2,trans68_r3,trans68_r4,trans68_r5]
end SharpPlanar.CachedData

end OAI
end


