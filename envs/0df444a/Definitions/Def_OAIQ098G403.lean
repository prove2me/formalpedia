-- Prove2me | Definitions.Def_OAIQ098G403
-- name    : OAIQ098G403
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:39:02.836021+00:00
-- url     : https://prove2.me/theorems/3300cd25-1947-4bb3-8017-3b0e27549be0
-- title:
--   Definitions bundle OAIQ098G403 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.density1_r2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableDensity1Panel2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableDensity1Panel2.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G400` and `OAIQ098G402` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G410`; the statement `OAI.SharpPlanar.CachedData.density1_r2_eq_g`; the proof of `OAI.SharpPlanar.CachedData.density1_r2_eq_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G400
import Definitions.Def_OAIQ098G402

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel2
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
noncomputable def density1_r2 : Fin 16 → Fin 16 → CBox := ![density1_r2_0,density1_r2_1,density1_r2_2,density1_r2_3,density1_r2_4,density1_r2_5,density1_r2_6,density1_r2_7,density1_r2_8,density1_r2_9,density1_r2_10,density1_r2_11,density1_r2_12,density1_r2_13,density1_r2_14,density1_r2_15]
end SharpPlanar.CachedData

end OAI
end


