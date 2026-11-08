-- Prove2me | Definitions.Def_OAIQ098G445
-- name    : OAIQ098G445
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:43:25.243908+00:00
-- url     : https://prove2.me/theorems/6c34d4f8-1f07-4469-9283-2aaa934a8f52
-- title:
--   Definitions bundle OAIQ098G445 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hk0_1_13`, `OAI.SharpPlanar.CachedData.hk0_1_14`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighHeaders0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders0.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G435` and `OAIQ098G442` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G747`; the statement `OAI.SharpPlanar.CachedData.hk0_1_14_contains_g`; the proof of `OAI.SharpPlanar.CachedData.hk0_1_14_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G435
import Definitions.Def_OAIQ098G442

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders0
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
noncomputable def hk0_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_13 j i k)
noncomputable def hk0_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_14 j i k)
end SharpPlanar.CachedData

end OAI
end


