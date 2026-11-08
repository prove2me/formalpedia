-- Prove2me | Definitions.Def_OAIQ098G419
-- name    : OAIQ098G419
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:46:57.440112+00:00
-- url     : https://prove2.me/theorems/f44245e4-54b8-43d6-918b-0a0ddea7d313
-- title:
--   Definitions bundle OAIQ098G419 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.mpower0_10`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G417` and `OAIQ098G418` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1460`, `OAIQ098G420`, `OAIQ098G478`, `OAIQ098G496`, `OAIQ098G513`, `OAIQ098G522`, `OAIQ098G541`, `OAIQ098G577`, `OAIQ098G592`, `OAIQ098G600`, `OAIQ098G624`, `OAIQ098G632`, `OAIQ098G640`, `OAIQ098G648`, `OAIQ098G662`, `OAIQ098G680`, `OAIQ098G703` and `OAIQ098G723`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G417
import Definitions.Def_OAIQ098G418

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers10
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
noncomputable def mpower0_10 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_10_r0,mpower0_10_r1,mpower0_10_r2,mpower0_10_r3,mpower0_10_r4,mpower0_10_r5]
end SharpPlanar.CachedData

end OAI
end


