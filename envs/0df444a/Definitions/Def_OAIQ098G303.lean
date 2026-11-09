-- Prove2me | Definitions.Def_OAIQ098G303
-- name    : OAIQ098G303
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:45:16.618017+00:00
-- url     : https://prove2.me/theorems/7215bff1-3889-4c7a-b5d4-1b177ba0c857
-- title:
--   Definitions bundle OAIQ098G303 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power10Expr`, `OAI.SharpPlanar.CachedData.power9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G299` and `OAIQ098G302` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G304`, `OAIQ098G723`, `OAIQ098G724`, `OAIQ098G725`, `OAIQ098G726`, `OAIQ098G727`, `OAIQ098G728`, `OAIQ098G729`, `OAIQ098G730` and `OAIQ098G731`; the proof of `OAI.SharpPlanar.CachedData.power12_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G299
import Definitions.Def_OAIQ098G302

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
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
noncomputable def power9 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power9_r0,power9_r1,power9_r2,power9_r3,power9_r4,power9_r5]
noncomputable def power10Expr (j : Fin 6) (i k : Fin 16) : CBox := (power9 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


