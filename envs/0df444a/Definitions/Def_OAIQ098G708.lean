-- Prove2me | Definitions.Def_OAIQ098G708
-- name    : OAIQ098G708
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:20:46.775253+00:00
-- url     : https://prove2.me/theorems/e7d8a0f1-b7c9-4495-b1d6-b862a0c3027d
-- title:
--   Definitions bundle OAIQ098G708 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hk7_0_3`, `OAI.SharpPlanar.CachedData.hk7_0_4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighHeaders7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders7.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G287`, `OAIQ098G387` and `OAIQ098G432` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1318` and `OAIQ098G1342`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G287
import Definitions.Def_OAIQ098G387
import Definitions.Def_OAIQ098G432

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders7
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
noncomputable def hk7_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk7_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power7 j i k).conj.mul (mpower0_4 j i k)
end SharpPlanar.CachedData

end OAI
end


