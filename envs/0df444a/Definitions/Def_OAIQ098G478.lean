-- Prove2me | Definitions.Def_OAIQ098G478
-- name    : OAIQ098G478
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:15:13.423177+00:00
-- url     : https://prove2.me/theorems/15bf416a-4572-4f56-84e9-5a3f6b29e4cc
-- title:
--   Definitions bundle OAIQ098G478 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hk12_0_10`, `OAI.SharpPlanar.CachedData.hk13_0_10`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighHeaders12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders12.lean), [`PlanarPacking_Certificate_HighHeaders13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders13.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G237`, `OAIQ098G387` and `OAIQ098G419` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G786` and `OAIQ098G806`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G237
import Definitions.Def_OAIQ098G387
import Definitions.Def_OAIQ098G419

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders12
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
noncomputable def hk12_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_10 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders13
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
noncomputable def hk13_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power13 j i k).conj.mul (mpower0_10 j i k)
end SharpPlanar.CachedData

end OAI
end


