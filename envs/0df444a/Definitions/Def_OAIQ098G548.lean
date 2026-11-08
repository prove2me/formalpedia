-- Prove2me | Definitions.Def_OAIQ098G548
-- name    : OAIQ098G548
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:50:41.773274+00:00
-- url     : https://prove2.me/theorems/bf4bac4b-0b7c-4b9e-997e-e8bba073a1dd
-- title:
--   Definitions bundle OAIQ098G548 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hk1_0_29`, `OAI.SharpPlanar.CachedData.hk1_0_30`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighHeaders1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders1.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G054`, `OAIQ098G387` and `OAIQ098G474` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G941` and `OAIQ098G980`; the statements `OAI.SharpPlanar.CachedData.hk1_0_29_contains_g` and `OAI.SharpPlanar.CachedData.hk1_0_30_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.hk1_0_29_contains_g` and `OAI.SharpPlanar.CachedData.hk1_0_30_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G054
import Definitions.Def_OAIQ098G387
import Definitions.Def_OAIQ098G474

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders1
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
noncomputable def hk1_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_29 j i k)
noncomputable def hk1_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_30 j i k)
end SharpPlanar.CachedData

end OAI
end


