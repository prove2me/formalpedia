-- Prove2me | Definitions.Def_OAIQ098G665
-- name    : OAIQ098G665
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:53:27.196491+00:00
-- url     : https://prove2.me/theorems/9ea9467b-e735-4f7a-96cd-bd55593c5127
-- title:
--   Definitions bundle OAIQ098G665 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hk3_0_2`, `OAI.SharpPlanar.CachedData.hk4_0_17`, `OAI.SharpPlanar.CachedData.hk4_0_18`, `OAI.SharpPlanar.CachedData.hk4_0_19`, `OAI.SharpPlanar.CachedData.hk4_0_2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighHeaders3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders3.lean), [`PlanarPacking_Certificate_HighHeaders4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighHeaders4.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G053`, `OAIQ098G387` and `OAIQ098G423` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1218` and `OAIQ098G1238`; the statements `OAI.SharpPlanar.CachedData.hk4_0_18_contains_g` and `OAI.SharpPlanar.CachedData.hk4_0_2_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.hk4_0_18_contains_g` and `OAI.SharpPlanar.CachedData.hk4_0_2_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G053
import Definitions.Def_OAIQ098G387
import Definitions.Def_OAIQ098G423

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders3
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
noncomputable def hk3_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_2 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders4
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
noncomputable def hk4_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk4_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_17 j i k)
noncomputable def hk4_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_18 j i k)
noncomputable def hk4_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_19 j i k)
end SharpPlanar.CachedData

end OAI
end


