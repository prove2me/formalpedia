-- Prove2me | Definitions.Def_OAIQ098G747
-- name    : OAIQ098G747
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:31:37.825467+00:00
-- url     : https://prove2.me/theorems/0815fa38-14d1-4ece-b2e0-b34d9f37b9f2
-- title:
--   Definitions bundle OAIQ098G747 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm0_0_1_13.chunk`, `OAI.SharpPlanar.CachedData.hm0_0_1_14.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighMoments0_5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G018`, `OAIQ098G395` and `OAIQ098G445` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein0.N1_right.t14_contains_g` and `OAI.SharpPlanar.CachedData.hm0_0_1_13.realContains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G445

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_5
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
namespace hm0_0_1_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_1_13 j i k))
end hm0_0_1_13
namespace hm0_0_1_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_1_14 j i k))
end hm0_0_1_14
end SharpPlanar.CachedData

end OAI
end


