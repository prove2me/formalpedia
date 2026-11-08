-- Prove2me | Definitions.Def_OAIQ098G946
-- name    : OAIQ098G946
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:43:20.853229+00:00
-- url     : https://prove2.me/theorems/b5b41a39-cf2c-4008-be50-21f9ccc04462
-- title:
--   Definitions bundle OAIQ098G946 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm1_0_1_10.chunk`, `OAI.SharpPlanar.CachedData.hm1_0_1_11.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighMoments1_5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments1_5.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G018`, `OAIQ098G395` and `OAIQ098G554` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein1.N1_left.t8_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t9_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t8_contains_g` and `OAI.SharpPlanar.Bernstein1.N1_right.t9_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G554

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_5
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
namespace hm1_0_1_10
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk1_1_10 j i k))
end hm1_0_1_10
namespace hm1_0_1_11
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk1_1_11 j i k))
end hm1_0_1_11
end SharpPlanar.CachedData

end OAI
end


