-- Prove2me | Definitions.Def_OAIQ098G1107
-- name    : OAIQ098G1107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:13:01.562469+00:00
-- url     : https://prove2.me/theorems/7a79c9cb-a761-4b6c-9ebf-ba7946ab82ed
-- title:
--   Definitions bundle OAIQ098G1107 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.hm27_1_1_9.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock27_11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock27_11.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G018`, `OAIQ098G410` and `OAIQ098G616` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein27.N0_left.t7_contains_g` and `OAI.SharpPlanar.Bernstein27.N0_right.t7_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G410
import Definitions.Def_OAIQ098G616

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_11
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
namespace hm27_1_1_9
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk27_1_9 j i k))
end hm27_1_1_9
end SharpPlanar.CachedData

end OAI
end


