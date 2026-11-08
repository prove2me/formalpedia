-- Prove2me | Definitions.Def_OAIQ098G1356
-- name    : OAIQ098G1356
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:47:23.628127+00:00
-- url     : https://prove2.me/theorems/1f70d16a-9735-4813-accc-224cb7380f4b
-- title:
--   Definitions bundle OAIQ098G1356 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm7_1_1_6.chunk`, `OAI.SharpPlanar.CachedData.hm7_1_1_7.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock7_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock7_10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G410` and `OAIQ098G720` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein7.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t5_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t4_contains_g` and `OAI.SharpPlanar.Bernstein7.N0_right.t5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G410
import Definitions.Def_OAIQ098G720

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_10
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
namespace hm7_1_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_6 j i k))
end hm7_1_1_6
namespace hm7_1_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_1_7 j i k))
end hm7_1_1_7
end SharpPlanar.CachedData

end OAI
end


