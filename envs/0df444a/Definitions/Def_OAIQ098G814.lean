-- Prove2me | Definitions.Def_OAIQ098G814
-- name    : OAIQ098G814
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:25:54.523941+00:00
-- url     : https://prove2.me/theorems/a5d2025f-dc05-44b1-bf6d-0b9646ee071b
-- title:
--   Definitions bundle OAIQ098G814 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm12_1_0_9.chunk`, `OAI.SharpPlanar.CachedData.hm13_1_0_9.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock12_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock12_1.lean), [`PlanarPacking_Certificate_LowBlock13_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock13_1.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G410` and `OAIQ098G485` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein12.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein12.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein13.N1_left.bound_g` and `OAI.SharpPlanar.Bernstein13.N1_right.bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G410
import Definitions.Def_OAIQ098G485

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_1
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
namespace hm12_1_0_9
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk12_0_9 j i k))
end hm12_1_0_9
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_1
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
namespace hm13_1_0_9
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk13_0_9 j i k))
end hm13_1_0_9
end SharpPlanar.CachedData

end OAI
end


