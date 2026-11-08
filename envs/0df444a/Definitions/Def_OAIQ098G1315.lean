-- Prove2me | Definitions.Def_OAIQ098G1315
-- name    : OAIQ098G1315
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:41:30.835219+00:00
-- url     : https://prove2.me/theorems/e54831f1-f32d-49ae-867b-878c0b2bfb65
-- title:
--   Definitions bundle OAIQ098G1315 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm7_0_0_12.chunk`, `OAI.SharpPlanar.CachedData.hm7_0_0_13.chunk`, `OAI.SharpPlanar.CachedData.hm7_0_0_14.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock7_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock7_1.lean), [`PlanarPacking_Certificate_LowBlock7_2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock7_2.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G395` and `OAIQ098G705` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein7.N0_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein7.N0_right.t12_contains_g` and `OAI.SharpPlanar.CachedData.hm7_0_0_12.realContains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G705

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_1
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
namespace hm7_0_0_12
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_0_12 j i k))
end hm7_0_0_12
namespace hm7_0_0_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_0_13 j i k))
end hm7_0_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_2
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
namespace hm7_0_0_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_0_14 j i k))
end hm7_0_0_14
end SharpPlanar.CachedData

end OAI
end


