-- Prove2me | Definitions.Def_OAIQ098G779
-- name    : OAIQ098G779
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:36:16.64643+00:00
-- url     : https://prove2.me/theorems/ba604005-05c8-4888-ba5a-0ce6565a73fd
-- title:
--   Definitions bundle OAIQ098G779 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm0_1_0_22.chunk`, `OAI.SharpPlanar.CachedData.hm0_1_0_23.chunk`, `OAI.SharpPlanar.CachedData.hm0_1_0_24.chunk`, `OAI.SharpPlanar.CachedData.hm0_1_0_25.chunk`, `OAI.SharpPlanar.CachedData.hm0_1_0_26.chunk`, `OAI.SharpPlanar.CachedData.hm0_1_0_27.chunk`, `OAI.SharpPlanar.CachedData.hm0_1_0_28.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_HighMoments0_2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_2.lean), [`PlanarPacking_Certificate_HighMoments0_3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/HighMoments0_3.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G018`, `OAIQ098G410` and `OAIQ098G430` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein0.N1_right.t22_contains_g`, `OAI.SharpPlanar.Bernstein0.N1_right.t23_contains_g`, `OAI.SharpPlanar.Bernstein0.N1_right.t24_contains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_25.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_26.realContains_g`, `OAI.SharpPlanar.CachedData.hm0_1_0_27.realContains_g` and `OAI.SharpPlanar.CachedData.hm0_1_0_28.realContains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G410
import Definitions.Def_OAIQ098G430

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_2
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
namespace hm0_1_0_22
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_22 j i k))
end hm0_1_0_22
namespace hm0_1_0_23
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_23 j i k))
end hm0_1_0_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_3
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
namespace hm0_1_0_24
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_24 j i k))
end hm0_1_0_24
namespace hm0_1_0_25
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_25 j i k))
end hm0_1_0_25
namespace hm0_1_0_26
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_26 j i k))
end hm0_1_0_26
namespace hm0_1_0_27
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_27 j i k))
end hm0_1_0_27
namespace hm0_1_0_28
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_28 j i k))
end hm0_1_0_28
end SharpPlanar.CachedData

end OAI
end


