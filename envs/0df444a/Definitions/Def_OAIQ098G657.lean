-- Prove2me | Definitions.Def_OAIQ098G657
-- name    : OAIQ098G657
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:53:03.108057+00:00
-- url     : https://prove2.me/theorems/bb565fa2-7326-44f9-90f3-491ffd66b60b
-- title:
--   Definitions bundle OAIQ098G657 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel39_0`, `OAI.SharpPlanar.CachedData.kernel40_0`, `OAI.SharpPlanar.CachedData.kernel40_0_r0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G608` and `OAIQ098G656` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1518`, `OAIQ098G1565`, `OAIQ098G658`, `OAIQ098G659`, `OAIQ098G660` and `OAIQ098G661`; the statements `OAI.SharpPlanar.CachedData.kernel39_0_contains_g` and `OAI.SharpPlanar.CachedData.kernel40_0_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.kernel39_0_contains_g` and `OAI.SharpPlanar.CachedData.kernel40_0_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G608
import Definitions.Def_OAIQ098G656

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues40
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
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def kernel39_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel39_0_r0,kernel39_0_r1,kernel39_0_r2,kernel39_0_r3,kernel39_0_r4,kernel39_0_r5]
noncomputable def kernel40_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel40_0_r0_0,kernel40_0_r0_1,kernel40_0_r0_2,kernel40_0_r0_3,kernel40_0_r0_4,kernel40_0_r0_5,kernel40_0_r0_6,kernel40_0_r0_7,kernel40_0_r0_8,kernel40_0_r0_9,kernel40_0_r0_10,kernel40_0_r0_11,kernel40_0_r0_12,kernel40_0_r0_13,kernel40_0_r0_14,kernel40_0_r0_15]
noncomputable def kernel40_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel40_0_r0,kernel40_0_r1,kernel40_0_r2,kernel40_0_r3,kernel40_0_r4,kernel40_0_r5]
end SharpPlanar.CachedData

end OAI
end


