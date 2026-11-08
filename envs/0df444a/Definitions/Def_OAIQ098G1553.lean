-- Prove2me | Definitions.Def_OAIQ098G1553
-- name    : OAIQ098G1553
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:28:30.928886+00:00
-- url     : https://prove2.me/theorems/22ca3c4b-9845-4854-bc63-70d90fc62f59
-- title:
--   Definitions bundle OAIQ098G1553 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.tm1_15_0.s2`, `OAI.SharpPlanar.CachedData.tm1_15_0.sums`, `OAI.SharpPlanar.CachedData.tm1_15_1.s0`, `OAI.SharpPlanar.CachedData.tm1_15_1.sums`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableMoments15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableMoments15.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1533` and `OAIQ098G1552` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Residual15.bound0_0_g` and `OAI.SharpPlanar.Residual15.bound0_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1533
import Definitions.Def_OAIQ098G1552

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments15
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

namespace tm1_15_0
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end tm1_15_0

namespace tm1_15_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end tm1_15_1

end SharpPlanar.CachedData

end OAI
end


