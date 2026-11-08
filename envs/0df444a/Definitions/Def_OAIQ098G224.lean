-- Prove2me | Definitions.Def_OAIQ098G224
-- name    : OAIQ098G224
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:57:07.447205+00:00
-- url     : https://prove2.me/theorems/2834f287-5099-4dda-b0f1-b836c74e9750
-- title:
--   Definitions bundle OAIQ098G224 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm88_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm88_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm88_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm88_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm88_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm88_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.column88_0`, `OAI.SharpPlanar.CachedData.column88_0_r3`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns90`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns90.lean), [`PlanarPacking_Certificate_UMoments88`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments88.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G221` and `OAIQ098G223` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G385`; the proofs of `OAI.SharpPlanar.Numerical.U88.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U88.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U88.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G221
import Definitions.Def_OAIQ098G223

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns90
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
noncomputable def column88_0_r3 : Fin 16 → Fin 16 → CBox := ![column88_0_r3_0,column88_0_r3_1,column88_0_r3_2,column88_0_r3_3,column88_0_r3_4,column88_0_r3_5,column88_0_r3_6,column88_0_r3_7,column88_0_r3_8,column88_0_r3_9,column88_0_r3_10,column88_0_r3_11,column88_0_r3_12,column88_0_r3_13,column88_0_r3_14,column88_0_r3_15]
noncomputable def column88_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column88_0_r0,column88_0_r1,column88_0_r2,column88_0_r3,column88_0_r4,column88_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments88
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
namespace cm88_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel1_0 j i k))
end cm88_1_0_0
namespace cm88_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel1_1 j i k))
end cm88_1_0_1
namespace cm88_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel3_0 j i k))
end cm88_3_0_0
namespace cm88_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel3_1 j i k))
end cm88_3_0_1
namespace cm88_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel4_0 j i k))
end cm88_4_0_0
namespace cm88_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column88_0 j i k).mul (kernel4_1 j i k))
end cm88_4_0_1
end SharpPlanar.CachedData

end OAI
end


