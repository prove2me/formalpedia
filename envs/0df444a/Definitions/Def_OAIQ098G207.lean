-- Prove2me | Definitions.Def_OAIQ098G207
-- name    : OAIQ098G207
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:56:24.735912+00:00
-- url     : https://prove2.me/theorems/c0220fc6-0536-45a4-aa8a-e67c11f80600
-- title:
--   Definitions bundle OAIQ098G207 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm75_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm75_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm75_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm75_3_0_0.s0`, `OAI.SharpPlanar.CachedData.cm75_3_0_0.sums`, `OAI.SharpPlanar.CachedData.cm75_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm75_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm75_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.column75_0`, `OAI.SharpPlanar.CachedData.column75_0_r4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns80.lean), [`PlanarPacking_Certificate_UMoments75`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments75.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G204` and `OAIQ098G206` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G385`; the statement `OAI.SharpPlanar.CachedData.column75_0_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.column75_0_contains_g`, `OAI.SharpPlanar.Numerical.U75.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U75.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U75.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U75.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G204
import Definitions.Def_OAIQ098G206

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns80
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
noncomputable def column75_0_r4 : Fin 16 → Fin 16 → CBox := ![column75_0_r4_0,column75_0_r4_1,column75_0_r4_2,column75_0_r4_3,column75_0_r4_4,column75_0_r4_5,column75_0_r4_6,column75_0_r4_7,column75_0_r4_8,column75_0_r4_9,column75_0_r4_10,column75_0_r4_11,column75_0_r4_12,column75_0_r4_13,column75_0_r4_14,column75_0_r4_15]
noncomputable def column75_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column75_0_r0,column75_0_r1,column75_0_r2,column75_0_r3,column75_0_r4,column75_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments75
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
namespace cm75_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel1_0 j i k))
end cm75_1_0_0
namespace cm75_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel1_1 j i k))
end cm75_1_0_1
namespace cm75_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel3_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm75_3_0_0
namespace cm75_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel3_1 j i k))
end cm75_3_0_1
namespace cm75_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel4_0 j i k))
end cm75_4_0_0
namespace cm75_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column75_0 j i k).mul (kernel4_1 j i k))
end cm75_4_0_1
end SharpPlanar.CachedData

end OAI
end


