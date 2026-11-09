-- Prove2me | Definitions.Def_OAIQ098G193
-- name    : OAIQ098G193
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:43:42.808457+00:00
-- url     : https://prove2.me/theorems/eb0527e3-e3d1-4280-97d2-3cd9a3fa9e2e
-- title:
--   Definitions bundle OAIQ098G193 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm61_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm61_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm61_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm61_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm61_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm61_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm61_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm61_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.column61_0`, `OAI.SharpPlanar.CachedData.column61_0_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns70.lean), [`PlanarPacking_Certificate_UMoments61`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments61.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G190` and `OAIQ098G192` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G385`; the proofs of `OAI.SharpPlanar.Numerical.U61.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U61.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U61.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U61.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G190
import Definitions.Def_OAIQ098G192

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns70
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
noncomputable def column61_0_r5 : Fin 16 → Fin 16 → CBox := ![column61_0_r5_0,column61_0_r5_1,column61_0_r5_2,column61_0_r5_3,column61_0_r5_4,column61_0_r5_5,column61_0_r5_6,column61_0_r5_7,column61_0_r5_8,column61_0_r5_9,column61_0_r5_10,column61_0_r5_11,column61_0_r5_12,column61_0_r5_13,column61_0_r5_14,column61_0_r5_15]
noncomputable def column61_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column61_0_r0,column61_0_r1,column61_0_r2,column61_0_r3,column61_0_r4,column61_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments61
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
namespace cm61_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm61_1_0_0
namespace cm61_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel1_1 j i k))
end cm61_1_0_1
namespace cm61_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel3_0 j i k))
end cm61_3_0_0
namespace cm61_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel3_1 j i k))
end cm61_3_0_1
namespace cm61_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel4_0 j i k))
end cm61_4_0_0
namespace cm61_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column61_0 j i k).mul (kernel4_1 j i k))
end cm61_4_0_1
end SharpPlanar.CachedData

end OAI
end


