-- Prove2me | Definitions.Def_OAIQ098G232
-- name    : OAIQ098G232
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:58:38.566209+00:00
-- url     : https://prove2.me/theorems/dee87a3e-7fef-4209-9ec0-e156922c08b3
-- title:
--   Definitions bundle OAIQ098G232 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm97_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm97_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm97_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm97_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm97_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm97_3_0_0.s0`, `OAI.SharpPlanar.CachedData.cm97_3_0_0.sums`, `OAI.SharpPlanar.CachedData.cm97_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm97_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm97_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.column97_0`, `OAI.SharpPlanar.CachedData.column97_0_r2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean), [`PlanarPacking_Certificate_UMoments97`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments97.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G229` and `OAIQ098G231` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G385`; the proofs of `OAI.SharpPlanar.Numerical.U97.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U97.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U97.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U97.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G229
import Definitions.Def_OAIQ098G231

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
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
noncomputable def column97_0_r2 : Fin 16 → Fin 16 → CBox := ![column97_0_r2_0,column97_0_r2_1,column97_0_r2_2,column97_0_r2_3,column97_0_r2_4,column97_0_r2_5,column97_0_r2_6,column97_0_r2_7,column97_0_r2_8,column97_0_r2_9,column97_0_r2_10,column97_0_r2_11,column97_0_r2_12,column97_0_r2_13,column97_0_r2_14,column97_0_r2_15]
noncomputable def column97_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column97_0_r0,column97_0_r1,column97_0_r2,column97_0_r3,column97_0_r4,column97_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments97
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
namespace cm97_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm97_1_0_0
namespace cm97_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel1_1 j i k))
end cm97_1_0_1
namespace cm97_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel3_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm97_3_0_0
namespace cm97_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel3_1 j i k))
end cm97_3_0_1
namespace cm97_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel4_0 j i k))
end cm97_4_0_0
namespace cm97_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column97_0 j i k).mul (kernel4_1 j i k))
end cm97_4_0_1
end SharpPlanar.CachedData

end OAI
end


