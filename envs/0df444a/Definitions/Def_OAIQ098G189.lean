-- Prove2me | Definitions.Def_OAIQ098G189
-- name    : OAIQ098G189
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:54:12.678085+00:00
-- url     : https://prove2.me/theorems/749ece41-1fd2-487c-b8fc-1d70cdd26de8
-- title:
--   Definitions bundle OAIQ098G189 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm57_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm57_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm57_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm57_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm57_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm57_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm57_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm57_4_0_0.s0`, `OAI.SharpPlanar.CachedData.cm57_4_0_0.sums`, `OAI.SharpPlanar.CachedData.cm57_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.column57_0`, `OAI.SharpPlanar.CachedData.column57_0_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns60.lean), [`PlanarPacking_Certificate_UMoments57`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments57.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G187` and `OAIQ098G188` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G385`; the proofs of `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuminus_contains_g` and `OAI.SharpPlanar.Numerical.U57.wuplus_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G187
import Definitions.Def_OAIQ098G188

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns60
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
noncomputable def column57_0_r5 : Fin 16 → Fin 16 → CBox := ![column57_0_r5_0,column57_0_r5_1,column57_0_r5_2,column57_0_r5_3,column57_0_r5_4,column57_0_r5_5,column57_0_r5_6,column57_0_r5_7,column57_0_r5_8,column57_0_r5_9,column57_0_r5_10,column57_0_r5_11,column57_0_r5_12,column57_0_r5_13,column57_0_r5_14,column57_0_r5_15]
noncomputable def column57_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column57_0_r0,column57_0_r1,column57_0_r2,column57_0_r3,column57_0_r4,column57_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments57
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
namespace cm57_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm57_1_0_0
namespace cm57_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel1_1 j i k))
end cm57_1_0_1
namespace cm57_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel3_0 j i k))
end cm57_3_0_0
namespace cm57_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel3_1 j i k))
end cm57_3_0_1
namespace cm57_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm57_4_0_0
namespace cm57_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column57_0 j i k).mul (kernel4_1 j i k))
end cm57_4_0_1
end SharpPlanar.CachedData

end OAI
end


