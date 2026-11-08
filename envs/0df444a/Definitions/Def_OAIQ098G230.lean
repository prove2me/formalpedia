-- Prove2me | Definitions.Def_OAIQ098G230
-- name    : OAIQ098G230
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:58:41.153518+00:00
-- url     : https://prove2.me/theorems/5749c8f7-f553-4652-8eaa-434eafc05478
-- title:
--   Definitions bundle OAIQ098G230 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm96_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm96_1_0_0.s0`, `OAI.SharpPlanar.CachedData.cm96_1_0_0.sums`, `OAI.SharpPlanar.CachedData.cm96_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm96_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm96_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm96_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm96_4_0_0.s0`, `OAI.SharpPlanar.CachedData.cm96_4_0_0.sums`, `OAI.SharpPlanar.CachedData.cm96_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.column96_0`, `OAI.SharpPlanar.CachedData.column96_0_r2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns100.lean), [`PlanarPacking_Certificate_UMoments96`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments96.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G227` and `OAIQ098G229` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G385`; the proofs of `OAI.SharpPlanar.Numerical.U96.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U96.entry4_0_contains_g` and `OAI.SharpPlanar.Numerical.U96.entry5_0_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G227
import Definitions.Def_OAIQ098G229

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
noncomputable def column96_0_r2 : Fin 16 → Fin 16 → CBox := ![column96_0_r2_0,column96_0_r2_1,column96_0_r2_2,column96_0_r2_3,column96_0_r2_4,column96_0_r2_5,column96_0_r2_6,column96_0_r2_7,column96_0_r2_8,column96_0_r2_9,column96_0_r2_10,column96_0_r2_11,column96_0_r2_12,column96_0_r2_13,column96_0_r2_14,column96_0_r2_15]
noncomputable def column96_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column96_0_r0,column96_0_r1,column96_0_r2,column96_0_r3,column96_0_r4,column96_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments96
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
namespace cm96_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel1_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm96_1_0_0
namespace cm96_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel1_1 j i k))
end cm96_1_0_1
namespace cm96_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel3_0 j i k))
end cm96_3_0_0
namespace cm96_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel3_1 j i k))
end cm96_3_0_1
namespace cm96_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel4_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm96_4_0_0
namespace cm96_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column96_0 j i k).mul (kernel4_1 j i k))
end cm96_4_0_1
end SharpPlanar.CachedData

end OAI
end


