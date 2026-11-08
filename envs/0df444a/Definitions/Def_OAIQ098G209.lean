-- Prove2me | Definitions.Def_OAIQ098G209
-- name    : OAIQ098G209
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:57:10.485202+00:00
-- url     : https://prove2.me/theorems/926ddd4f-75b4-4032-8f29-3434e6068dc2
-- title:
--   Definitions bundle OAIQ098G209 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm76_1_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm76_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm76_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm76_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm76_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm76_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.column76_0`, `OAI.SharpPlanar.CachedData.column76_0_r4`, `OAI.SharpPlanar.CachedData.column76_0_r5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns80`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns80.lean), [`PlanarPacking_Certificate_UMoments76`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments76.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G206` and `OAIQ098G208` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G385`; the statement `OAI.SharpPlanar.CachedData.column76_0_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.column76_0_contains_g`, `OAI.SharpPlanar.Numerical.U76.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U76.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U76.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U76.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G206
import Definitions.Def_OAIQ098G208

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
noncomputable def column76_0_r4 : Fin 16 → Fin 16 → CBox := ![column76_0_r4_0,column76_0_r4_1,column76_0_r4_2,column76_0_r4_3,column76_0_r4_4,column76_0_r4_5,column76_0_r4_6,column76_0_r4_7,column76_0_r4_8,column76_0_r4_9,column76_0_r4_10,column76_0_r4_11,column76_0_r4_12,column76_0_r4_13,column76_0_r4_14,column76_0_r4_15]
noncomputable def column76_0_r5 : Fin 16 → Fin 16 → CBox := ![column76_0_r5_0,column76_0_r5_1,column76_0_r5_2,column76_0_r5_3,column76_0_r5_4,column76_0_r5_5,column76_0_r5_6,column76_0_r5_7,column76_0_r5_8,column76_0_r5_9,column76_0_r5_10,column76_0_r5_11,column76_0_r5_12,column76_0_r5_13,column76_0_r5_14,column76_0_r5_15]
noncomputable def column76_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![column76_0_r0,column76_0_r1,column76_0_r2,column76_0_r3,column76_0_r4,column76_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments76
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
namespace cm76_1_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel1_0 j i k))
end cm76_1_0_0
namespace cm76_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel1_1 j i k))
end cm76_1_0_1
namespace cm76_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel3_0 j i k))
end cm76_3_0_0
namespace cm76_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel3_1 j i k))
end cm76_3_0_1
namespace cm76_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel4_0 j i k))
end cm76_4_0_0
namespace cm76_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column76_0 j i k).mul (kernel4_1 j i k))
end cm76_4_0_1
end SharpPlanar.CachedData

end OAI
end


