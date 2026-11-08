-- Prove2me | Definitions.Def_OAIQ098G124
-- name    : OAIQ098G124
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:23:28.854402+00:00
-- url     : https://prove2.me/theorems/84def729-1564-4b14-88ed-b7a836a72e9d
-- title:
--   Definitions bundle OAIQ098G124 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 10 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm1_7_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm1_7_0_0.s0`, `OAI.SharpPlanar.CachedData.cm1_7_0_0.sums`, `OAI.SharpPlanar.CachedData.cm1_7_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_7_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_7_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_7_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_7_1_0.chunk`, `OAI.SharpPlanar.CachedData.kernel7_0`, `OAI.SharpPlanar.CachedData.kernel7_0_r1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean), [`PlanarPacking_Certificate_LMoments7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments7.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G031`, `OAIQ098G038`, `OAIQ098G047`, `OAIQ098G121` and `OAIQ098G123` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1537`, `OAIQ098G1584`, `OAIQ098G712`, `OAIQ098G713`, `OAIQ098G714`, `OAIQ098G715`, `OAIQ098G716`, `OAIQ098G717`, `OAIQ098G718`, `OAIQ098G719`, `OAIQ098G720`, `OAIQ098G721` and `OAIQ098G722`; the statement `OAI.SharpPlanar.CachedData.kernel7_0_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.kernel7_0_contains_g`, `OAI.SharpPlanar.Numerical.Lmat_column_g`, `OAI.SharpPlanar.Numerical.lentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_4_contains_g` and `OAI.SharpPlanar.Numerical.lentry6_5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G031
import Definitions.Def_OAIQ098G038
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G121
import Definitions.Def_OAIQ098G123

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
noncomputable def kernel7_0_r1 : Fin 16 → Fin 16 → CBox := ![kernel7_0_r1_0,kernel7_0_r1_1,kernel7_0_r1_2,kernel7_0_r1_3,kernel7_0_r1_4,kernel7_0_r1_5,kernel7_0_r1_6,kernel7_0_r1_7,kernel7_0_r1_8,kernel7_0_r1_9,kernel7_0_r1_10,kernel7_0_r1_11,kernel7_0_r1_12,kernel7_0_r1_13,kernel7_0_r1_14,kernel7_0_r1_15]
noncomputable def kernel7_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel7_0_r0,kernel7_0_r1,kernel7_0_r2,kernel7_0_r3,kernel7_0_r4,kernel7_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments7
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
namespace cm1_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel7_0 j i k))
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_7_0_0
namespace cm1_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel7_0 j i k))
end cm1_7_1_0
namespace cm3_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel7_0 j i k))
end cm3_7_0_0
namespace cm3_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel7_0 j i k))
end cm3_7_1_0
namespace cm4_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel7_0 j i k))
end cm4_7_0_0
namespace cm4_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel7_0 j i k))
end cm4_7_1_0
end SharpPlanar.CachedData

end OAI
end


