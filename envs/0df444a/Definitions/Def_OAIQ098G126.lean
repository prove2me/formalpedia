-- Prove2me | Definitions.Def_OAIQ098G126
-- name    : OAIQ098G126
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:26:19.643139+00:00
-- url     : https://prove2.me/theorems/5d00c326-3f04-42e0-8414-9d0e73cec42d
-- title:
--   Definitions bundle OAIQ098G126 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm1_9_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm1_9_0_1.sums`, `OAI.SharpPlanar.CachedData.cm1_9_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_9_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_9_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_9_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_9_1_1.chunk`, `OAI.SharpPlanar.CachedData.kernel9_1`, `OAI.SharpPlanar.CachedData.kernel9_1_r4`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean), [`PlanarPacking_Certificate_LMoments9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments9.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G031`, `OAIQ098G038`, `OAIQ098G047`, `OAIQ098G123` and `OAIQ098G125` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1547` and `OAIQ098G1596`; the proofs of `OAI.SharpPlanar.Numerical.lentry1_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_4_contains_g` and `OAI.SharpPlanar.Numerical.lentry7_5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G031
import Definitions.Def_OAIQ098G038
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G123
import Definitions.Def_OAIQ098G125

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
noncomputable def kernel9_1_r4 : Fin 16 → Fin 16 → CBox := ![kernel9_1_r4_0,kernel9_1_r4_1,kernel9_1_r4_2,kernel9_1_r4_3,kernel9_1_r4_4,kernel9_1_r4_5,kernel9_1_r4_6,kernel9_1_r4_7,kernel9_1_r4_8,kernel9_1_r4_9,kernel9_1_r4_10,kernel9_1_r4_11,kernel9_1_r4_12,kernel9_1_r4_13,kernel9_1_r4_14,kernel9_1_r4_15]
noncomputable def kernel9_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel9_1_r0,kernel9_1_r1,kernel9_1_r2,kernel9_1_r3,kernel9_1_r4,kernel9_1_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments9
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
namespace cm1_9_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel9_1 j i k))
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_9_0_1
namespace cm1_9_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel9_1 j i k))
end cm1_9_1_1
namespace cm3_9_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel9_1 j i k))
end cm3_9_0_1
namespace cm3_9_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel9_1 j i k))
end cm3_9_1_1
namespace cm4_9_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel9_1 j i k))
end cm4_9_0_1
namespace cm4_9_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel9_1 j i k))
end cm4_9_1_1
end SharpPlanar.CachedData

end OAI
end


