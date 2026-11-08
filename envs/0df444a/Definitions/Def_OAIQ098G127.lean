-- Prove2me | Definitions.Def_OAIQ098G127
-- name    : OAIQ098G127
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:25:38.750556+00:00
-- url     : https://prove2.me/theorems/70802fc8-57c8-4463-be5c-0b94af617051
-- title:
--   Definitions bundle OAIQ098G127 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm1_9_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_7_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_7_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_9_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_9_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_7_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_7_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_9_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_9_1_0.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LMoments7`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments7.lean), [`PlanarPacking_Certificate_LMoments9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments9.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G031`, `OAIQ098G038`, `OAIQ098G047` and `OAIQ098G123` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.Lmat_column_g`, `OAI.SharpPlanar.Numerical.lentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_4_contains_g` and `OAI.SharpPlanar.Numerical.lentry7_5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G031
import Definitions.Def_OAIQ098G038
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G123

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
namespace cm3_7_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel7_1 j i k))
end cm3_7_0_1
namespace cm3_7_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel7_1 j i k))
end cm3_7_1_1
namespace cm4_7_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel7_1 j i k))
end cm4_7_0_1
namespace cm4_7_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel7_1 j i k))
end cm4_7_1_1
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
namespace cm1_9_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel9_0 j i k))
end cm1_9_1_0
namespace cm3_9_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel9_0 j i k))
end cm3_9_0_0
namespace cm3_9_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel9_0 j i k))
end cm3_9_1_0
namespace cm4_9_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel9_0 j i k))
end cm4_9_0_0
namespace cm4_9_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel9_0 j i k))
end cm4_9_1_0
end SharpPlanar.CachedData

end OAI
end


