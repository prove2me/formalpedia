-- Prove2me | Definitions.Def_OAIQ098G159
-- name    : OAIQ098G159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:50:18.097202+00:00
-- url     : https://prove2.me/theorems/34a04f12-db2e-4868-9b1c-9098c110c8e9
-- title:
--   Definitions bundle OAIQ098G159 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 16 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm3_15_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_15_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_15_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_15_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_16_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_16_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm3_16_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm3_16_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_15_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_15_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_15_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_15_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_16_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_16_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm4_16_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm4_16_1_1.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LMoments15`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments15.lean), [`PlanarPacking_Certificate_LMoments16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments16.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G031`, `OAIQ098G038`, `OAIQ098G047` and `OAIQ098G121` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.cm3_16_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_16_1_1.contains_g`, `OAI.SharpPlanar.Numerical.lentry10_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_4_contains_g` and `OAI.SharpPlanar.Numerical.lentry5_5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G031
import Definitions.Def_OAIQ098G038
import Definitions.Def_OAIQ098G047
import Definitions.Def_OAIQ098G121

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments15
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
namespace cm3_15_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel15_0 j i k))
end cm3_15_0_0
namespace cm3_15_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel15_1 j i k))
end cm3_15_0_1
namespace cm3_15_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel15_0 j i k))
end cm3_15_1_0
namespace cm3_15_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel15_1 j i k))
end cm3_15_1_1
namespace cm4_15_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel15_0 j i k))
end cm4_15_0_0
namespace cm4_15_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel15_1 j i k))
end cm4_15_0_1
namespace cm4_15_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel15_0 j i k))
end cm4_15_1_0
namespace cm4_15_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel15_1 j i k))
end cm4_15_1_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments16
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
namespace cm3_16_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel16_0 j i k))
end cm3_16_0_0
namespace cm3_16_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel16_1 j i k))
end cm3_16_0_1
namespace cm3_16_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel16_0 j i k))
end cm3_16_1_0
namespace cm3_16_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel16_1 j i k))
end cm3_16_1_1
namespace cm4_16_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel16_0 j i k))
end cm4_16_0_0
namespace cm4_16_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel16_1 j i k))
end cm4_16_0_1
namespace cm4_16_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel16_0 j i k))
end cm4_16_1_0
namespace cm4_16_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel16_1 j i k))
end cm4_16_1_1
end SharpPlanar.CachedData

end OAI
end


