-- Prove2me | Definitions.Def_OAIQ098G1112
-- name    : OAIQ098G1112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:13:40.362388+00:00
-- url     : https://prove2.me/theorems/e3210d4f-a994-49a4-832a-87d25ea90e24
-- title:
--   Definitions bundle OAIQ098G1112 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm28_0_1_4.chunk`, `OAI.SharpPlanar.CachedData.hm31_0_1_4.chunk`, `OAI.SharpPlanar.CachedData.hm33_0_1_4.chunk`, `OAI.SharpPlanar.CachedData.hm36_0_1_4.chunk`, `OAI.SharpPlanar.CachedData.hm37_0_1_4.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock28_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock28_10.lean), [`PlanarPacking_Certificate_LowBlock31_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock31_10.lean), [`PlanarPacking_Certificate_LowBlock33_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock33_10.lean), [`PlanarPacking_Certificate_LowBlock36_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock36_10.lean), [`PlanarPacking_Certificate_LowBlock37_10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock37_10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G018`, `OAIQ098G395` and `OAIQ098G619` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein28.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein28.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein31.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein33.N1_left.bound_g`, `OAI.SharpPlanar.Bernstein33.N1_right.bound_g`, `OAI.SharpPlanar.Bernstein36.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein36.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_left.t2_contains_g` and `OAI.SharpPlanar.Bernstein37.N1_right.t2_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G619

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock28_10
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
namespace hm28_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk28_1_4 j i k))
end hm28_0_1_4
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock31_10
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
namespace hm31_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk31_1_4 j i k))
end hm31_0_1_4
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock33_10
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
namespace hm33_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk33_1_4 j i k))
end hm33_0_1_4
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock36_10
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
namespace hm36_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk36_1_4 j i k))
end hm36_0_1_4
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock37_10
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
namespace hm37_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk37_1_4 j i k))
end hm37_0_1_4
end SharpPlanar.CachedData

end OAI
end


