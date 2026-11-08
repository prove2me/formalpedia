-- Prove2me | Definitions.Def_OAIQ098G1032
-- name    : OAIQ098G1032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:05:36.489737+00:00
-- url     : https://prove2.me/theorems/88f071d1-def4-42cd-b57a-62ce036f5504
-- title:
--   Definitions bundle OAIQ098G1032 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.hm21_1_0_12.chunk`, `OAI.SharpPlanar.CachedData.hm21_1_0_13.chunk`, `OAI.SharpPlanar.CachedData.hm24_1_0_12.chunk`, `OAI.SharpPlanar.CachedData.hm24_1_0_13.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LowBlock21_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock21_1.lean), [`PlanarPacking_Certificate_LowBlock24_1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LowBlock24_1.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G018`, `OAIQ098G410` and `OAIQ098G579` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein21.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_right.t10_contains_g`, `OAI.SharpPlanar.Bernstein21.N1_right.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t10_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_left.t11_contains_g`, `OAI.SharpPlanar.Bernstein24.N1_right.t10_contains_g` and `OAI.SharpPlanar.Bernstein24.N1_right.t11_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G018
import Definitions.Def_OAIQ098G410
import Definitions.Def_OAIQ098G579

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_1
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
namespace hm21_1_0_12
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk21_0_12 j i k))
end hm21_1_0_12
namespace hm21_1_0_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk21_0_13 j i k))
end hm21_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_1
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
namespace hm24_1_0_12
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk24_0_12 j i k))
end hm24_1_0_12
namespace hm24_1_0_13
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk24_0_13 j i k))
end hm24_1_0_13
end SharpPlanar.CachedData

end OAI
end


