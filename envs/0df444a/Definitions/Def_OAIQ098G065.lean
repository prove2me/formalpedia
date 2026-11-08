-- Prove2me | Definitions.Def_OAIQ098G065
-- name    : OAIQ098G065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:03:54.580246+00:00
-- url     : https://prove2.me/theorems/e8d1ec63-af28-4a73-a3b7-f7cf09d9180f
-- title:
--   Definitions bundle OAIQ098G065 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power2`, `OAI.SharpPlanar.CachedData.power2_r4`, `OAI.SharpPlanar.CachedData.trans4Expr`, `OAI.SharpPlanar.IntegerCompact.roots16`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers10.lean), [`PlanarPacking_Certificate_TransformedPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean), [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G059` and `OAIQ098G064` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G067` and `OAIQ098G085`; the proofs of `OAI.SharpPlanar.CachedData.kernel4_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel4_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel7_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel7_1_contains_g` and `OAI.SharpPlanar.CachedData.trans8_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G059
import Definitions.Def_OAIQ098G064

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
def roots16 : Fin 32 → CBox := ![IntegerRoots.root512,IntegerRoots.root513,IntegerRoots.root514,IntegerRoots.root515,IntegerRoots.root516,IntegerRoots.root517,IntegerRoots.root518,IntegerRoots.root519,IntegerRoots.root520,IntegerRoots.root521,IntegerRoots.root522,IntegerRoots.root523,IntegerRoots.root524,IntegerRoots.root525,IntegerRoots.root526,IntegerRoots.root527,IntegerRoots.root528,IntegerRoots.root529,IntegerRoots.root530,IntegerRoots.root531,IntegerRoots.root532,IntegerRoots.root533,IntegerRoots.root534,IntegerRoots.root535,IntegerRoots.root536,IntegerRoots.root537,IntegerRoots.root538,IntegerRoots.root539,IntegerRoots.root540,IntegerRoots.root541,IntegerRoots.root542,IntegerRoots.root543]
end SharpPlanar.IntegerCompact


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
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
noncomputable def power2_r4 : Fin 16 → Fin 16 → CBox := ![power2_r4_0,power2_r4_1,power2_r4_2,power2_r4_3,power2_r4_4,power2_r4_5,power2_r4_6,power2_r4_7,power2_r4_8,power2_r4_9,power2_r4_10,power2_r4_11,power2_r4_12,power2_r4_13,power2_r4_14,power2_r4_15]
noncomputable def power2 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power2_r0,power2_r1,power2_r2,power2_r3,power2_r4,power2_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
noncomputable def trans4Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans3 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


