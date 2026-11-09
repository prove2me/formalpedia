-- Prove2me | Definitions.Def_OAIQ098G307
-- name    : OAIQ098G307
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T04:15:39.939926+00:00
-- url     : https://prove2.me/theorems/82d36fd7-dc40-48e2-acfb-c83d8b117457
-- title:
--   Definitions bundle OAIQ098G307 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel12_0Expr`, `OAI.SharpPlanar.CachedData.kernel12_1Expr`, `OAI.SharpPlanar.CachedData.trans12`, `OAI.SharpPlanar.CachedData.trans13Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues20.lean), [`PlanarPacking_Certificate_TransformedPowers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G305` and `OAIQ098G306` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.kernel12_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel12_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_1_contains_g` and `OAI.SharpPlanar.CachedData.trans15_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G305
import Definitions.Def_OAIQ098G306

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers20
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
noncomputable def trans12 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans12_r0,trans12_r1,trans12_r2,trans12_r3,trans12_r4,trans12_r5]
noncomputable def trans13Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans12 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues20
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
noncomputable def kernel12_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans12 j i k)
noncomputable def kernel12_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans12 j i k)).mul (piI.mul (gridRows j i k).z)
end SharpPlanar.CachedData

end OAI
end


