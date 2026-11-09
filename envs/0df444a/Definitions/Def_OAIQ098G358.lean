-- Prove2me | Definitions.Def_OAIQ098G358
-- name    : OAIQ098G358
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T04:15:09.806914+00:00
-- url     : https://prove2.me/theorems/244bcf93-8d14-4f86-8b85-0b9581b0bf80
-- title:
--   Definitions bundle OAIQ098G358 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans10`, `OAI.SharpPlanar.CachedData.trans11Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean), [`PlanarPacking_Certificate_TransformedPowers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G064`, `OAIQ098G355`, `OAIQ098G356` and `OAIQ098G357` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.kernel12_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel12_1_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel13_1_contains_g` and `OAI.SharpPlanar.CachedData.trans15_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G355
import Definitions.Def_OAIQ098G356
import Definitions.Def_OAIQ098G357

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
noncomputable def trans10 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans10_r0,trans10_r1,trans10_r2,trans10_r3,trans10_r4,trans10_r5]
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def trans11Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans10 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


