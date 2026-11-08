-- Prove2me | Definitions.Def_OAIQ098G367
-- name    : OAIQ098G367
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:16:43.595859+00:00
-- url     : https://prove2.me/theorems/1de0166b-19fa-4b06-ac3d-a0512b0a30fa
-- title:
--   Definitions bundle OAIQ098G367 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 instance.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_CanonicalRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G364` and `OAIQ098G366` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SharpPlanar.IntegerBasis.density_finite_check_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G364
import Definitions.Def_OAIQ098G366

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

instance instDecidableDensityCheck (n : ℕ) (j : Fin 6) : Decidable (DensityCheck n j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end SharpPlanar.IntegerBasis

end OAI
end


