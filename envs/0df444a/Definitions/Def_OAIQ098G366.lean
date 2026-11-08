-- Prove2me | Definitions.Def_OAIQ098G366
-- name    : OAIQ098G366
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:15:39.87632+00:00
-- url     : https://prove2.me/theorems/c7ba3842-5b62-400e-9525-009f8244cec6
-- title:
--   Definitions bundle OAIQ098G366 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 instance.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_CanonicalRows`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CanonicalRows.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G250` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G367`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G250

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerIntervals

instance instDecidableSqNormCheck (a : CBox) (m n : ℤ) : Decidable (a.SqNormCheck m n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end SharpPlanar.IntegerIntervals

end OAI
end


