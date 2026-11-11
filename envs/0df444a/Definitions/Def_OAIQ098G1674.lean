-- Prove2me | Definitions.Def_OAIQ098G1674
-- name    : OAIQ098G1674
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T08:57:33.185741+00:00
-- url     : https://prove2.me/theorems/8517d366-f73d-47d9-b949-8f059a412757
-- title:
--   Definitions bundle OAIQ098G1674 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.coefficientError`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_InterpolationError`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/InterpolationError.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1651` and `OAIQ098G1673` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g` and `OAI.SharpPlanar.tail_second_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1651
import Definitions.Def_OAIQ098G1673

section
-- module Solutions.OAIQ098_PP.PlanarPacking_InterpolationError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Error bounds for cardinal interpolation

Norm bounds for the inverse interpolation operator control the distance from the finite coefficient families to the exact solution.
-/

namespace SharpPlanar
open Numerical
noncomputable def coefficientError (a : Bool) : X := tableList a-exactList a
end SharpPlanar

end OAI
end


