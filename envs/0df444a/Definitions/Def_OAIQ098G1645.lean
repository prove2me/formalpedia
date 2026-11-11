-- Prove2me | Definitions.Def_OAIQ098G1645
-- name    : OAIQ098G1645
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T08:54:44.527478+00:00
-- url     : https://prove2.me/theorems/88c4af15-c72c-4417-b5b0-28f9a4aba8c0
-- title:
--   Definitions bundle OAIQ098G1645 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.coupledLeft`, `OAI.SharpPlanar.coupledRight`, `OAI.SharpPlanar.interpolationInverse`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_CoupledFull`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/CoupledFull.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G010` of this split; the published statement `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1651`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G010
import Theorems.Thm_OAI_SharpPlanar_Numerical_interpolation_exists_unique_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoupledFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coupled interpolation system

The finite inverse and tail estimates solve the interpolation equations in the space of absolutely summable coefficients.
-/

namespace SharpPlanar
open Numerical

noncomputable def interpolationInverse (neg : Bool) (r : X) : X :=
  Classical.choose (interpolation_exists_unique_g neg r)
noncomputable def coupledLeft (g₁ g₂ : X) : X :=
  (1/2:ℝ) • (interpolationInverse false (g₁+g₂)+interpolationInverse true (g₁-g₂))
noncomputable def coupledRight (g₁ g₂ : X) : X :=
  (1/2:ℝ) • (interpolationInverse false (g₁+g₂)-interpolationInverse true (g₁-g₂))
end SharpPlanar

end OAI
end


