-- Prove2me | Definitions.Def_OAIQ098G380
-- name    : OAIQ098G380
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T08:46:47.874421+00:00
-- url     : https://prove2.me/theorems/b77c970e-391c-453f-8ade-8d24e20fa059
-- title:
--   Definitions bundle OAIQ098G380 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.finiteEquiv`, `OAI.SharpPlanar.Numerical.finiteV`, `OAI.SharpPlanar.liftedInverse`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_FiniteFull`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteFull.lean), [`PlanarPacking_FiniteLift`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteLift.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G010` of this split; the published statement `OAI.SharpPlanar.Numerical.finiteA_bijective_g`.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.interpolation_exists_unique_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g` and `OAI.SharpPlanar.tail_second_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G010
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteA_bijective_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Lift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


noncomputable def liftedInverse (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F) : E →L[ℝ] E :=
  1 + I.comp (V.comp (R.comp S))

end Lift
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
noncomputable def finiteEquiv (neg : Bool) : L1Finite FiniteIndex ≃L[ℝ] L1Finite FiniteIndex :=
  (LinearEquiv.ofBijective (finiteA neg).toLinearMap (finiteA_bijective_g neg)).toContinuousLinearEquiv
noncomputable def finiteV (neg : Bool) : L1Finite FiniteIndex →L[ℝ] L1Finite FiniteIndex :=
  (finiteEquiv neg).symm.toContinuousLinearMap
end SharpPlanar.Numerical

end OAI
end


