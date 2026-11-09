-- Prove2me | Definitions.Def_OAIQ098G009
-- name    : OAIQ098G009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:57:03.816193+00:00
-- url     : https://prove2.me/theorems/a3e389ee-1d4e-4556-8f23-7db9335791b7
-- title:
--   Definitions bundle OAIQ098G009 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.finiteRestrictionLinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_FiniteCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FiniteCoordinates.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G010`; the statement `OAI.SharpPlanar.finiteRestriction_bound_g`; the proof of `OAI.SharpPlanar.finiteRestriction_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
noncomputable def finiteRestrictionLinear : X →ₗ[ℝ] L1Finite ι where
  toFun x := WithLp.toLp 1 (fun i => x (e i))
  map_add' := by intro x y; ext i; rfl
  map_smul' := by intro r x; ext i; rfl
end
end SharpPlanar

end OAI
end


