-- Prove2me | Definitions.Def_OAIQ334E031
-- name    : OAIQ334E031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:55:50.932593+00:00
-- url     : https://prove2.me/theorems/e86685d7-bf4a-4c1a-8df8-8f513962c01a
-- title:
--   Definitions bundle OAIQ334E031 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularEnergy`; the bundles `OAIQ334E007` and `OAIQ334E008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ334E032`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E007
import Definitions.Def_OAIQ334E008

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_GaussianPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular
open Construction

lemma realFourier_gaussian {α : ℝ} (hα : 0<α) (w : Plane) :
    realFourier (gaussian α) w=(α⁻¹*gaussian α⁻¹ w:ℝ) := by
  have he : (fun x => (gaussian α x:ℂ))=(fun x : Plane => exp (-(Real.pi:ℂ)*(α:ℂ)*‖x‖^2)) := by
    ext x
    simp [gaussian]
  rw [realFourier,he,complex_gaussian_transform (α:ℂ) hα]
  simp only [gaussian,ofReal_mul,ofReal_inv]
  congr 1
  rw [ofReal_exp]
  congr 1
  push_cast
  ring
end AtomicTriangular
end

end OAI
end


