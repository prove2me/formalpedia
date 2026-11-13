-- Prove2me | Definitions.Def_OAIQ334E010
-- name    : OAIQ334E010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T11:36:23.540618+00:00
-- url     : https://prove2.me/theorems/919996f2-600e-478f-bba6-99454cd060c0
-- title:
--   Definitions bundle OAIQ334E010 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.AtomicTriangular.Radial`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Basic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Basic.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularEnergy`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ334E030`; the statement `OAI.AtomicTriangular.Construction.actualSchwartz_radial_eu`; the proof of `OAI.AtomicTriangular.Construction.actualSchwartz_radial_eu`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularEnergy

section
-- module Solutions.OAIQ334_EU.Triangular_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex Polynomial

namespace AtomicTriangular

def Radial (f : Plane → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → f x = f y

end AtomicTriangular

end

end OAI
end


