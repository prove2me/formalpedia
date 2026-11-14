-- Prove2me | Definitions.Def_OAIQ334E033
-- name    : OAIQ334E033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T19:37:58.792936+00:00
-- url     : https://prove2.me/theorems/e9cdae69-f2b0-49fa-aeac-566857fd42fb
-- title:
--   Definitions bundle OAIQ334E033 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.AtomicTriangular.gaussianPair`, `OAI.AtomicTriangular.largeGaussianPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularEnergy`; the bundles `OAIQ334E009` and `OAIQ334E032` of this split; the published statements `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_eu`, `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_eu`, `OAI.AtomicTriangular.Construction.actualSchwartz_node_eu`, `OAI.AtomicTriangular.Construction.actualSchwartz_radial_eu` and `OAI.AtomicTriangular.Construction.actualSchwartz_signs_eu`.
--
--   **Imported by** (directly, in this split): the statement `OAI.AtomicTriangular.gaussianPair_poisson_eu`; the proofs of `OAI.AtomicTriangular.gaussianPair_poisson_eu` and `OAI.AtomicTriangular.universal_energy_minimum`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E009
import Definitions.Def_OAIQ334E032
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_fourier_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_fourier_side_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_node_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_radial_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_signs_eu

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

def largeGaussianPair {α : ℝ} (hα : 1 ≤ α) : GaussianPair α where
  first := actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le
  second := actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le
  first_radial := actualSchwartz_radial_eu 0 _ _
  second_radial := actualSchwartz_radial_eu 1 _ _
  fourier_first := actualSchwartz_fourier_eu _ _
  fourier_second := actualSchwartz_fourier_side_eu 1 _ _
  minorant x := (actualSchwartz_signs_eu hα x).1
  positive x := (actualSchwartz_signs_eu hα x).2
  contact x n hx := (actualSchwartz_node_eu hα x n hx).1
  zeros x n hx := (actualSchwartz_node_eu hα x n hx).2

def gaussianPair (α : ℝ) (hα : 0<α) : GaussianPair α :=
  if h : 1 ≤ α then largeGaussianPair h else
    reciprocalGaussianPair hα (largeGaussianPair ((one_le_inv₀ hα).mpr (le_of_not_ge h)))

end AtomicTriangular
end

end OAI
end


