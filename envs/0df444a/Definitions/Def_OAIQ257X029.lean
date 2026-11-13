-- Prove2me | Definitions.Def_OAIQ257X029
-- name    : OAIQ257X029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T07:14:51.261739+00:00
-- url     : https://prove2.me/theorems/dc9bcab1-28c8-4b3f-9166-7657c51f2d64
-- title:
--   Definitions bundle OAIQ257X029 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.AtomicTriangular.gaussianPair`, `OAI.AtomicTriangular.largeGaussianPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ257X008` and `OAIQ257X028` of this split; the published statements `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_node_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_radial_x` and `OAI.AtomicTriangular.Construction.actualSchwartz_signs_x`.
--
--   **Imported by** (directly, in this split): the proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X008
import Definitions.Def_OAIQ257X028
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_fourier_side_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_fourier_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_node_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_radial_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_signs_x

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_GaussianPair
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
  first_radial := actualSchwartz_radial_x 0 _ _
  second_radial := actualSchwartz_radial_x 1 _ _
  fourier_first := actualSchwartz_fourier_x _ _
  fourier_second := actualSchwartz_fourier_side_x 1 _ _
  minorant x := (actualSchwartz_signs_x hα x).1
  positive x := (actualSchwartz_signs_x hα x).2
  contact x n hx := (actualSchwartz_node_x hα x n hx).1
  zeros x n hx := (actualSchwartz_node_x hα x n hx).2

def gaussianPair (α : ℝ) (hα : 0<α) : GaussianPair α :=
  if h : 1 ≤ α then largeGaussianPair h else
    reciprocalGaussianPair hα (largeGaussianPair ((one_le_inv₀ hα).mpr (le_of_not_ge h)))

end AtomicTriangular
end

end OAI
end


