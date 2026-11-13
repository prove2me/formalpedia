-- Prove2me | Definitions.Def_OAIQ262T261
-- name    : OAIQ262T261
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:53:01.433373+00:00
-- url     : https://prove2.me/theorems/78ebb412-5cc7-4706-a7f5-6dd1be3a0863
-- title:
--   Definitions bundle OAIQ262T261 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 2 definitions and 1 theorem. The definitions and types are `OAI.AtomicTriangular.gaussianPair`, `OAI.AtomicTriangular.largeGaussianPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_Normalization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean), [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T149`, `OAIQ262T150` and `OAIQ262T259` of this split; the published statement `OAI.AtomicTriangular.Construction.global_signs_tg`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T262`; the proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T149
import Definitions.Def_OAIQ262T150
import Definitions.Def_OAIQ262T259
import Theorems.Thm_OAI_AtomicTriangular_Construction_global_signs_tg

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_signs {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x ≤ AtomicTriangular.gaussian α x ∧
      0 ≤ actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x := by
  have hj := global_signs_tg (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le (radial_nonneg x)
  rw [actualSchwartz_apply,actualSchwartz_apply,←gaussian_normalization hα x]
  exact ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj.1 (Real.exp_pos _).le) (normalizingDen_pos (gaussianZ_bounds hα).1).le,
    div_nonneg (mul_nonneg (Real.exp_pos _).le hj.2) (normalizingDen_pos (gaussianZ_bounds hα).1).le⟩
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_GaussianPair
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
  first_radial := actualSchwartz_radial 0 _ _
  second_radial := actualSchwartz_radial 1 _ _
  fourier_first := actualSchwartz_fourier _ _
  fourier_second := actualSchwartz_fourier_side 1 _ _
  minorant x := (actualSchwartz_signs hα x).1
  positive x := (actualSchwartz_signs hα x).2
  contact x n hx := (actualSchwartz_node hα x n hx).1
  zeros x n hx := (actualSchwartz_node hα x n hx).2

def gaussianPair (α : ℝ) (hα : 0<α) : GaussianPair α :=
  if h : 1 ≤ α then largeGaussianPair h else
    reciprocalGaussianPair hα (largeGaussianPair ((one_le_inv₀ hα).mpr (le_of_not_ge h)))

end AtomicTriangular
end

end OAI
end


