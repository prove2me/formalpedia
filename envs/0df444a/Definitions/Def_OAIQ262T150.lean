-- Prove2me | Definitions.Def_OAIQ262T150
-- name    : OAIQ262T150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:24:57.436564+00:00
-- url     : https://prove2.me/theorems/39701030-bd7a-480e-b11c-e358912eb7ab
-- title:
--   Definitions bundle OAIQ262T150 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.AtomicTriangular.reciprocalGaussianPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T083`, `OAIQ262T084` and `OAIQ262T112` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T266`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T083
import Definitions.Def_OAIQ262T084
import Definitions.Def_OAIQ262T112

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

def reciprocalGaussianPair {α : ℝ} (hα : 0<α) (p : GaussianPair α⁻¹) : GaussianPair α where
  first := gaussianSchwartz α hα-α⁻¹ • p.second
  second := α⁻¹ • (gaussianSchwartz α⁻¹ (inv_pos.mpr hα)-p.first)
  first_radial := by
    intro x y hxy
    simp only [sub_apply,smul_apply,smul_eq_mul,gaussianSchwartz_apply,
      gaussian_radial α x y hxy,p.second_radial x y hxy]
  second_radial := by
    intro x y hxy
    simp only [sub_apply,smul_apply,smul_eq_mul,gaussianSchwartz_apply,
      gaussian_radial α⁻¹ x y hxy,p.first_radial x y hxy]
  fourier_first w := by
    rw [realFourier_sub,gaussianSchwartz_coe]
    change realFourier (gaussian α) w-realFourier (α⁻¹ • (p.second:Plane → ℝ)) w=_
    rw [realFourier_gaussian hα,realFourier_smul,p.fourier_second]
    simp only [smul_apply,sub_apply,smul_eq_mul,gaussianSchwartz_apply,ofReal_mul,ofReal_sub]
    ring
  fourier_second w := by
    change realFourier (α⁻¹ • ((gaussianSchwartz α⁻¹ (inv_pos.mpr hα)-p.first : 𝓢(Plane,ℝ)):Plane → ℝ)) w=_
    rw [realFourier_smul,realFourier_sub,gaussianSchwartz_coe]
    rw [realFourier_gaussian (inv_pos.mpr hα),p.fourier_first,inv_inv]
    simp only [sub_apply,smul_apply,smul_eq_mul,gaussianSchwartz_apply,ofReal_mul,ofReal_sub,ofReal_inv]
    field_simp [hα.ne']
  minorant x := by
    change gaussianSchwartz α hα x-α⁻¹*p.second x ≤ _
    rw [gaussianSchwartz_apply]
    exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr hα.le) (p.positive x))
  positive x := by
    change 0 ≤ α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) x-p.first x)
    rw [gaussianSchwartz_apply]
    exact mul_nonneg (inv_nonneg.mpr hα.le) (sub_nonneg.mpr (p.minorant x))
  contact x n hx := by
    change gaussianSchwartz α hα x-α⁻¹*p.second x=_
    rw [p.zeros x n hx,mul_zero,sub_zero,gaussianSchwartz_apply]
  zeros x n hx := by
    change α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) x-p.first x)=0
    rw [p.contact x n hx,gaussianSchwartz_apply,sub_self,mul_zero]

end AtomicTriangular
end

end OAI
end


