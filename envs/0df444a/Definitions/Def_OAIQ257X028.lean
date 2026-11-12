-- Prove2me | Definitions.Def_OAIQ257X028
-- name    : OAIQ257X028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:51:24.838115+00:00
-- url     : https://prove2.me/theorems/46e012a0-a812-4235-aeca-99cac6383e9b
-- title:
--   Definitions bundle OAIQ257X028 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 2 definitions and 2 theorems. The definitions and types are `OAI.AtomicTriangular.gaussianSchwartz`, `OAI.AtomicTriangular.reciprocalGaussianPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ257X006`, `OAIQ257X026` and `OAIQ257X027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ257X029`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X006
import Definitions.Def_OAIQ257X026
import Definitions.Def_OAIQ257X027

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

def gaussianSchwartz (α : ℝ) (hα : 0<α) : 𝓢(Plane,ℝ) :=
  Analysis.gaussianSchwartz (Real.pi*α) (mul_pos Real.pi_pos hα)
lemma gaussianSchwartz_apply (α : ℝ) (hα : 0<α) (x : Plane) :
    gaussianSchwartz α hα x=gaussian α x := by
  simp only [gaussianSchwartz,Analysis.gaussianSchwartz_apply,gaussian,neg_mul]
lemma gaussianSchwartz_coe (α : ℝ) (hα : 0<α) :
    (gaussianSchwartz α hα : Plane → ℝ)=gaussian α := funext (gaussianSchwartz_apply α hα)

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


