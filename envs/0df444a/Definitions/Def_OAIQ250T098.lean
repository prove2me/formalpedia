-- Prove2me | Definitions.Def_OAIQ250T098
-- name    : OAIQ250T098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:54:58.305182+00:00
-- url     : https://prove2.me/theorems/8f81355b-9f16-4cf1-904f-eeba19deb104
-- title:
--   Definitions bundle OAIQ250T098 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 1 definition and 27 theorems. The definitions and types are `OAI.AtomicTriangular.reciprocalGaussianPair`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean), [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_OrdinaryComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorWave115`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave115.lean), [`Triangular_Taylor_TaylorWave116`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave116.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T046`, `OAIQ250T047`, `OAIQ250T049`, `OAIQ250T051`, `OAIQ250T052`, `OAIQ250T060`, `OAIQ250T061`, `OAIQ250T077` and `OAIQ250T079` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T108`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T046
import Definitions.Def_OAIQ250T047
import Definitions.Def_OAIQ250T049
import Definitions.Def_OAIQ250T051
import Definitions.Def_OAIQ250T052
import Definitions.Def_OAIQ250T060
import Definitions.Def_OAIQ250T061
import Definitions.Def_OAIQ250T077
import Definitions.Def_OAIQ250T079

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_5_7_calc (j : Fin 31) : taylorWaveBox 1 1 5 7 j = tw1_1_5_7 j := by
  revert j
  decide +kernel
lemma tw1_1_5_8_calc (j : Fin 31) : taylorWaveBox 1 1 5 8 j = tw1_1_5_8 j := by
  revert j
  decide +kernel
lemma tw1_1_5_9_calc (j : Fin 31) : taylorWaveBox 1 1 5 9 j = tw1_1_5_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw1_1_6_1_calc (j : Fin 31) : taylorWaveBox 1 1 6 1 j = tw1_1_6_1 j := by
  revert j
  decide +kernel
lemma tw1_1_6_2_calc (j : Fin 31) : taylorWaveBox 1 1 6 2 j = tw1_1_6_2 j := by
  revert j
  decide +kernel
lemma tw1_1_6_3_calc (j : Fin 31) : taylorWaveBox 1 1 6 3 j = tw1_1_6_3 j := by
  revert j
  decide +kernel
lemma tw1_1_6_4_calc (j : Fin 31) : taylorWaveBox 1 1 6 4 j = tw1_1_6_4 j := by
  revert j
  decide +kernel
lemma tw1_1_6_5_calc (j : Fin 31) : taylorWaveBox 1 1 6 5 j = tw1_1_6_5 j := by
  revert j
  decide +kernel
lemma tw1_1_6_6_calc (j : Fin 31) : taylorWaveBox 1 1 6 6 j = tw1_1_6_6 j := by
  revert j
  decide +kernel
lemma tw1_1_6_7_calc (j : Fin 31) : taylorWaveBox 1 1 6 7 j = tw1_1_6_7 j := by
  revert j
  decide +kernel
lemma tw1_1_6_8_calc (j : Fin 31) : taylorWaveBox 1 1 6 8 j = tw1_1_6_8 j := by
  revert j
  decide +kernel
lemma tw1_1_6_9_calc (j : Fin 31) : taylorWaveBox 1 1 6 9 j = tw1_1_6_9 j := by
  revert j
  decide +kernel
lemma tw1_1_6_10_calc (j : Fin 31) : taylorWaveBox 1 1 6 10 j = tw1_1_6_10 j := by
  revert j
  decide +kernel
lemma tw1_1_6_11_calc (j : Fin 31) : taylorWaveBox 1 1 6 11 j = tw1_1_6_11 j := by
  revert j
  decide +kernel
lemma tw1_1_6_12_calc (j : Fin 31) : taylorWaveBox 1 1 6 12 j = tw1_1_6_12 j := by
  revert j
  decide +kernel
lemma tw1_1_6_13_calc (j : Fin 31) : taylorWaveBox 1 1 6 13 j = tw1_1_6_13 j := by
  revert j
  decide +kernel
lemma tw1_1_6_14_calc (j : Fin 31) : taylorWaveBox 1 1 6 14 j = tw1_1_6_14 j := by
  revert j
  decide +kernel
lemma tw1_1_6_15_calc (j : Fin 31) : taylorWaveBox 1 1 6 15 j = tw1_1_6_15 j := by
  revert j
  decide +kernel
lemma tw1_1_6_16_calc (j : Fin 31) : taylorWaveBox 1 1 6 16 j = tw1_1_6_16 j := by
  revert j
  decide +kernel
lemma tw1_1_6_17_calc (j : Fin 31) : taylorWaveBox 1 1 6 17 j = tw1_1_6_17 j := by
  revert j
  decide +kernel
lemma tw1_1_6_18_calc (j : Fin 31) : taylorWaveBox 1 1 6 18 j = tw1_1_6_18 j := by
  revert j
  decide +kernel
lemma tw1_1_6_19_calc (j : Fin 31) : taylorWaveBox 1 1 6 19 j = tw1_1_6_19 j := by
  revert j
  decide +kernel
lemma tw1_1_6_20_calc (j : Fin 31) : taylorWaveBox 1 1 6 20 j = tw1_1_6_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex1b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 8 r = ex1b8 r := by
  revert r
  decide +kernel
lemma ex1b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 9 r = ex1b9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ordinaryOffsetBox_mem (n : Fin 7) (r : Fin 8) :
    (ordinaryOffsetBox n r).Mem (ordinaryOffset n r) := by
  unfold ordinaryOffsetBox ordinaryOffset
  split_ifs
  · rw [div_eq_mul_inv]
    exact RI.mem_mul QBox1_mem (RI.mem_invPos (RI.mem_mul (RI.mem_point 2) ZBox_mem) (by decide +kernel))
  · exact RI.mem_mul (RI.mem_divNat (RI.mem_point 4) (by norm_num)) QBox1_mem
  · simpa using RI.mem_point 0

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_OrdinaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma gaussian_ordinary_lower {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    (∑ r : Fin 8,ordinaryOffset n r*actualParameter z r) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  rw [ordinaryOffset_actual]
  by_cases hn0 : n=0
  · subst n
    have hy : y=0 := by fin_cases y <;> simp_all
    subst y
    norm_num [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum]
    have hh := gaussian_deleted_left (m:=1) hz (neg_nonpos.mpr hτ.1)
    norm_num at hh
    have hd := div_le_div_of_nonneg_left Q_one_pos.le (show 0<2*z by positivity) (show 2*z ≤ 2*Z by linarith)
    exact hd.trans hh
  · have hnval : n.val≠0 := by exact fun hh => hn0 (Fin.ext hh)
    simp only [hnval,ite_false, if_false]
    by_cases hn1 : n=1
    · subst n
      simp only [Fin.val_one,ite_true, if_true]
      have hv : nearDisplacement 1 y*τ ≤ 1/2 := by
        fin_cases y <;> norm_num[nearDisplacement,nearDisplacementNum] <;> nlinarith [hτ.1,hτ.2]
      have hh := gaussian_deleted_three hz hzB hv
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      norm_num [nearNode,finiteNode,residue]
    · have hnval1 : n.val≠1 := by exact fun hh => hn1 (Fin.ext hh)
      simp only [hnval1,ite_false, if_false]
      exact gaussian_deleted_nonneg hz _ _
end AtomicTriangular.Construction
end

end OAI
end

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


