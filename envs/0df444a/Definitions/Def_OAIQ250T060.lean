-- Prove2me | Definitions.Def_OAIQ250T060
-- name    : OAIQ250T060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:17:46.375567+00:00
-- url     : https://prove2.me/theorems/444cd8b5-1d86-4f13-b177-8b8fbcf1ef52
-- title:
--   Definitions bundle OAIQ250T060 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 1 definition and 8 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_2_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_GaussianDeleted`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/GaussianDeleted.lean), [`Triangular_Signs_Signs02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs02.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorExp11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp11.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T005`, `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T026`, `OAIQ250T028` and `OAIQ250T029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T098`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T005
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T028
import Definitions.Def_OAIQ250T029

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp1_1_3_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 3)).exp = taylorExp1_1_3 j := by
  revert j
  decide +kernel
lemma taylorExp1_1_4_calc (j : Fin 31) : ((taylorPhase1_1 j).mul (CI.point 4)).exp = taylorExp1_1_4 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex3b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex3r 9 r = ex3b9 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_GaussianDeleted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
lemma gaussian_deleted_left {z m v : ℝ} (hz : 0<z) (hv : v ≤ 0) :
    Q 1*Real.exp ((1-m)/z)/(2*z) ≤ deletedSecond (gaussianG z) m (m+v) := by
  apply deletedSecond_lower ((gaussianG_contDiff z).of_le (by norm_num))
  intro t ht
  have htm : t ≤ m := by
    have hh := ht.2
    rw [max_eq_left (by linarith : m+v ≤ m)] at hh
    exact hh
  rw [gaussianG_second hz]
  have he : Real.exp ((1-m)/z) ≤ Real.exp ((1-t)/z) := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hz.le)
  have hh := mul_le_mul_of_nonneg_left he (div_nonneg Q_one_pos.le hz.le)
  convert div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 2) using 1 <;> first | rfl | ring

lemma gaussian_deleted_formula {z m v : ℝ} (hz : 0<z) (hv : v≠0) :
    deletedSecond (gaussianG z) m (m+v)=
      Q 1*z*Real.exp ((1-m)/z)*(Real.exp (-v/z)-1+v/z)/v^2 := by
  rw [deletedSecond,ite_eq_right (by intro hh; apply hv; linarith : m+v≠m),(gaussianG_deriv hz m).deriv]
  simp only [gaussianG]
  rw [show (1-(m+v))/z=(1-m)/z+(-v/z) by ring,Real.exp_add]
  field_simp [hz.ne',hv]
  ring
lemma gaussian_deleted_right {z m v : ℝ} (hz : 0<z) (hv : 0 ≤ v) :
    Q 1*Real.exp ((1-m)/z)*((3*z+v)/(6*z^2+4*z*v+v^2)) ≤
      deletedSecond (gaussianG z) m (m+v) := by
  rcases hv.eq_or_lt with hv|hv
  · subst v
    simp only [add_zero,deletedSecond,ite_true, if_true]
    rw [gaussianG_second hz]
    apply le_of_eq
    field_simp [hz.ne']
    ring
  · rw [gaussian_deleted_formula hz hv.ne']
    have hQ := Q_one_pos
    have hh := mul_le_mul_of_nonneg_left (pade_rational (div_pos hv hz))
      (show 0 ≤ Q 1*Real.exp ((1-m)/z)/z by positivity)
    have hz0 := hz.ne'
    have hv0 := hv.ne'
    have hd : 6*z^2+4*z*v+v^2≠0 := ne_of_gt (by positivity)
    convert hh using 1 <;> first | rfl | field_simp [hz0,hv0,hd]
lemma gaussian_deleted_three {z v : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hv : v ≤ 1/2) :
    (4/5)*Q 1*Real.exp (-2/z) ≤ deletedSecond (gaussianG z) 3 (3+v) := by
  have hzBound : z ≤ 391/1000 := hzB
  have hq : 0 ≤ Q 1*Real.exp (-2/z) := mul_nonneg Q_one_pos.le (Real.exp_pos _).le
  by_cases hv0 : v ≤ 0
  · have hh := gaussian_deleted_left (m:=3) hz hv0
    norm_num at hh
    have hr : (4/5:ℝ) ≤ 1/(2*z) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hl := mul_le_mul_of_nonneg_left hr hq
    have he : Q 1*Real.exp (-2/z)*(1/(2*z))=Q 1*Real.exp (-2/z)/(2*z) := by ring
    rw [he] at hl
    convert hl.trans hh using 1 <;> first | rfl | ring
  · have hv0 : 0<v := lt_of_not_ge hv0
    have hd : 0<6*z^2+4*z*v+v^2 := by positivity
    have hz2 : z^2 ≤ (391/1000)*z := by nlinarith
    have hv2 : v^2 ≤ (1/2)*v := by nlinarith
    have hzv : z*v ≤ (1/2)*z := by nlinarith
    have hzv' : z*v ≤ (391/1000)*v := by nlinarith
    have hr : (4/5:ℝ) ≤ (3*z+v)/(6*z^2+4*z*v+v^2) := by
      rw [le_div_iff₀ hd]
      nlinarith
    have hh := gaussian_deleted_right (m:=3) hz hv0.le
    norm_num at hh
    convert (mul_le_mul_of_nonneg_left hr hq).trans hh using 1 <;> first | rfl | ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_2_0 : Fin 21 → Fin 8 → RI := ![bs0_2_0_0,bs0_2_0_1,bs0_2_0_2,bs0_2_0_3,bs0_2_0_4,bs0_2_0_5,bs0_2_0_6,bs0_2_0_7,bs0_2_0_8,bs0_2_0_9,bs0_2_0_10,bs0_2_0_11,bs0_2_0_12,bs0_2_0_13,bs0_2_0_14,bs0_2_0_15,bs0_2_0_16,bs0_2_0_17,bs0_2_0_18,bs0_2_0_19,bs0_2_0_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors08 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


