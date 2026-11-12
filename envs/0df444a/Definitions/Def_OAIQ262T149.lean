-- Prove2me | Definitions.Def_OAIQ262T149
-- name    : OAIQ262T149
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:33:56.140201+00:00
-- url     : https://prove2.me/theorems/aaac0643-c54b-4e51-8fb5-7297c2c73f25
-- title:
--   Definitions bundle OAIQ262T149 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 97 declarations of OpenAI's Lean: 97 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_Normalization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean), [`Triangular_Signs_Exceptional`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Exceptional.lean), [`Triangular_Signs_ExceptionalComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalComparison.lean), [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_ExceptionalSign3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign3.lean), [`Triangular_Signs_GaussianDeleted`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/GaussianDeleted.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T086`, `OAIQ262T092`, `OAIQ262T094`, `OAIQ262T097`, `OAIQ262T100`, `OAIQ262T104`, `OAIQ262T108` and `OAIQ262T113` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T166` and `OAIQ262T180`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T092
import Definitions.Def_OAIQ262T094
import Definitions.Def_OAIQ262T097
import Definitions.Def_OAIQ262T100
import Definitions.Def_OAIQ262T104
import Definitions.Def_OAIQ262T108
import Definitions.Def_OAIQ262T113

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Exceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma frozenTaylorRow_eval (z : ℝ) (l : ℕ) (e : Fin 8 → ℝ) (he : e 1=1) :
    (∑ r : Fin 8, frozenTaylorRow z l r*e r) =
      -∑ r : Fin 8, taylorRow 0 1 1 l r*freezeParameter z e r := by
  simp only [frozenTaylorRow,freezeParameter,Fin.sum_univ_succ,Fin.val_zero,
    ite_true, if_true,Fin.val_succ,Fin.succ_zero_eq_one]
  norm_num
  rw [he]
  ring

lemma frozenTaylor_eq (z : ℝ) (e : Fin 8 → ℝ) (he : e 1=1) (τ : ℝ) :
    frozenTaylor z e τ = -finiteTaylor 0 1 1 (freezeParameter z e) τ := by
  simp_rw [frozenTaylor,frozenTaylorRow_eval z _ e he,neg_mul,Finset.sum_neg_distrib]
  rw [finiteTaylor,←Fin.sum_univ_eq_sum_range]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex1r1_calc (r : Fin 8) : exceptionalRowBox 1 1 r = ex1r1 r := by
  revert r
  decide +kernel
lemma ex1r2_calc (r : Fin 8) : exceptionalRowBox 1 2 r = ex1r2 r := by
  revert r
  decide +kernel
lemma ex1r3_calc (r : Fin 8) : exceptionalRowBox 1 3 r = ex1r3 r := by
  revert r
  decide +kernel
lemma ex1r4_calc (r : Fin 8) : exceptionalRowBox 1 4 r = ex1r4 r := by
  revert r
  decide +kernel
lemma ex1r5_calc (r : Fin 8) : exceptionalRowBox 1 5 r = ex1r5 r := by
  revert r
  decide +kernel
lemma ex1r6_calc (r : Fin 8) : exceptionalRowBox 1 6 r = ex1r6 r := by
  revert r
  decide +kernel
lemma ex1r7_calc (r : Fin 8) : exceptionalRowBox 1 7 r = ex1r7 r := by
  revert r
  decide +kernel
lemma ex1r8_calc (r : Fin 8) : exceptionalRowBox 1 8 r = ex1r8 r := by
  revert r
  decide +kernel
lemma ex1r9_calc (r : Fin 8) : exceptionalRowBox 1 9 r = ex1r9 r := by
  revert r
  decide +kernel
lemma ex1r10_calc (r : Fin 8) : exceptionalRowBox 1 10 r = ex1r10 r := by
  revert r
  decide +kernel
lemma ex1r11_calc (r : Fin 8) : exceptionalRowBox 1 11 r = ex1r11 r := by
  revert r
  decide +kernel
lemma ex1r12_calc (r : Fin 8) : exceptionalRowBox 1 12 r = ex1r12 r := by
  revert r
  decide +kernel
lemma ex1r13_calc (r : Fin 8) : exceptionalRowBox 1 13 r = ex1r13 r := by
  revert r
  decide +kernel
lemma ex1r14_calc (r : Fin 8) : exceptionalRowBox 1 14 r = ex1r14 r := by
  revert r
  decide +kernel
lemma ex1r15_calc (r : Fin 8) : exceptionalRowBox 1 15 r = ex1r15 r := by
  revert r
  decide +kernel
lemma ex1r16_calc (r : Fin 8) : exceptionalRowBox 1 16 r = ex1r16 r := by
  revert r
  decide +kernel
lemma ex1r17_calc (r : Fin 8) : exceptionalRowBox 1 17 r = ex1r17 r := by
  revert r
  decide +kernel
lemma ex1r18_calc (r : Fin 8) : exceptionalRowBox 1 18 r = ex1r18 r := by
  revert r
  decide +kernel
lemma ex1r19_calc (r : Fin 8) : exceptionalRowBox 1 19 r = ex1r19 r := by
  revert r
  decide +kernel
lemma ex1r20_calc (r : Fin 8) : exceptionalRowBox 1 20 r = ex1r20 r := by
  revert r
  decide +kernel
lemma ex1r21_calc (r : Fin 8) : exceptionalRowBox 1 21 r = ex1r21 r := by
  revert r
  decide +kernel
lemma ex1r22_calc (r : Fin 8) : exceptionalRowBox 1 22 r = ex1r22 r := by
  revert r
  decide +kernel
lemma ex1b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 1 r = ex1b1 r := by
  revert r
  decide +kernel
lemma ex1b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 2 r = ex1b2 r := by
  revert r
  decide +kernel
lemma ex1b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 3 r = ex1b3 r := by
  revert r
  decide +kernel
lemma ex1b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 4 r = ex1b4 r := by
  revert r
  decide +kernel
lemma ex1b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 5 r = ex1b5 r := by
  revert r
  decide +kernel
lemma ex1b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 6 r = ex1b6 r := by
  revert r
  decide +kernel
lemma ex1b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 7 r = ex1b7 r := by
  revert r
  decide +kernel
lemma ex1b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 8 r = ex1b8 r := by
  revert r
  decide +kernel
lemma ex1b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 9 r = ex1b9 r := by
  revert r
  decide +kernel
lemma ex1b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 12 r = ex1b12 r := by
  revert r
  decide +kernel
lemma ex1b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 13 r = ex1b13 r := by
  revert r
  decide +kernel
lemma ex1b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 14 r = ex1b14 r := by
  revert r
  decide +kernel
lemma ex1b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 15 r = ex1b15 r := by
  revert r
  decide +kernel
lemma ex1b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 16 r = ex1b16 r := by
  revert r
  decide +kernel
lemma ex1b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 17 r = ex1b17 r := by
  revert r
  decide +kernel
lemma ex1b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 18 r = ex1b18 r := by
  revert r
  decide +kernel
lemma ex1b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 19 r = ex1b19 r := by
  revert r
  decide +kernel
lemma ex1b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 20 r = ex1b20 r := by
  revert r
  decide +kernel
lemma ex1b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 21 r = ex1b21 r := by
  revert r
  decide +kernel
lemma ex1b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex1r 22 r = ex1b22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex2r0_calc (r : Fin 8) : exceptionalRowBox 2 0 r = ex2r0 r := by
  revert r
  decide +kernel
lemma ex2r1_calc (r : Fin 8) : exceptionalRowBox 2 1 r = ex2r1 r := by
  revert r
  decide +kernel
lemma ex2r2_calc (r : Fin 8) : exceptionalRowBox 2 2 r = ex2r2 r := by
  revert r
  decide +kernel
lemma ex2r3_calc (r : Fin 8) : exceptionalRowBox 2 3 r = ex2r3 r := by
  revert r
  decide +kernel
lemma ex2r4_calc (r : Fin 8) : exceptionalRowBox 2 4 r = ex2r4 r := by
  revert r
  decide +kernel
lemma ex2r5_calc (r : Fin 8) : exceptionalRowBox 2 5 r = ex2r5 r := by
  revert r
  decide +kernel
lemma ex2r6_calc (r : Fin 8) : exceptionalRowBox 2 6 r = ex2r6 r := by
  revert r
  decide +kernel
lemma ex2r7_calc (r : Fin 8) : exceptionalRowBox 2 7 r = ex2r7 r := by
  revert r
  decide +kernel
lemma ex2r8_calc (r : Fin 8) : exceptionalRowBox 2 8 r = ex2r8 r := by
  revert r
  decide +kernel
lemma ex2r9_calc (r : Fin 8) : exceptionalRowBox 2 9 r = ex2r9 r := by
  revert r
  decide +kernel
lemma ex2r10_calc (r : Fin 8) : exceptionalRowBox 2 10 r = ex2r10 r := by
  revert r
  decide +kernel
lemma ex2r11_calc (r : Fin 8) : exceptionalRowBox 2 11 r = ex2r11 r := by
  revert r
  decide +kernel
lemma ex2r12_calc (r : Fin 8) : exceptionalRowBox 2 12 r = ex2r12 r := by
  revert r
  decide +kernel
lemma ex2r13_calc (r : Fin 8) : exceptionalRowBox 2 13 r = ex2r13 r := by
  revert r
  decide +kernel
lemma ex2r14_calc (r : Fin 8) : exceptionalRowBox 2 14 r = ex2r14 r := by
  revert r
  decide +kernel
lemma ex2r15_calc (r : Fin 8) : exceptionalRowBox 2 15 r = ex2r15 r := by
  revert r
  decide +kernel
lemma ex2r16_calc (r : Fin 8) : exceptionalRowBox 2 16 r = ex2r16 r := by
  revert r
  decide +kernel
lemma ex2r17_calc (r : Fin 8) : exceptionalRowBox 2 17 r = ex2r17 r := by
  revert r
  decide +kernel
lemma ex2r18_calc (r : Fin 8) : exceptionalRowBox 2 18 r = ex2r18 r := by
  revert r
  decide +kernel
lemma ex2r19_calc (r : Fin 8) : exceptionalRowBox 2 19 r = ex2r19 r := by
  revert r
  decide +kernel
lemma ex2r20_calc (r : Fin 8) : exceptionalRowBox 2 20 r = ex2r20 r := by
  revert r
  decide +kernel
lemma ex2r21_calc (r : Fin 8) : exceptionalRowBox 2 21 r = ex2r21 r := by
  revert r
  decide +kernel
lemma ex2r22_calc (r : Fin 8) : exceptionalRowBox 2 22 r = ex2r22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex3r0_calc (r : Fin 8) : exceptionalRowBox 3 0 r = ex3r0 r := by
  revert r
  decide +kernel
lemma ex3r1_calc (r : Fin 8) : exceptionalRowBox 3 1 r = ex3r1 r := by
  revert r
  decide +kernel
lemma ex3r2_calc (r : Fin 8) : exceptionalRowBox 3 2 r = ex3r2 r := by
  revert r
  decide +kernel
lemma ex3r3_calc (r : Fin 8) : exceptionalRowBox 3 3 r = ex3r3 r := by
  revert r
  decide +kernel
lemma ex3r4_calc (r : Fin 8) : exceptionalRowBox 3 4 r = ex3r4 r := by
  revert r
  decide +kernel
lemma ex3r5_calc (r : Fin 8) : exceptionalRowBox 3 5 r = ex3r5 r := by
  revert r
  decide +kernel
lemma ex3r6_calc (r : Fin 8) : exceptionalRowBox 3 6 r = ex3r6 r := by
  revert r
  decide +kernel
lemma ex3r7_calc (r : Fin 8) : exceptionalRowBox 3 7 r = ex3r7 r := by
  revert r
  decide +kernel
lemma ex3r8_calc (r : Fin 8) : exceptionalRowBox 3 8 r = ex3r8 r := by
  revert r
  decide +kernel
lemma ex3r9_calc (r : Fin 8) : exceptionalRowBox 3 9 r = ex3r9 r := by
  revert r
  decide +kernel
lemma ex3r10_calc (r : Fin 8) : exceptionalRowBox 3 10 r = ex3r10 r := by
  revert r
  decide +kernel
lemma ex3r11_calc (r : Fin 8) : exceptionalRowBox 3 11 r = ex3r11 r := by
  revert r
  decide +kernel
lemma ex3r12_calc (r : Fin 8) : exceptionalRowBox 3 12 r = ex3r12 r := by
  revert r
  decide +kernel
lemma ex3r13_calc (r : Fin 8) : exceptionalRowBox 3 13 r = ex3r13 r := by
  revert r
  decide +kernel
lemma ex3r14_calc (r : Fin 8) : exceptionalRowBox 3 14 r = ex3r14 r := by
  revert r
  decide +kernel
lemma ex3r15_calc (r : Fin 8) : exceptionalRowBox 3 15 r = ex3r15 r := by
  revert r
  decide +kernel
lemma ex3r16_calc (r : Fin 8) : exceptionalRowBox 3 16 r = ex3r16 r := by
  revert r
  decide +kernel
lemma ex3r17_calc (r : Fin 8) : exceptionalRowBox 3 17 r = ex3r17 r := by
  revert r
  decide +kernel
lemma ex3r18_calc (r : Fin 8) : exceptionalRowBox 3 18 r = ex3r18 r := by
  revert r
  decide +kernel
lemma ex3r19_calc (r : Fin 8) : exceptionalRowBox 3 19 r = ex3r19 r := by
  revert r
  decide +kernel
lemma ex3r20_calc (r : Fin 8) : exceptionalRowBox 3 20 r = ex3r20 r := by
  revert r
  decide +kernel
lemma ex3r21_calc (r : Fin 8) : exceptionalRowBox 3 21 r = ex3r21 r := by
  revert r
  decide +kernel
lemma ex3r22_calc (r : Fin 8) : exceptionalRowBox 3 22 r = ex3r22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalComparison
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
lemma frozenTaylor_affine (z : ℝ) (e : Fin 8 → ℝ) (v : ℝ) :
    frozenTaylor z e v=(1-z/Z)*frozenTaylor 0 e v+(z/Z)*frozenTaylor Z e v := by
  unfold frozenTaylor
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [←mul_assoc,Finset.mul_sum]
  rw [←add_mul,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  unfold frozenTaylorRow
  split_ifs <;> (try omega) <;> norm_num [Z] <;> ring
lemma frozenTaylor_actual (e : Fin 8 → ℝ) (he : e 1=1) (v : ℝ) :
    frozenTaylor (e 0) e v= -finiteTaylor 0 1 1 e v := by
  have heq : freezeParameter (e 0) e=e := by
    ext r
    unfold freezeParameter
    split_ifs with hr
    · rw [show r=0 from Fin.ext hr]
    · rfl
  rw [frozenTaylor_eq _ _ he,heq]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_GaussianDeleted
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_SignBase
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

lemma normalizingDen_pos {z : ℝ} (hz : 0<z) : 0<normalizingDen z := by
  exact mul_pos (mul_pos Q_one_pos hz) (Real.exp_pos _)
end AtomicTriangular.Construction
end

end OAI
end


