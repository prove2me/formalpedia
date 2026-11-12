-- Prove2me | Definitions.Def_OAIQ262T254
-- name    : OAIQ262T254
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T21:05:37.944287+00:00
-- url     : https://prove2.me/theorems/8e97fb5c-b111-4cd6-b91e-c3bbd3fdcc06
-- title:
--   Definitions bundle OAIQ262T254 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Construction_FiniteSystem`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FiniteSystem.lean), [`Triangular_Construction_TailInterpolation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/TailInterpolation.lean), [`Triangular_Taylor_TaylorExp00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp00.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T193` and `OAIQ262T194` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T259`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T193
import Definitions.Def_OAIQ262T194

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Matrix

lemma finiteSolution_equations :
    finiteSolution 0 = R*finiteSolution 1+R0*gamma 1+Yf ∧
    finiteSolution 1 = R*finiteSolution 0+R0*gamma 0 := by
  have hp := Uplus_equation
  have hm := Uminus_equation
  simp only [Matrix.sub_mul,Matrix.add_mul,Matrix.one_mul,Matrix.mul_add,Matrix.mul_sub] at hp hm
  constructor
  · simp only [finiteSolution,Fin.val_zero,Fin.val_one,one_ne_zero,ite_true, if_true,ite_false, if_false,
      Matrix.mul_smul,Matrix.mul_sub]
    ext i j
    have hpij := congrFun (congrFun hp i) j
    have hmij := congrFun (congrFun hm i) j
    simp only [Matrix.add_apply,Matrix.sub_apply] at hpij hmij
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    linarith
  · simp only [finiteSolution,Fin.val_zero,Fin.val_one,one_ne_zero,ite_true, if_true,ite_false, if_false,
      Matrix.mul_smul,Matrix.mul_add]
    ext i j
    have hpij := congrFun (congrFun hp i) j
    have hmij := congrFun (congrFun hm i) j
    simp only [Matrix.add_apply,Matrix.sub_apply] at hpij hmij
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
lemma inputJJet_tail_transformed (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (p : TailNode × Fin 2) :
    (negativeJet h p.1.val.val p.2 (inputJJet (coefficientInput C a w) 1 0 p.1.val.val)
      (inputJJet (coefficientInput C a w) 1 1 p.1.val.val)).re=
      Doperator w p+CallOperator a p+C*tailFixedColumn 22 p := by
  rw [inputJJet_negative_coefficient]
  have hd : Doperator w p=∑' q : TailNode × Fin 2,w q*tailJet h h p.1.val.val q.1.val.val q.2 p.2 := by
    unfold Doperator
    erw [operator_apply]
    rfl
  have hc : CallOperator a p=∑ c : Fin 22,a c*jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩) := by
    unfold CallOperator
    erw [operator_apply,tsum_fintype]
    rfl
  rw [hd,hc,tailFixedColumn_apply]
  simp only [show (22:Fin 23).val=22 from rfl,↓reduceIte]
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorExp00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExp0_0_1_mem (j : Fin 31) : (taylorExp0_0_1 j).Mem (exp (taylorPhase 0 0 (frequency j)*((1:ℤ):ℂ))) := by
  rw [← taylorExp0_0_1_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 1)) (by
    revert j
    decide +kernel)
lemma taylorExp0_0_3_mem (j : Fin 31) : (taylorExp0_0_3 j).Mem (exp (taylorPhase 0 0 (frequency j)*((3:ℤ):ℂ))) := by
  rw [← taylorExp0_0_3_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 3)) (by
    revert j
    decide +kernel)
lemma taylorExp0_0_4_mem (j : Fin 31) : (taylorExp0_0_4 j).Mem (exp (taylorPhase 0 0 (frequency j)*((4:ℤ):ℂ))) := by
  rw [← taylorExp0_0_4_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 4)) (by
    revert j
    decide +kernel)
lemma taylorExp0_0_7_mem (j : Fin 31) : (taylorExp0_0_7 j).Mem (exp (taylorPhase 0 0 (frequency j)*((7:ℤ):ℂ))) := by
  rw [← taylorExp0_0_7_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 7)) (by
    revert j
    decide +kernel)
lemma taylorExp0_0_12_mem (j : Fin 31) : (taylorExp0_0_12 j).Mem (exp (taylorPhase 0 0 (frequency j)*((12:ℤ):ℂ))) := by
  rw [← taylorExp0_0_12_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 12)) (by
    revert j
    decide +kernel)
lemma taylorExp0_0_13_mem (j : Fin 31) : (taylorExp0_0_13 j).Mem (exp (taylorPhase 0 0 (frequency j)*((13:ℤ):ℂ))) := by
  rw [← taylorExp0_0_13_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 13)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end


