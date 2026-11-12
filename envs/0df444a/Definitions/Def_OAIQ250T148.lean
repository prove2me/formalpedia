-- Prove2me | Definitions.Def_OAIQ250T148
-- name    : OAIQ250T148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:55:41.265039+00:00
-- url     : https://prove2.me/theorems/af4a0e1d-b1ff-4ee2-9154-8cbed7f9d63f
-- title:
--   Definitions bundle OAIQ250T148 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_MatrixInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/MatrixInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Construction_L1Matrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/L1Matrix.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T005`, `OAIQ250T007` and `OAIQ250T009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T101` and `OAIQ250T151`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T005
import Definitions.Def_OAIQ250T007
import Definitions.Def_OAIQ250T009

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_MatrixInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval
open Matrix AtomicTriangular.MatrixBounds

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
omit [Fintype m] [Fintype p] in
lemma matrixMul_mem {a : m → n → RI} {b : n → p → RI}
    {A : Matrix m n ℝ} {B : Matrix n p ℝ} (ha : ∀ i j, (a i j).Mem (A i j))
    (hb : ∀ i j, (b i j).Mem (B i j)) (i : m) (j : p) :
    (matrixMul a b i j).Mem ((A*B) i j) :=
  RI.mem_sum (fun k => RI.mem_mul (ha i k) (hb k j))
end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma waveExp1_3_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 3)).exp = waveExp1_3 j := by
  revert j
  decide +kernel
lemma waveExp1_4_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 4)).exp = waveExp1_4 j := by
  revert j
  decide +kernel
lemma waveExp1_7_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 7)).exp = waveExp1_7 j := by
  revert j
  decide +kernel
lemma waveExp1_9_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 9)).exp = waveExp1_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.MatrixBounds
open L1Kernel
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Nonempty m] [Nonempty n] [Nonempty p]
omit [Nonempty m] in
lemma l1Matrix_apply (A : Matrix m n ℝ) (x : ℓ¹(n,ℝ)) (i : m) :
    l1Matrix A x i = ∑ j, A i j*x j := by
  have hh := operator_apply A (fun j => (hasSum_fintype _).summable) (matNorm A)
    (fun j => by simpa [tsum_fintype,colNorm] using colNorm_le_matNorm A j) x i
  simpa only [l1Matrix,tsum_fintype,mul_comm] using hh
omit [Nonempty m] in
lemma l1Matrix_mul (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    l1Matrix (A*B) = (l1Matrix A).comp (l1Matrix B) := by
  ext x i
  simp only [l1Matrix_apply,ContinuousLinearMap.comp_apply,Matrix.mul_apply,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma l1Matrix_one [DecidableEq n] : l1Matrix (1:Matrix n n ℝ) = 1 := by
  ext x i
  simp [l1Matrix_apply,Matrix.one_apply]
omit [Nonempty m] in
lemma l1Matrix_add (A B : Matrix m n ℝ) : l1Matrix (A+B)=l1Matrix A+l1Matrix B := by
  ext x i
  simp [l1Matrix_apply,add_mul,Finset.sum_add_distrib]
end AtomicTriangular.MatrixBounds
end

end OAI
end


