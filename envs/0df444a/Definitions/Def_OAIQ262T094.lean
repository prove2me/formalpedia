-- Prove2me | Definitions.Def_OAIQ262T094
-- name    : OAIQ262T094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:51:59.538705+00:00
-- url     : https://prove2.me/theorems/3b8c833a-34b2-43da-9c1b-e74fdf0a5e9b
-- title:
--   Definitions bundle OAIQ262T094 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.minusResidualTable`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_MatrixInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/MatrixInterval.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Envelope_TargetEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/TargetEnvelope.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T008`, `OAIQ262T010`, `OAIQ262T011` and `OAIQ262T012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T141`, `OAIQ262T142`, `OAIQ262T143`, `OAIQ262T146` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T008
import Definitions.Def_OAIQ262T010
import Definitions.Def_OAIQ262T011
import Definitions.Def_OAIQ262T012

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma waveExp1_1_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 1)).exp = waveExp1_1 j := by
  revert j
  decide +kernel
lemma waveExp1_3_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 3)).exp = waveExp1_3 j := by
  revert j
  decide +kernel
lemma waveExp1_4_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 4)).exp = waveExp1_4 j := by
  revert j
  decide +kernel
lemma waveExp1_7_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 7)).exp = waveExp1_7 j := by
  revert j
  decide +kernel
lemma waveExp1_16_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 16)).exp = waveExp1_16 j := by
  revert j
  decide +kernel
lemma waveExp1_19_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 19)).exp = waveExp1_19 j := by
  revert j
  decide +kernel
lemma waveExp1_21_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 21)).exp = waveExp1_21 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_MatrixInterval
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
omit [Fintype n] in
lemma matrixOne_mem [DecidableEq n] (i j : n) : (matrixOne i j).Mem ((1:Matrix n n ℝ) i j) := by
  simpa only [matrixOne,Matrix.one_apply,Int.cast_ite,Int.cast_zero,Int.cast_one] using
    RI.mem_point (if i=j then 1 else 0)

end AtomicTriangular.Interval
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
def minusResidualTable : Fin 20 → Fin 20 → RI := ![minusResidualRow0,minusResidualRow1,minusResidualRow2,minusResidualRow3,minusResidualRow4,minusResidualRow5,minusResidualRow6,minusResidualRow7,minusResidualRow8,minusResidualRow9,minusResidualRow10,minusResidualRow11,minusResidualRow12,minusResidualRow13,minusResidualRow14,minusResidualRow15,minusResidualRow16,minusResidualRow17,minusResidualRow18,minusResidualRow19]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_TargetEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate AtomicTriangular.L1Kernel

lemma Q_one_pos : 0<Q 1 := by linarith [Q_1_bounds.1]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma targetZBox_mem : targetZBox.Mem Z := by
  simpa [Z,targetZBox] using RI.mem_divNat (RI.mem_point 391) (by norm_num : 0<1000)
end AtomicTriangular.FiniteCertificate
end

end OAI
end


