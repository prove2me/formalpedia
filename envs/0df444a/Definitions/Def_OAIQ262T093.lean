-- Prove2me | Definitions.Def_OAIQ262T093
-- name    : OAIQ262T093
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:51:38.952397+00:00
-- url     : https://prove2.me/theorems/f8ed8ec6-77ea-404e-aba3-114fc8b7571e
-- title:
--   Definitions bundle OAIQ262T093 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.A2Table`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamA`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamA.lean), [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Construction_L1Matrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/L1Matrix.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T007`, `OAIQ262T008`, `OAIQ262T010`, `OAIQ262T011` and `OAIQ262T012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T141`, `OAIQ262T142` and `OAIQ262T143`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T007
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
lemma waveExp0_3_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 3)).exp = waveExp0_3 j := by
  revert j
  decide +kernel
lemma waveExp0_4_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 4)).exp = waveExp0_4 j := by
  revert j
  decide +kernel
lemma waveExp0_7_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 7)).exp = waveExp0_7 j := by
  revert j
  decide +kernel
lemma waveExp0_9_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 9)).exp = waveExp0_9 j := by
  revert j
  decide +kernel
lemma waveExp0_21_calc (j : Fin 31) : ((phaseHTable0 j).mul (CI.point 21)).exp = waveExp0_21 j := by
  revert j
  decide +kernel
lemma waveExp1_12_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 12)).exp = waveExp1_12 j := by
  revert j
  decide +kernel
lemma waveExp1_13_calc (j : Fin 31) : ((phaseHTable1 j).mul (CI.point 13)).exp = waveExp1_13 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma etaPiBox_mem : etaPiBox.Mem (Real.pi*eta) := by
  apply RI.mem_mul piBox_mem
  simpa [eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<(5:ℕ))

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def A2Table : Fin 23 → Fin 8 → RI := ![A2TableRow0,A2TableRow1,A2TableRow2,A2TableRow3,A2TableRow4,A2TableRow5,A2TableRow6,A2TableRow7,A2TableRow8,A2TableRow9,A2TableRow10,A2TableRow11,A2TableRow12,A2TableRow13,A2TableRow14,A2TableRow15,A2TableRow16,A2TableRow17,A2TableRow18,A2TableRow19,A2TableRow20,A2TableRow21,A2TableRow22]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_L1Matrix
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
lemma l1Matrix_one [DecidableEq n] : l1Matrix (1:Matrix n n ℝ) = 1 := by
  ext x i
  simp [l1Matrix_apply,Matrix.one_apply]
end AtomicTriangular.MatrixBounds
end

end OAI
end


