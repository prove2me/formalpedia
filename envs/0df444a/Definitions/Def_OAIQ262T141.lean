-- Prove2me | Definitions.Def_OAIQ262T141
-- name    : OAIQ262T141
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:23.880544+00:00
-- url     : https://prove2.me/theorems/835aa14a-453e-4a0c-b958-991f77b608f6
-- title:
--   Definitions bundle OAIQ262T141 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.splitL`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Construction_ConcreteSchur`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean), [`Triangular_Construction_L1Matrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/L1Matrix.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T086`, `OAIQ262T091`, `OAIQ262T093` and `OAIQ262T094` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T153`, `OAIQ262T156` and `OAIQ262T157`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T091
import Definitions.Def_OAIQ262T093
import Definitions.Def_OAIQ262T094

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
lemma phaseHTable1_calc (j : Fin 31) : wavePhaseBox 1 1 j = phaseHTable1 j := by
  revert j
  decide +kernel
lemma phaseHTable1_mem (j : Fin 31) : (phaseHTable1 j).Mem (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)) := by
  rw [← phaseHTable1_calc]
  exact wavePhaseBox_mem 1 1 j
lemma waveExp1_1_mem (j : Fin 31) : (waveExp1_1 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((1:ℤ):ℂ))) := by
  rw [← waveExp1_1_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 1)) (by
    revert j
    decide +kernel)
lemma waveExp1_12_mem (j : Fin 31) : (waveExp1_12 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((12:ℤ):ℂ))) := by
  rw [← waveExp1_12_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 12)) (by
    revert j
    decide +kernel)
lemma waveExp1_13_mem (j : Fin 31) : (waveExp1_13 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((13:ℤ):ℂ))) := by
  rw [← waveExp1_13_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 13)) (by
    revert j
    decide +kernel)
lemma waveExp1_16_mem (j : Fin 31) : (waveExp1_16 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((16:ℤ):ℂ))) := by
  rw [← waveExp1_16_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 16)) (by
    revert j
    decide +kernel)
lemma waveExp1_19_mem (j : Fin 31) : (waveExp1_19 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((19:ℤ):ℂ))) := by
  rw [← waveExp1_19_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 19)) (by
    revert j
    decide +kernel)
lemma waveExp1_21_mem (j : Fin 31) : (waveExp1_21 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((21:ℤ):ℂ))) := by
  rw [← waveExp1_21_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 21)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
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
lemma minusApproxBox_mem (i j : Fin 20) : (minusApproxBox i j).Mem (minusApprox i j) := RI.mem_singleton _
lemma plusResidualRow11_calc (j : Fin 20) : plusResidualBox 11 j = plusResidualRow11 j := by
  revert j
  decide +kernel

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
lemma l1Matrix_add (A B : Matrix m n ℝ) : l1Matrix (A+B)=l1Matrix A+l1Matrix B := by
  ext x i
  simp [l1Matrix_apply,add_mul,Finset.sum_add_distrib]
end AtomicTriangular.MatrixBounds
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ConcreteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

def splitL (e : Fin 2) : FiniteCoefficients →L[ℝ] FiniteCoefficients :=
  if e.val=0 then Lplus else Lminus
end AtomicTriangular.Construction
end

end OAI
end


