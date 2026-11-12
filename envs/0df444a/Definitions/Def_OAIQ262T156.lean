-- Prove2me | Definitions.Def_OAIQ262T156
-- name    : OAIQ262T156
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:34:20.772197+00:00
-- url     : https://prove2.me/theorems/7581d3a9-c636-4d37-ab22-9a2aa38a81c5
-- title:
--   Definitions bundle OAIQ262T156 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 1 definition and 28 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.minusResidualBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T095`, `OAIQ262T137`, `OAIQ262T140` and `OAIQ262T141` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T193`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T095
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T140
import Definitions.Def_OAIQ262T141

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
lemma waveExp1_3_mem (j : Fin 31) : (waveExp1_3 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((3:ℤ):ℂ))) := by
  rw [← waveExp1_3_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 3)) (by
    revert j
    decide +kernel)
lemma waveExp1_4_mem (j : Fin 31) : (waveExp1_4 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((4:ℤ):ℂ))) := by
  rw [← waveExp1_4_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 4)) (by
    revert j
    decide +kernel)
lemma waveExp1_7_mem (j : Fin 31) : (waveExp1_7 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((7:ℤ):ℂ))) := by
  rw [← waveExp1_7_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 7)) (by
    revert j
    decide +kernel)
lemma waveExp1_9_mem (j : Fin 31) : (waveExp1_9 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((9:ℤ):ℂ))) := by
  rw [← waveExp1_9_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 9)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveJetsData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma jetTable0_7_calc (j : Fin 31) : jetMultiplierBox 0 7 j = jetTable0_7 j := by
  revert j
  decide +kernel
lemma jetTable0_8_calc (j : Fin 31) : jetMultiplierBox 0 8 j = jetTable0_8 j := by
  revert j
  decide +kernel
lemma jetTable0_9_calc (j : Fin 31) : jetMultiplierBox 0 9 j = jetTable0_9 j := by
  revert j
  decide +kernel
lemma jetTable1_0_calc (j : Fin 31) : jetMultiplierBox 1 0 j = jetTable1_0 j := by
  revert j
  decide +kernel
lemma jetTable1_1_calc (j : Fin 31) : jetMultiplierBox 1 1 j = jetTable1_1 j := by
  revert j
  decide +kernel
lemma jetTable1_2_calc (j : Fin 31) : jetMultiplierBox 1 2 j = jetTable1_2 j := by
  revert j
  decide +kernel
lemma jetTable1_3_calc (j : Fin 31) : jetMultiplierBox 1 3 j = jetTable1_3 j := by
  revert j
  decide +kernel
lemma jetTable1_4_calc (j : Fin 31) : jetMultiplierBox 1 4 j = jetTable1_4 j := by
  revert j
  decide +kernel
lemma jetTable1_5_calc (j : Fin 31) : jetMultiplierBox 1 5 j = jetTable1_5 j := by
  revert j
  decide +kernel
lemma jetTable1_6_calc (j : Fin 31) : jetMultiplierBox 1 6 j = jetTable1_6 j := by
  revert j
  decide +kernel
lemma jetTable1_7_calc (j : Fin 31) : jetMultiplierBox 1 7 j = jetTable1_7 j := by
  revert j
  decide +kernel
lemma jetTable1_8_calc (j : Fin 31) : jetMultiplierBox 1 8 j = jetTable1_8 j := by
  revert j
  decide +kernel
lemma jetTable1_9_calc (j : Fin 31) : jetMultiplierBox 1 9 j = jetTable1_9 j := by
  revert j
  decide +kernel
lemma jetTable1_10_calc (j : Fin 31) : jetMultiplierBox 1 10 j = jetTable1_10 j := by
  revert j
  decide +kernel
lemma jetTable1_11_calc (j : Fin 31) : jetMultiplierBox 1 11 j = jetTable1_11 j := by
  revert j
  decide +kernel
lemma jetTable1_12_calc (j : Fin 31) : jetMultiplierBox 1 12 j = jetTable1_12 j := by
  revert j
  decide +kernel
lemma jetTable1_13_calc (j : Fin 31) : jetMultiplierBox 1 13 j = jetTable1_13 j := by
  revert j
  decide +kernel
lemma jetTable1_14_calc (j : Fin 31) : jetMultiplierBox 1 14 j = jetTable1_14 j := by
  revert j
  decide +kernel
lemma jetTable1_15_calc (j : Fin 31) : jetMultiplierBox 1 15 j = jetTable1_15 j := by
  revert j
  decide +kernel
lemma jetTable1_16_calc (j : Fin 31) : jetMultiplierBox 1 16 j = jetTable1_16 j := by
  revert j
  decide +kernel
lemma jetTable1_17_calc (j : Fin 31) : jetMultiplierBox 1 17 j = jetTable1_17 j := by
  revert j
  decide +kernel
lemma jetTable1_18_calc (j : Fin 31) : jetMultiplierBox 1 18 j = jetTable1_18 j := by
  revert j
  decide +kernel
lemma jetTable1_19_calc (j : Fin 31) : jetMultiplierBox 1 19 j = jetTable1_19 j := by
  revert j
  decide +kernel
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
def minusResidualBox (i j : Fin 20) : RI :=
  (matrixMul minusApproxBox minusBlockBox i j).sub (matrixOne i j)
lemma plusApprox_bound : matNorm plusApprox ≤ (3885/1000:ℝ) := by
  have hh := matrixNorm_bound (b := 3885000000000000000000000000000000000000000000000000000000000) plusApproxBox_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end AtomicTriangular.FiniteCertificate
end

end OAI
end


