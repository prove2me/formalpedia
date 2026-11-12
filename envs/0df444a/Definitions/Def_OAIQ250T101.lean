-- Prove2me | Definitions.Def_OAIQ250T101
-- name    : OAIQ250T101
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:53:58.029277+00:00
-- url     : https://prove2.me/theorems/bd5f7290-f9c8-4a01-87ff-90c5bdefd460
-- title:
--   Definitions bundle OAIQ250T101 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 2 definitions and 41 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.rhsMinusBox`, `OAI.AtomicTriangular.FiniteCertificate.rhsPlusBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_ParamRHS`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamRHS.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T147`, `OAIQ250T148`, `OAIQ250T083`, `OAIQ250T084` and `OAIQ250T085` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T112`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T147
import Definitions.Def_OAIQ250T148
import Definitions.Def_OAIQ250T083
import Definitions.Def_OAIQ250T084
import Definitions.Def_OAIQ250T085

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
lemma waveExp1_1_mem (j : Fin 31) : (waveExp1_1 j).Mem
    (exp (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)*((1:ℤ):ℂ))) := by
  rw [← waveExp1_1_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable1_mem j) (CI.mem_point 1)) (by
    revert j
    decide +kernel)
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveJetsData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma jetTable0_1_calc (j : Fin 31) : jetMultiplierBox 0 1 j = jetTable0_1 j := by
  revert j
  decide +kernel
lemma jetTable0_2_calc (j : Fin 31) : jetMultiplierBox 0 2 j = jetTable0_2 j := by
  revert j
  decide +kernel
lemma jetTable0_3_calc (j : Fin 31) : jetMultiplierBox 0 3 j = jetTable0_3 j := by
  revert j
  decide +kernel
lemma jetTable0_4_calc (j : Fin 31) : jetMultiplierBox 0 4 j = jetTable0_4 j := by
  revert j
  decide +kernel
lemma jetTable0_5_calc (j : Fin 31) : jetMultiplierBox 0 5 j = jetTable0_5 j := by
  revert j
  decide +kernel
lemma jetTable0_6_calc (j : Fin 31) : jetMultiplierBox 0 6 j = jetTable0_6 j := by
  revert j
  decide +kernel
lemma jetTable0_7_calc (j : Fin 31) : jetMultiplierBox 0 7 j = jetTable0_7 j := by
  revert j
  decide +kernel
lemma jetTable0_8_calc (j : Fin 31) : jetMultiplierBox 0 8 j = jetTable0_8 j := by
  revert j
  decide +kernel
lemma jetTable0_9_calc (j : Fin 31) : jetMultiplierBox 0 9 j = jetTable0_9 j := by
  revert j
  decide +kernel
lemma jetTable0_16_calc (j : Fin 31) : jetMultiplierBox 0 16 j = jetTable0_16 j := by
  revert j
  decide +kernel
lemma jetTable0_17_calc (j : Fin 31) : jetMultiplierBox 0 17 j = jetTable0_17 j := by
  revert j
  decide +kernel
lemma jetTable0_18_calc (j : Fin 31) : jetMultiplierBox 0 18 j = jetTable0_18 j := by
  revert j
  decide +kernel
lemma jetTable0_19_calc (j : Fin 31) : jetMultiplierBox 0 19 j = jetTable0_19 j := by
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix

def rhsPlusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).add (gammaBox 0 k j)) i j)
def rhsMinusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).sub (gammaBox 0 k j)) i j)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma rhsMinusTableRow0_calc (j : Fin 8) : rhsMinusBox 0 j = rhsMinusTableRow0 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow10_calc (j : Fin 8) : rhsMinusBox 10 j = rhsMinusTableRow10 j := by
  revert j
  decide +kernel
lemma rhsMinusTableRow11_calc (j : Fin 8) : rhsMinusBox 11 j = rhsMinusTableRow11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


