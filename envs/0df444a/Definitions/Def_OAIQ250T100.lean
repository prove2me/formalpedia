-- Prove2me | Definitions.Def_OAIQ250T100
-- name    : OAIQ250T100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:43:30.486819+00:00
-- url     : https://prove2.me/theorems/89e79bd2-bd2f-48be-b2d2-ccf72f79dd19
-- title:
--   Definitions bundle OAIQ250T100 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 2 definitions and 19 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.approximationTailResidual`, `OAI.AtomicTriangular.Construction.splitK`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Construction_ActualCorrection`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualCorrection.lean), [`Triangular_Construction_ConcreteSchur`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T083` and `OAIQ250T084` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T112`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T083
import Definitions.Def_OAIQ250T084

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
lemma waveExp0_1_mem (j : Fin 31) : (waveExp0_1 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((1:ℤ):ℂ))) := by
  rw [← waveExp0_1_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 1)) (by
    revert j
    decide +kernel)
lemma waveExp0_3_mem (j : Fin 31) : (waveExp0_3 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((3:ℤ):ℂ))) := by
  rw [← waveExp0_3_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 3)) (by
    revert j
    decide +kernel)
lemma waveExp0_4_mem (j : Fin 31) : (waveExp0_4 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((4:ℤ):ℂ))) := by
  rw [← waveExp0_4_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 4)) (by
    revert j
    decide +kernel)
lemma waveExp0_7_mem (j : Fin 31) : (waveExp0_7 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((7:ℤ):ℂ))) := by
  rw [← waveExp0_7_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 7)) (by
    revert j
    decide +kernel)
lemma waveExp0_9_mem (j : Fin 31) : (waveExp0_9 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((9:ℤ):ℂ))) := by
  rw [← waveExp0_9_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 9)) (by
    revert j
    decide +kernel)
lemma waveExp0_12_mem (j : Fin 31) : (waveExp0_12 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((12:ℤ):ℂ))) := by
  rw [← waveExp0_12_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 12)) (by
    revert j
    decide +kernel)
lemma waveExp0_13_mem (j : Fin 31) : (waveExp0_13 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((13:ℤ):ℂ))) := by
  rw [← waveExp0_13_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 13)) (by
    revert j
    decide +kernel)
lemma waveExp0_16_mem (j : Fin 31) : (waveExp0_16 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((16:ℤ):ℂ))) := by
  rw [← waveExp0_16_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 16)) (by
    revert j
    decide +kernel)
lemma waveExp0_19_mem (j : Fin 31) : (waveExp0_19 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((19:ℤ):ℂ))) := by
  rw [← waveExp0_19_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 19)) (by
    revert j
    decide +kernel)
lemma waveExp0_21_mem (j : Fin 31) : (waveExp0_21 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((21:ℤ):ℂ))) := by
  rw [← waveExp0_21_calc]
  exact CI.mem_exp_checked (CI.mem_mul (phaseHTable0_mem j) (CI.mem_point 21)) (by
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
lemma jetTable0_11_calc (j : Fin 31) : jetMultiplierBox 0 11 j = jetTable0_11 j := by
  revert j
  decide +kernel
lemma jetTable0_12_calc (j : Fin 31) : jetMultiplierBox 0 12 j = jetTable0_12 j := by
  revert j
  decide +kernel
lemma jetTable0_13_calc (j : Fin 31) : jetMultiplierBox 0 13 j = jetTable0_13 j := by
  revert j
  decide +kernel
lemma jetTable0_14_calc (j : Fin 31) : jetMultiplierBox 0 14 j = jetTable0_14 j := by
  revert j
  decide +kernel
lemma jetTable0_15_calc (j : Fin 31) : jetMultiplierBox 0 15 j = jetTable0_15 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma psiD49_mem (j : Fin 31) : (psiD49 j).Mem (normJetEnvelope (damping 0) (damping 0) 49 (frequency j)) := by
  rw [← psiD49_calc]
  apply psiBox_mem
  · convert QBox13_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox13_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD49_mem j
  · decide +kernel
lemma psiD52_mem (j : Fin 31) : (psiD52 j).Mem (normJetEnvelope (damping 0) (damping 0) 52 (frequency j)) := by
  rw [← psiD52_calc]
  apply psiBox_mem
  · convert QBox16_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox16_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD52_mem j
  · decide +kernel
lemma psiD55_mem (j : Fin 31) : (psiD55 j).Mem (normJetEnvelope (damping 0) (damping 0) 55 (frequency j)) := by
  rw [← psiD55_calc]
  apply psiBox_mem
  · convert QBox19_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox19_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD55_mem j
  · decide +kernel
lemma psiD57_mem (j : Fin 31) : (psiD57 j).Mem (normJetEnvelope (damping 0) (damping 0) 57 (frequency j)) := by
  rw [← psiD57_calc]
  apply psiBox_mem
  · convert QBox21_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox21_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD57_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ConcreteSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

def splitK (e : Fin 2) : FiniteCoefficients →L[ℝ] TailCoefficients :=
  if e.val=0 then Coperator-Aoperator else -Coperator-Aoperator
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_ActualCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

def approximationTailResidual (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  tailTarget z hz hzB +
  (if e.val=0 then CallOperator (finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z)) -
      AallOperator (finiteApprox 0 (actualParameter z)+finiteApprox 1 (actualParameter z))
    else CallOperator (finiteApprox 1 (actualParameter z)-finiteApprox 0 (actualParameter z)) -
      AallOperator (finiteApprox 0 (actualParameter z)-finiteApprox 1 (actualParameter z)) +
      (12/1000:ℝ) • tailFixedColumn 22)
end AtomicTriangular.Construction
end

end OAI
end


