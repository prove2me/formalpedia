-- Prove2me | Definitions.Def_OAIQ262T154
-- name    : OAIQ262T154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:35:06.069543+00:00
-- url     : https://prove2.me/theorems/308da6cb-92fa-4dc3-b451-8cc74ccdf7cc
-- title:
--   Definitions bundle OAIQ262T154 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 2 definitions and 13 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.YfBox`, `OAI.AtomicTriangular.FiniteCertificate.rhsMinusBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139` and `OAIQ262T140` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T193` and `OAIQ262T194`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T138
import Definitions.Def_OAIQ262T139
import Definitions.Def_OAIQ262T140

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
lemma jetTable0_1_calc (j : Fin 31) : jetMultiplierBox 0 1 j = jetTable0_1 j := by
  revert j
  decide +kernel
lemma jetTable0_2_calc (j : Fin 31) : jetMultiplierBox 0 2 j = jetTable0_2 j := by
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

def YfBox (i : Fin 20) (j : Fin 8) : RI :=
  if i.val<8 then (targetCoefficientBox ⟨i.val/2,by omega⟩).mul
    (if i.val%2=0 then (if j.val=i.val then RI.point 1 else RI.point 0)
     else (if j.val=i.val then RI.point (-1) else if j.val=i.val-1 then etaPiBox.sub (DTable ⟨i.val/2,by omega⟩) else RI.point 0))
  else RI.point 0
def rhsMinusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).sub (gammaBox 0 k j)) i j)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiD
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


