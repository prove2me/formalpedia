-- Prove2me | Definitions.Def_OAIQ262T153
-- name    : OAIQ262T153
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:38:38.66329+00:00
-- url     : https://prove2.me/theorems/a5132c2f-99a6-4bb3-a879-2f66e1b614b1
-- title:
--   Definitions bundle OAIQ262T153 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 15 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139`, `OAIQ262T140` and `OAIQ262T141` of this split.
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
lemma phaseHTable_mem (q : Fin 2) (j : Fin 31) :
    (phaseHTable q j).Mem (I*Real.pi*zeta (damping q) (damping 1) (frequency j)) := by
  fin_cases q
  · exact phaseHTable0_mem j
  · exact phaseHTable1_mem j
lemma DTable_mem (a : Fin 10) : (DTable a).Mem (D (finiteNode a)) := by
  fin_cases a
  · exact DBox1_mem
  · exact DBox3_mem
  · exact DBox4_mem
  · exact DBox7_mem
  · exact DBox9_mem
  · exact DBox12_mem
  · exact DBox13_mem
  · exact DBox16_mem
  · exact DBox19_mem
  · exact DBox21_mem

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
lemma jetTable0_0_calc (j : Fin 31) : jetMultiplierBox 0 0 j = jetTable0_0 j := by
  revert j
  decide +kernel
lemma jetTable0_10_calc (j : Fin 31) : jetMultiplierBox 0 10 j = jetTable0_10 j := by
  revert j
  decide +kernel
lemma jetTable0_11_calc (j : Fin 31) : jetMultiplierBox 0 11 j = jetTable0_11 j := by
  revert j
  decide +kernel
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
lemma psiD36_mem (j : Fin 31) : (psiD36 j).Mem (normJetEnvelope (damping 0) (damping 0) 36 (frequency j)) := by
  rw [← psiD36_calc]
  apply psiBox_mem
  · convert QBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD36_mem j
  · decide +kernel
lemma psiD37_mem (j : Fin 31) : (psiD37 j).Mem (normJetEnvelope (damping 0) (damping 0) 37 (frequency j)) := by
  rw [← psiD37_calc]
  apply psiBox_mem
  · convert QBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD37_mem j
  · decide +kernel
lemma psiD39_mem (j : Fin 31) : (psiD39 j).Mem (normJetEnvelope (damping 0) (damping 0) 39 (frequency j)) := by
  rw [← psiD39_calc]
  apply psiBox_mem
  · convert QBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD39_mem j
  · decide +kernel
lemma psiD40_mem (j : Fin 31) : (psiD40 j).Mem (normJetEnvelope (damping 0) (damping 0) 40 (frequency j)) := by
  rw [← psiD40_calc]
  apply psiBox_mem
  · convert QBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD40_mem j
  · decide +kernel
lemma psiD43_mem (j : Fin 31) : (psiD43 j).Mem (normJetEnvelope (damping 0) (damping 0) 43 (frequency j)) := by
  rw [← psiD43_calc]
  apply psiBox_mem
  · convert QBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD43_mem j
  · decide +kernel
lemma psiD45_mem (j : Fin 31) : (psiD45 j).Mem (normJetEnvelope (damping 0) (damping 0) 45 (frequency j)) := by
  rw [← psiD45_calc]
  apply psiBox_mem
  · convert QBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD45_mem j
  · decide +kernel
lemma psiD48_mem (j : Fin 31) : (psiD48 j).Mem (normJetEnvelope (damping 0) (damping 0) 48 (frequency j)) := by
  rw [← psiD48_calc]
  apply psiBox_mem
  · convert QBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD48_mem j
  · decide +kernel
lemma psiD27_mem (j : Fin 31) : (psiD27 j).Mem (normJetEnvelope (damping 0) (damping 0) 27 (frequency j)) := by
  rw [← psiD27_calc]
  apply psiBox_mem
  · exact QBox27_mem
  · exact DBox27_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD27_mem j
  · decide +kernel
lemma psiD28_mem (j : Fin 31) : (psiD28 j).Mem (normJetEnvelope (damping 0) (damping 0) 28 (frequency j)) := by
  rw [← psiD28_calc]
  apply psiBox_mem
  · exact QBox28_mem
  · exact DBox28_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD28_mem j
  · decide +kernel
lemma psiD31_mem (j : Fin 31) : (psiD31 j).Mem (normJetEnvelope (damping 0) (damping 0) 31 (frequency j)) := by
  rw [← psiD31_calc]
  apply psiBox_mem
  · exact QBox31_mem
  · exact DBox31_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm00_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpD31_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


