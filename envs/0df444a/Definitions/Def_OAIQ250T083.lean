-- Prove2me | Definitions.Def_OAIQ250T083
-- name    : OAIQ250T083
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:19:33.375101+00:00
-- url     : https://prove2.me/theorems/b3260186-f3ae-4ef8-a941-864d9ab5f2d1
-- title:
--   Definitions bundle OAIQ250T083 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 4 definitions and 60 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.CallOperator`, `OAI.AtomicTriangular.Construction.Coperator`, `OAI.AtomicTriangular.FiniteCertificate.YfBox`, `OAI.AtomicTriangular.FiniteCertificate.jetMultiplierBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_WaveIntervals`, `Triangular_Certificate_WaveJetsData`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_RepetitionBound`, `Triangular_Construction_RepetitionOperators`, `Triangular_Envelope_EnvelopeNorms`, `Triangular_Envelope_EnvelopePsiB`, `Triangular_Envelope_EnvelopePsiC`, `Triangular_Envelope_EnvelopePsiD`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_EnvelopeWaves`, `Triangular_Envelope_KernelBounds`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T011`, `OAIQ250T047`, `OAIQ250T048` and `OAIQ250T049` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T099`, `OAIQ250T100`, `OAIQ250T101`, `OAIQ250T102`, `OAIQ250T103` and `OAIQ250T104`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T047
import Definitions.Def_OAIQ250T048
import Definitions.Def_OAIQ250T049

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma fourier_node_deriv_cancel (n : Node) : waveDerivative 1 n.val = 0 := by
  rw [← (hasDerivAt_P n.val).deriv, deriv_P_node]

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma DBox21_mem : DBox21.Mem (D 21) := by
  rw [← DBox21_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_21_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox21_mem
  · left; decide +kernel
end AtomicTriangular.FiniteCertificate

end
end
end
end
end
end
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
def jetMultiplierBox (q : Fin 2) (i : Fin 20) (j : Fin 31) : CI :=
  let n : Fin 10 := ⟨i.val/2,by omega⟩
  (((CI.ofReal (QTable n).invPos).mul (lambdaTable q j)).mul (waveExpTable q n j)).mul
    (if i.val%2=0 then CI.point (-1) else (CI.ofReal (DTable n)).sub (phaseHTable q j))
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

def YfBox (i : Fin 20) (j : Fin 8) : RI :=
  if i.val<8 then (targetCoefficientBox ⟨i.val/2,by omega⟩).mul
    (if i.val%2=0 then (if j.val=i.val then RI.point 1 else RI.point 0)
     else (if j.val=i.val then RI.point (-1) else if j.val=i.val-1 then etaPiBox.sub (DTable ⟨i.val/2,by omega⟩) else RI.point 0))
  else RI.point 0

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullWTable_mem (i : Fin 15) (d : Fin 2) : (fullWTable i d).Mem (fullTailW i d) := by
  rw [← fullWTable_calc]
  exact fullTailWBox_mem columnNorm22 fourierNorm_mem i d
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaNorm0_mem (j : Fin 31) : (lambdaNorm0 j).Mem ‖lambda (damping 0) (frequency j)‖ := by
  have hh := lambdaNorm0_check j
  exact CI.mem_norm (lambdaTable_mem 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma envelopePhase00_mem (j : Fin 31) : (envelopePhase00 j).Mem (I*Real.pi*zeta (damping 0) (damping 0) (frequency j)) := by
  rw [← envelopePhase00_calc]
  exact wavePhaseBox_mem 0 0 j
lemma phaseNorm00_mem (j : Fin 31) : (phaseNorm00 j).Mem ‖I*Real.pi*zeta (damping 0) (damping 0) (frequency j)‖ := by
  have hh := phaseNorm00_check j
  exact CI.mem_norm (envelopePhase00_mem j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma envelopePhase01_mem (j : Fin 31) : (envelopePhase01 j).Mem (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)) := by
  rw [← envelopePhase01_calc]
  exact wavePhaseBox_mem 0 1 j
lemma phaseNorm01_mem (j : Fin 31) : (phaseNorm01 j).Mem ‖I*Real.pi*zeta (damping 0) (damping 1) (frequency j)‖ := by
  have hh := phaseNorm01_check j
  exact CI.mem_norm (envelopePhase01_mem j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpB1_mem (j : Fin 31) : (envelopeExpB1 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*1)) := by
  rw [← envelopeExpB1_calc]
  have hh := decayExpBox_mem 0 1 1 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB1_pre j)
lemma psiB1_calc (j : Fin 31) : psiBox 0 1 1 j QBox1 DBox1 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB1 j)=psiB1 j := by
  revert j
  decide +kernel
lemma envelopeExpB3_mem (j : Fin 31) : (envelopeExpB3 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*3)) := by
  rw [← envelopeExpB3_calc]
  have hh := decayExpBox_mem 0 1 3 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB3_pre j)
lemma envelopeExpB4_mem (j : Fin 31) : (envelopeExpB4 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*4)) := by
  rw [← envelopeExpB4_calc]
  have hh := decayExpBox_mem 0 1 4 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB4_pre j)
lemma envelopeExpB7_mem (j : Fin 31) : (envelopeExpB7 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*7)) := by
  rw [← envelopeExpB7_calc]
  have hh := decayExpBox_mem 0 1 7 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB7_pre j)
lemma envelopeExpB9_mem (j : Fin 31) : (envelopeExpB9 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*9)) := by
  rw [← envelopeExpB9_calc]
  have hh := decayExpBox_mem 0 1 9 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB9_pre j)
lemma envelopeExpB12_mem (j : Fin 31) : (envelopeExpB12 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*12)) := by
  rw [← envelopeExpB12_calc]
  have hh := decayExpBox_mem 0 1 12 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB12_pre j)
lemma psiB12_calc (j : Fin 31) : psiBox 0 1 12 j QBox12 DBox12 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB12 j)=psiB12 j := by
  revert j
  decide +kernel
lemma psiB12_mem (j : Fin 31) : (psiB12 j).Mem (normJetEnvelope (damping 0) (damping 1) 12 (frequency j)) := by
  rw [← psiB12_calc]
  apply psiBox_mem
  · exact QBox12_mem
  · exact DBox12_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB12_mem j
  · decide +kernel
lemma envelopeExpB13_mem (j : Fin 31) : (envelopeExpB13 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*13)) := by
  rw [← envelopeExpB13_calc]
  have hh := decayExpBox_mem 0 1 13 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB13_pre j)
lemma psiB13_calc (j : Fin 31) : psiBox 0 1 13 j QBox13 DBox13 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB13 j)=psiB13 j := by
  revert j
  decide +kernel
lemma psiB13_mem (j : Fin 31) : (psiB13 j).Mem (normJetEnvelope (damping 0) (damping 1) 13 (frequency j)) := by
  rw [← psiB13_calc]
  apply psiBox_mem
  · exact QBox13_mem
  · exact DBox13_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB13_mem j
  · decide +kernel
lemma envelopeExpB16_mem (j : Fin 31) : (envelopeExpB16 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*16)) := by
  rw [← envelopeExpB16_calc]
  have hh := decayExpBox_mem 0 1 16 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB16_pre j)
lemma psiB16_calc (j : Fin 31) : psiBox 0 1 16 j QBox16 DBox16 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB16 j)=psiB16 j := by
  revert j
  decide +kernel
lemma psiB16_mem (j : Fin 31) : (psiB16 j).Mem (normJetEnvelope (damping 0) (damping 1) 16 (frequency j)) := by
  rw [← psiB16_calc]
  apply psiBox_mem
  · exact QBox16_mem
  · exact DBox16_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB16_mem j
  · decide +kernel
lemma envelopeExpB19_mem (j : Fin 31) : (envelopeExpB19 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*19)) := by
  rw [← envelopeExpB19_calc]
  have hh := decayExpBox_mem 0 1 19 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB19_pre j)
lemma psiB19_calc (j : Fin 31) : psiBox 0 1 19 j QBox19 DBox19 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB19 j)=psiB19 j := by
  revert j
  decide +kernel
lemma psiB19_mem (j : Fin 31) : (psiB19 j).Mem (normJetEnvelope (damping 0) (damping 1) 19 (frequency j)) := by
  rw [← psiB19_calc]
  apply psiBox_mem
  · exact QBox19_mem
  · exact DBox19_mem
  · exact lambdaNorm0_mem j
  · exact phaseNorm01_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpB19_mem j
  · decide +kernel
lemma envelopeExpB21_mem (j : Fin 31) : (envelopeExpB21 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*21)) := by
  rw [← envelopeExpB21_calc]
  have hh := decayExpBox_mem 0 1 21 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB21_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma psiC45_calc (j : Fin 31) : psiBox 1 0 45 j QBox9 DBox9 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC45 j)=psiC45 j := by
  revert j
  decide +kernel
lemma psiC45_mem (j : Fin 31) : (psiC45 j).Mem (normJetEnvelope (damping 1) (damping 0) 45 (frequency j)) := by
  rw [← psiC45_calc]
  apply psiBox_mem
  · convert QBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox9_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC45_mem j
  · decide +kernel
lemma envelopeExpC48_mem (j : Fin 31) : (envelopeExpC48 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*48)) := by
  rw [← envelopeExpC48_calc]
  have hh := decayExpBox_mem 1 0 48 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC48_pre j)
lemma psiC48_calc (j : Fin 31) : psiBox 1 0 48 j QBox12 DBox12 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC48 j)=psiC48 j := by
  revert j
  decide +kernel
lemma psiC48_mem (j : Fin 31) : (psiC48 j).Mem (normJetEnvelope (damping 1) (damping 0) 48 (frequency j)) := by
  rw [← psiC48_calc]
  apply psiBox_mem
  · convert QBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox12_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC48_mem j
  · decide +kernel
lemma envelopeExpC49_mem (j : Fin 31) : (envelopeExpC49 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*49)) := by
  rw [← envelopeExpC49_calc]
  have hh := decayExpBox_mem 1 0 49 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC49_pre j)
lemma psiC49_calc (j : Fin 31) : psiBox 1 0 49 j QBox13 DBox13 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC49 j)=psiC49 j := by
  revert j
  decide +kernel
lemma psiC49_mem (j : Fin 31) : (psiC49 j).Mem (normJetEnvelope (damping 1) (damping 0) 49 (frequency j)) := by
  rw [← psiC49_calc]
  apply psiBox_mem
  · convert QBox13_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox13_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC49_mem j
  · decide +kernel
lemma envelopeExpC52_mem (j : Fin 31) : (envelopeExpC52 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*52)) := by
  rw [← envelopeExpC52_calc]
  have hh := decayExpBox_mem 1 0 52 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC52_pre j)
lemma psiC52_calc (j : Fin 31) : psiBox 1 0 52 j QBox16 DBox16 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC52 j)=psiC52 j := by
  revert j
  decide +kernel
lemma psiC52_mem (j : Fin 31) : (psiC52 j).Mem (normJetEnvelope (damping 1) (damping 0) 52 (frequency j)) := by
  rw [← psiC52_calc]
  apply psiBox_mem
  · convert QBox16_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox16_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC52_mem j
  · decide +kernel
lemma envelopeExpC55_mem (j : Fin 31) : (envelopeExpC55 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*55)) := by
  rw [← envelopeExpC55_calc]
  have hh := decayExpBox_mem 1 0 55 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC55_pre j)
lemma psiC55_calc (j : Fin 31) : psiBox 1 0 55 j QBox19 DBox19 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC55 j)=psiC55 j := by
  revert j
  decide +kernel
lemma psiC55_mem (j : Fin 31) : (psiC55 j).Mem (normJetEnvelope (damping 1) (damping 0) 55 (frequency j)) := by
  rw [← psiC55_calc]
  apply psiBox_mem
  · convert QBox19_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox19_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC55_mem j
  · decide +kernel
lemma envelopeExpC57_mem (j : Fin 31) : (envelopeExpC57 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*57)) := by
  rw [← envelopeExpC57_calc]
  have hh := decayExpBox_mem 1 0 57 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC57_pre j)
lemma psiC57_calc (j : Fin 31) : psiBox 1 0 57 j QBox21 DBox21 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC57 j)=psiC57 j := by
  revert j
  decide +kernel
lemma psiC57_mem (j : Fin 31) : (psiC57 j).Mem (normJetEnvelope (damping 1) (damping 0) 57 (frequency j)) := by
  rw [← psiC57_calc]
  apply psiBox_mem
  · convert QBox21_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox21_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC57_mem j
  · decide +kernel
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
lemma envelopeExpD25_mem (j : Fin 31) : (envelopeExpD25 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*25)) := by
  rw [← envelopeExpD25_calc]
  have hh := decayExpBox_mem 0 0 25 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD25_pre j)
lemma envelopeExpD27_mem (j : Fin 31) : (envelopeExpD27 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*27)) := by
  rw [← envelopeExpD27_calc]
  have hh := decayExpBox_mem 0 0 27 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD27_pre j)
lemma envelopeExpD28_mem (j : Fin 31) : (envelopeExpD28 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*28)) := by
  rw [← envelopeExpD28_calc]
  have hh := decayExpBox_mem 0 0 28 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD28_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma psiTableC_mem (i : Fin 15) (j : Fin 31) : (psiTableC i j).Mem (normJetEnvelope (damping 1) (damping 0) (tailBase i) (frequency j)) := by
  fin_cases i
  · exact psiC36_mem j
  · exact psiC37_mem j
  · exact psiC39_mem j
  · exact psiC40_mem j
  · exact psiC43_mem j
  · exact psiC45_mem j
  · exact psiC48_mem j
  · exact psiC49_mem j
  · exact psiC52_mem j
  · exact psiC55_mem j
  · exact psiC57_mem j
  · exact psiC25_mem j
  · exact psiC27_mem j
  · exact psiC28_mem j
  · exact psiC31_mem j
lemma envelopeSumBoxC_mem (j : Fin 31) : (envelopeSumBoxC j).Mem (tailEnvelopeSum 1 0 j) := by
  rw [← envelopeSumBoxC_calc]
  exact RI.mem_mul (RI.mem_sum (fun i => psiTableC_mem i j))
    (RI.mem_invPos (RI.mem_sub ri1_mem (periodExpC_mem j)) (periodDenC_pos j))
lemma periodExpD_mem (j : Fin 31) : (periodExpD j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*36)) := by
  rw [← periodExpD_calc]
  have hh := decayExpBox_mem 0 0 36 j
  unfold decayExpBox decayBox RI.neg at hh
  rw [envelopePhase00_calc] at hh
  simp only [neg_neg] at hh
  exact hh (periodExpD_pre j)
lemma boundC_mem (c : Fin 22) : (boundC c).Mem (tailFiniteEnvelope c) := by
  rw [← boundC_calc]
  exact RI.mem_sum (fun j => RI.mem_mul (envelopeSumBoxC_mem j) (columnNormTable_mem _ j))
lemma tailFiniteEnvelope_bound (c : Fin 22) : tailFiniteEnvelope c < (7/1000000000000000:ℝ) := by
  apply ri_mem_lt (boundC_mem c) 7 1000000000000000 (by norm_num)
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma tail_finite_column_bound (c : Fin 22) :
    (∑' p : TailNode × Fin 2, |jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩)|) < 7/10^15 := by
  exact (tail_atom_column_bounds 1 0 _).2.trans_lt (by norm_num [tailFiniteEnvelope,damping,H,h] at ⊢; simpa [tailFiniteEnvelope] using FiniteCertificate.tailFiniteEnvelope_bound c)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma Ckernel_bound (i : Fin 20) : (∑' p, |Ckernel p i|) ≤ 7/10^15 :=
  (tail_finite_column_bound ⟨i.val+2,by omega⟩).le
def Coperator : FiniteCoefficients →L[ℝ] TailCoefficients :=
  operator Ckernel Ckernel_summable (7/10^15) Ckernel_bound
lemma Coperator_norm : ‖Coperator‖ ≤ 7/10^15 := operator_norm _ _ _ (by norm_num) _
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma repetitionNormBox_mem : repetitionNormBox.Mem repetitionNorm := by
  rw [← repetitionNormBox_calc]
  unfold repetitionNorm
  rw [div_eq_mul_inv]
  apply RI.mem_mul
  · apply RI.mem_mul
    · exact RI.mem_add ri1_mem (RI.mem_mul piBox_mem
        (by simpa [Construction.eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5)))
    · exact repetitionExpData_mem
  · exact RI.mem_invPos (RI.mem_sub ri1_mem repetitionExpData_mem) (by decide +kernel)
lemma repetitionNorm_bound : repetitionNorm < (1/4000000000:ℝ) := by
  simpa using ri_mem_lt repetitionNormBox_mem 1 4000000000 (by norm_num) (by decide +kernel)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
def CallOperator : TrigonometricCoefficients →L[ℝ] TailCoefficients :=
  operator CallKernel (fun _ => (tail_atom_column_bounds 1 0 _).1) (7/10^15)
    (fun i => (tail_finite_column_bound i).le)
lemma CallOperator_norm : ‖CallOperator‖ ≤ 7/10^15 :=
  operator_norm _ _ _ (by norm_num) _
lemma AC_bound : ‖Aoperator‖+‖Coperator‖ ≤ beta := by
  have hA := Aoperator_norm
  have hC := Coperator_norm
  have hr := repetitionNorm_bound
  norm_num [beta] at *
  linarith
lemma AC_all_bound : ‖AallOperator‖+‖CallOperator‖ ≤ beta := by
  have hA := AallOperator_norm
  have hC := CallOperator_norm
  have hr := repetitionNorm_bound
  norm_num [beta] at *
  linarith
end AtomicTriangular.Construction
end

end OAI
end


