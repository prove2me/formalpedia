-- Prove2me | Definitions.Def_OAIQ262T138
-- name    : OAIQ262T138
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:22:20.196136+00:00
-- url     : https://prove2.me/theorems/65a3dfa9-f3e4-40ef-843c-29b150049c32
-- title:
--   Definitions bundle OAIQ262T138 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 44 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Construction_BlockOperators`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean), [`Triangular_Construction_RepetitionBound`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/RepetitionBound.lean), [`Triangular_Construction_TailJetVector`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/TailJetVector.lean), [`Triangular_Envelope_EnvelopeBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeBoxes.lean), [`Triangular_Envelope_EnvelopePsiB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopeWaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeWaves.lean), [`Triangular_Envelope_KernelBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T085`, `OAIQ262T086`, `OAIQ262T087`, `OAIQ262T088`, `OAIQ262T089` and `OAIQ262T090` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T151`, `OAIQ262T152`, `OAIQ262T153`, `OAIQ262T154` and `OAIQ262T158`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T085
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T087
import Definitions.Def_OAIQ262T088
import Definitions.Def_OAIQ262T089
import Definitions.Def_OAIQ262T090

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveIntervals
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
lemma DBox12_mem : DBox12.Mem (D 12) := by
  rw [← DBox12_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_12_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox12_mem
  · left; decide +kernel
lemma DBox13_mem : DBox13.Mem (D 13) := by
  rw [← DBox13_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_13_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox13_mem
  · left; decide +kernel
lemma DBox16_mem : DBox16.Mem (D 16) := by
  rw [← DBox16_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_16_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox16_mem
  · left; decide +kernel
lemma DBox19_mem : DBox19.Mem (D 19) := by
  rw [← DBox19_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_19_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox19_mem
  · left; decide +kernel
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
lemma QTable_pos (n : Fin 10) : 0 < (QTable n).lo := by
  revert n
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullTailWBox_mem (pn : Fin 31 → RI) (hp : ∀ l, (pn l).Mem ‖fourierCoeff l‖)
    (i : Fin 15) (d : Fin 2) : (fullTailWBox pn i d).Mem (fullTailW i d) := by
  unfold fullTailWBox fullTailW
  split_ifs with hd
  · apply RI.mem_mul (by norm_num at *; simpa using RI.mem_divNat (RI.mem_pow piBox_mem 2) (by norm_num : 0<(18^2:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · apply RI.mem_mul _ (hp l)
      apply RI.mem_sub
      · simpa using RI.mem_point ((frequencyDistance l:ℤ)-i.val)
      · simpa using RI.mem_divNat ri1_mem (by norm_num : 0<(2:ℕ))
    · exact ri0_mem
  · apply RI.mem_mul (by simpa using RI.mem_divNat piBox_mem (by norm_num : 0<(18:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · exact hp l
    · exact ri0_mem

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailJetVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
lemma tailJet_pair_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    (∑ d : Fin 2, |tailJet (damping q) (damping v) m n c d|)  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  apply le_trans _ (tailJetVector_bound q v m n hm hQ c)
  rw [PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum (fun d _ => Complex.abs_re_le_norm _)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaNorm0_check (j : Fin 31) : 0≤(lambdaNorm0 j).lo ∧ (lambdaNorm0 j).lo*(lambdaNorm0 j).lo ≤ scale*max 0 (lambdaTable 0 j).normSq.lo ∧ scale*(lambdaTable 0 j).normSq.hi ≤ (lambdaNorm0 j).hi*(lambdaNorm0 j).hi ∧ 0≤(lambdaNorm0 j).hi := by
  revert j
  decide +kernel
lemma lambdaNorm0_mem (j : Fin 31) : (lambdaNorm0 j).Mem ‖lambda (damping 0) (frequency j)‖ := by
  have hh := lambdaNorm0_check j
  exact CI.mem_norm (lambdaTable_mem 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma envelopePhase01_calc (j : Fin 31) : wavePhaseBox 0 1 j=envelopePhase01 j := by
  revert j
  decide +kernel
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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiB
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
lemma envelopeExpB16_mem (j : Fin 31) : (envelopeExpB16 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*16)) := by
  rw [← envelopeExpB16_calc]
  have hh := decayExpBox_mem 0 1 16 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB16_pre j)
lemma envelopeExpB19_mem (j : Fin 31) : (envelopeExpB19 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*19)) := by
  rw [← envelopeExpB19_calc]
  have hh := decayExpBox_mem 0 1 19 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase01_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpB19_pre j)
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
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma psiC39_calc (j : Fin 31) : psiBox 1 0 39 j QBox3 DBox3 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC39 j)=psiC39 j := by
  revert j
  decide +kernel
lemma psiC40_calc (j : Fin 31) : psiBox 1 0 40 j QBox4 DBox4 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC40 j)=psiC40 j := by
  revert j
  decide +kernel
lemma psiC43_calc (j : Fin 31) : psiBox 1 0 43 j QBox7 DBox7 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC43 j)=psiC43 j := by
  revert j
  decide +kernel
lemma psiC45_calc (j : Fin 31) : psiBox 1 0 45 j QBox9 DBox9 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC45 j)=psiC45 j := by
  revert j
  decide +kernel
lemma envelopeExpC48_mem (j : Fin 31) : (envelopeExpC48 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*48)) := by
  rw [← envelopeExpC48_calc]
  have hh := decayExpBox_mem 1 0 48 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC48_pre j)
lemma psiC48_calc (j : Fin 31) : psiBox 1 0 48 j QBox12 DBox12 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC48 j)=psiC48 j := by
  revert j
  decide +kernel
lemma envelopeExpC49_mem (j : Fin 31) : (envelopeExpC49 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*49)) := by
  rw [← envelopeExpC49_calc]
  have hh := decayExpBox_mem 1 0 49 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC49_pre j)
lemma psiC49_calc (j : Fin 31) : psiBox 1 0 49 j QBox13 DBox13 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC49 j)=psiC49 j := by
  revert j
  decide +kernel
lemma envelopeExpC52_mem (j : Fin 31) : (envelopeExpC52 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*52)) := by
  rw [← envelopeExpC52_calc]
  have hh := decayExpBox_mem 1 0 52 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC52_pre j)
lemma psiC52_calc (j : Fin 31) : psiBox 1 0 52 j QBox16 DBox16 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC52 j)=psiC52 j := by
  revert j
  decide +kernel
lemma envelopeExpC55_mem (j : Fin 31) : (envelopeExpC55 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*55)) := by
  rw [← envelopeExpC55_calc]
  have hh := decayExpBox_mem 1 0 55 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC55_pre j)
lemma psiC55_calc (j : Fin 31) : psiBox 1 0 55 j QBox19 DBox19 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC55 j)=psiC55 j := by
  revert j
  decide +kernel
lemma envelopeExpC57_mem (j : Fin 31) : (envelopeExpC57 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*57)) := by
  rw [← envelopeExpC57_calc]
  have hh := decayExpBox_mem 1 0 57 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC57_pre j)
lemma psiC57_calc (j : Fin 31) : psiBox 1 0 57 j QBox21 DBox21 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC57 j)=psiC57 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma tail_tail_column_bounds (q v : Fin 2) (n : ℤ) (c : Fin 2) :
    Summable (fun p : TailNode × Fin 2 => |tailJet (damping q) (damping v) p.1.val.val n c p.2|) ∧
    (∑' p : TailNode × Fin 2, |tailJet (damping q) (damping v) p.1.val.val n c p.2|)  ≤ 
      ∑ i : Fin 15, tailEnvelopeSum q v ⟨i.val+16,by omega⟩*fullTailW i c := by
  have hs (i : Fin 15) : Summable (fun m : TailNode =>
      normJetEnvelope (damping q) (damping v) m.val.val (frequency ⟨i.val+16,by omega⟩)*fullTailW i c) :=
    (summable_tailEnvelope q v (abs_le.mpr (frequency_mem _))).mul_right _
  have hsum := summable_sum (s:=Finset.univ) (fun i _ => hs i)
  have hh := paired_summable_bound (fun m d => tailJet (damping q) (damping v) m.val.val n c d)
    (fun m : TailNode => ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m.val.val (frequency ⟨i.val+16,by omega⟩)*fullTailW i c)
    hsum (fun m => tailJet_pair_bound q v _ n (by have h := m.val.property.1; omega) m.val.Qpos c)
  refine ⟨hh.1,?_⟩
  calc
    _  ≤  _ := hh.2
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
      simp only [tsum_mul_right,tsum_tailEnvelope]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
lemma Dkernel_summable (q : TailNode × Fin 2) : Summable (fun p => |Dkernel p q|) :=
  (tail_tail_column_bounds 0 0 q.1.val.val q.2).1
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_RepetitionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma repetitionExpData_mem : repetitionExpData.Mem repetitionRatio := by
  rw [← repetitionExpData_calc]
  apply ri_exp_mem
  exact RI.mem_mul (RI.mem_mul (by simpa using RI.mem_point (-36)) piBox_mem)
    (by simpa [Construction.eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5))
  decide +kernel
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


