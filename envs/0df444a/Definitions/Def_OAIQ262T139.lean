-- Prove2me | Definitions.Def_OAIQ262T139
-- name    : OAIQ262T139
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:32:22.326192+00:00
-- url     : https://prove2.me/theorems/78657c62-28d7-481f-a724-4792218d3e95
-- title:
--   Definitions bundle OAIQ262T139 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 4 definitions and 33 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.R0Box`, `OAI.AtomicTriangular.FiniteCertificate.UplusCachedBox`, `OAI.AtomicTriangular.FiniteCertificate.fullJetBox`, `OAI.AtomicTriangular.FiniteCertificate.minusInverseBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_ParamU`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Envelope_EnvelopePsiB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_EnvelopeWaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeWaves.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T085`, `OAIQ262T086`, `OAIQ262T088`, `OAIQ262T089`, `OAIQ262T090`, `OAIQ262T091` and `OAIQ262T092` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T152`, `OAIQ262T153`, `OAIQ262T154`, `OAIQ262T157` and `OAIQ262T158`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T085
import Definitions.Def_OAIQ262T086
import Definitions.Def_OAIQ262T088
import Definitions.Def_OAIQ262T089
import Definitions.Def_OAIQ262T090
import Definitions.Def_OAIQ262T091
import Definitions.Def_OAIQ262T092

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
lemma QTable_mem (a : Fin 10) : (QTable a).Mem (Q (finiteNode a)) := by
  fin_cases a
  · exact QBox1_mem
  · exact QBox3_mem
  · exact QBox4_mem
  · exact QBox7_mem
  · exact QBox9_mem
  · exact QBox12_mem
  · exact QBox13_mem
  · exact QBox16_mem
  · exact QBox19_mem
  · exact QBox21_mem

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def fullJetBox (i : Fin 20) (col : Fin 23) : RI :=
  (CI.sum (fun j : Fin 31 => (jetTable (if col.val=22 then 0 else 1) i j).mul (columnTable col j))).re
def R0Box (i : Fin 20) (j : Fin 3) : RI := jetMatrixTable i (if j.val<2 then ⟨j.val,by omega⟩ else 22)
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
def minusInverseBox (i j : Fin 20) : RI := (minusApproxBox i j).widen 10000000000000000000000000000000000000

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_ParamU
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def UplusCachedBox (i : Fin 20) (j : Fin 8) : RI := matrixMul minusInverseBox rhsPlusTable i j
end AtomicTriangular.FiniteCertificate
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
lemma envelopePhase00_calc (j : Fin 31) : wavePhaseBox 0 0 j=envelopePhase00 j := by
  revert j
  decide +kernel
lemma envelopePhase00_mem (j : Fin 31) : (envelopePhase00 j).Mem (I*Real.pi*zeta (damping 0) (damping 0) (frequency j)) := by
  rw [← envelopePhase00_calc]
  exact wavePhaseBox_mem 0 0 j
lemma phaseNorm00_mem (j : Fin 31) : (phaseNorm00 j).Mem ‖I*Real.pi*zeta (damping 0) (damping 0) (frequency j)‖ := by
  have hh := phaseNorm00_check j
  exact CI.mem_norm (envelopePhase00_mem j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
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
lemma psiB1_calc (j : Fin 31) : psiBox 0 1 1 j QBox1 DBox1 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB1 j)=psiB1 j := by
  revert j
  decide +kernel
lemma psiB3_calc (j : Fin 31) : psiBox 0 1 3 j QBox3 DBox3 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB3 j)=psiB3 j := by
  revert j
  decide +kernel
lemma psiB4_calc (j : Fin 31) : psiBox 0 1 4 j QBox4 DBox4 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB4 j)=psiB4 j := by
  revert j
  decide +kernel
lemma psiB7_calc (j : Fin 31) : psiBox 0 1 7 j QBox7 DBox7 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB7 j)=psiB7 j := by
  revert j
  decide +kernel
lemma psiB9_calc (j : Fin 31) : psiBox 0 1 9 j QBox9 DBox9 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB9 j)=psiB9 j := by
  revert j
  decide +kernel
lemma psiB13_calc (j : Fin 31) : psiBox 0 1 13 j QBox13 DBox13 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB13 j)=psiB13 j := by
  revert j
  decide +kernel
lemma psiB16_calc (j : Fin 31) : psiBox 0 1 16 j QBox16 DBox16 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB16 j)=psiB16 j := by
  revert j
  decide +kernel
lemma psiB19_calc (j : Fin 31) : psiBox 0 1 19 j QBox19 DBox19 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB19 j)=psiB19 j := by
  revert j
  decide +kernel
lemma psiB21_calc (j : Fin 31) : psiBox 0 1 21 j QBox21 DBox21 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB21 j)=psiB21 j := by
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
lemma envelopeExpD36_mem (j : Fin 31) : (envelopeExpD36 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*36)) := by
  rw [← envelopeExpD36_calc]
  have hh := decayExpBox_mem 0 0 36 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD36_pre j)
lemma envelopeExpD37_mem (j : Fin 31) : (envelopeExpD37 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*37)) := by
  rw [← envelopeExpD37_calc]
  have hh := decayExpBox_mem 0 0 37 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD37_pre j)
lemma envelopeExpD39_mem (j : Fin 31) : (envelopeExpD39 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*39)) := by
  rw [← envelopeExpD39_calc]
  have hh := decayExpBox_mem 0 0 39 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD39_pre j)
lemma envelopeExpD40_mem (j : Fin 31) : (envelopeExpD40 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*40)) := by
  rw [← envelopeExpD40_calc]
  have hh := decayExpBox_mem 0 0 40 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD40_pre j)
lemma envelopeExpD43_mem (j : Fin 31) : (envelopeExpD43 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*43)) := by
  rw [← envelopeExpD43_calc]
  have hh := decayExpBox_mem 0 0 43 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD43_pre j)
lemma envelopeExpD45_mem (j : Fin 31) : (envelopeExpD45 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*45)) := by
  rw [← envelopeExpD45_calc]
  have hh := decayExpBox_mem 0 0 45 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD45_pre j)
lemma envelopeExpD48_mem (j : Fin 31) : (envelopeExpD48 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*48)) := by
  rw [← envelopeExpD48_calc]
  have hh := decayExpBox_mem 0 0 48 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD48_pre j)
lemma envelopeExpD49_mem (j : Fin 31) : (envelopeExpD49 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*49)) := by
  rw [← envelopeExpD49_calc]
  have hh := decayExpBox_mem 0 0 49 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD49_pre j)
lemma envelopeExpD52_mem (j : Fin 31) : (envelopeExpD52 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*52)) := by
  rw [← envelopeExpD52_calc]
  have hh := decayExpBox_mem 0 0 52 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD52_pre j)
lemma envelopeExpD55_mem (j : Fin 31) : (envelopeExpD55 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*55)) := by
  rw [← envelopeExpD55_calc]
  have hh := decayExpBox_mem 0 0 55 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD55_pre j)
lemma envelopeExpD57_mem (j : Fin 31) : (envelopeExpD57 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*57)) := by
  rw [← envelopeExpD57_calc]
  have hh := decayExpBox_mem 0 0 57 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD57_pre j)
lemma envelopeExpD25_mem (j : Fin 31) : (envelopeExpD25 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*25)) := by
  rw [← envelopeExpD25_calc]
  have hh := decayExpBox_mem 0 0 25 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD25_pre j)
lemma psiD25_calc (j : Fin 31) : psiBox 0 0 25 j QBox25 DBox25 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD25 j)=psiD25 j := by
  revert j
  decide +kernel
lemma envelopeExpD27_mem (j : Fin 31) : (envelopeExpD27 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*27)) := by
  rw [← envelopeExpD27_calc]
  have hh := decayExpBox_mem 0 0 27 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD27_pre j)
lemma psiD27_calc (j : Fin 31) : psiBox 0 0 27 j QBox27 DBox27 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD27 j)=psiD27 j := by
  revert j
  decide +kernel
lemma envelopeExpD28_mem (j : Fin 31) : (envelopeExpD28 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*28)) := by
  rw [← envelopeExpD28_calc]
  have hh := decayExpBox_mem 0 0 28 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD28_pre j)
lemma psiD28_calc (j : Fin 31) : psiBox 0 0 28 j QBox28 DBox28 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD28 j)=psiD28 j := by
  revert j
  decide +kernel
lemma envelopeExpD31_mem (j : Fin 31) : (envelopeExpD31 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*31)) := by
  rw [← envelopeExpD31_calc]
  have hh := decayExpBox_mem 0 0 31 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD31_pre j)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma periodExpD_mem (j : Fin 31) : (periodExpD j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*36)) := by
  rw [← periodExpD_calc]
  have hh := decayExpBox_mem 0 0 36 j
  unfold decayExpBox decayBox RI.neg at hh
  rw [envelopePhase00_calc] at hh
  simp only [neg_neg] at hh
  exact hh (periodExpD_pre j)
lemma envelopeSumBoxD_calc (j : Fin 31) : (RI.sum (fun i : Fin 15 => psiTableD i j)).mul ((RI.point 1).sub (periodExpD j)).invPos=envelopeSumBoxD j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


