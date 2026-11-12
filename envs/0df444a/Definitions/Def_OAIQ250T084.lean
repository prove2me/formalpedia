-- Prove2me | Definitions.Def_OAIQ250T084
-- name    : OAIQ250T084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:28:49.462879+00:00
-- url     : https://prove2.me/theorems/b0c4598c-e3f9-415a-a8b6-90f0ec085aa2
-- title:
--   Definitions bundle OAIQ250T084 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 5 definitions and 44 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.splitL`, `OAI.AtomicTriangular.FiniteCertificate.UplusCachedBox`, `OAI.AtomicTriangular.FiniteCertificate.fullJetBox`, `OAI.AtomicTriangular.FiniteCertificate.minusInverseBox`, `OAI.AtomicTriangular.FiniteCertificate.minusResidualBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_ParamA`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamA.lean), [`Triangular_Certificate_ParamU`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean), [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Construction_ConcreteSchur`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean), [`Triangular_Envelope_EnvelopePsiB`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean), [`Triangular_Envelope_EnvelopePsiD`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T047`, `OAIQ250T048`, `OAIQ250T049` and `OAIQ250T050` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T099`, `OAIQ250T100`, `OAIQ250T101`, `OAIQ250T102` and `OAIQ250T103`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T047
import Definitions.Def_OAIQ250T048
import Definitions.Def_OAIQ250T049
import Definitions.Def_OAIQ250T050

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
lemma phaseHTable0_mem (j : Fin 31) : (phaseHTable0 j).Mem (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)) := by
  rw [← phaseHTable0_calc]
  exact wavePhaseBox_mem 0 1 j
lemma phaseHTable1_mem (j : Fin 31) : (phaseHTable1 j).Mem (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)) := by
  rw [← phaseHTable1_calc]
  exact wavePhaseBox_mem 1 1 j
lemma phaseHTable_mem (q : Fin 2) (j : Fin 31) :
    (phaseHTable q j).Mem (I*Real.pi*zeta (damping q) (damping 1) (frequency j)) := by
  fin_cases q
  · exact phaseHTable0_mem j
  · exact phaseHTable1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_JetMatrix
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
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_Inverse
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
def minusResidualBox (i j : Fin 20) : RI :=
  (matrixMul minusApproxBox minusBlockBox i j).sub (matrixOne i j)
def minusInverseBox (i j : Fin 20) : RI := (minusApproxBox i j).widen 10000000000000000000000000000000000000
lemma plusResidualRow13_calc (j : Fin 20) : plusResidualBox 13 j = plusResidualRow13 j := by
  revert j
  decide +kernel
lemma plusResidualRow14_calc (j : Fin 20) : plusResidualBox 14 j = plusResidualRow14 j := by
  revert j
  decide +kernel
lemma plusResidualRow15_calc (j : Fin 20) : plusResidualBox 15 j = plusResidualRow15 j := by
  revert j
  decide +kernel
lemma plusResidualRow16_calc (j : Fin 20) : plusResidualBox 16 j = plusResidualRow16 j := by
  revert j
  decide +kernel
lemma plusResidualRow17_calc (j : Fin 20) : plusResidualBox 17 j = plusResidualRow17 j := by
  revert j
  decide +kernel
lemma plusResidualRow18_calc (j : Fin 20) : plusResidualBox 18 j = plusResidualRow18 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamU
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
-- module Solutions.OAIQ250_TR.Triangular_Certificate_ParamA
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma A1Table_calc (i : Fin 23) (j : Fin 8) : A1CachedBox i j = A1Table i j := by
  fin_cases i
  · exact A1TableRow0_calc j
  · exact A1TableRow1_calc j
  · exact A1TableRow2_calc j
  · exact A1TableRow3_calc j
  · exact A1TableRow4_calc j
  · exact A1TableRow5_calc j
  · exact A1TableRow6_calc j
  · exact A1TableRow7_calc j
  · exact A1TableRow8_calc j
  · exact A1TableRow9_calc j
  · exact A1TableRow10_calc j
  · exact A1TableRow11_calc j
  · exact A1TableRow12_calc j
  · exact A1TableRow13_calc j
  · exact A1TableRow14_calc j
  · exact A1TableRow15_calc j
  · exact A1TableRow16_calc j
  · exact A1TableRow17_calc j
  · exact A1TableRow18_calc j
  · exact A1TableRow19_calc j
  · exact A1TableRow20_calc j
  · exact A1TableRow21_calc j
  · exact A1TableRow22_calc j
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
lemma psiB21_calc (j : Fin 31) : psiBox 0 1 21 j QBox21 DBox21 (lambdaNorm0 j) (phaseNorm01 j) (envelopeExpB21 j)=psiB21 j := by
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
lemma envelopeExpD36_mem (j : Fin 31) : (envelopeExpD36 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*36)) := by
  rw [← envelopeExpD36_calc]
  have hh := decayExpBox_mem 0 0 36 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD36_pre j)
lemma psiD36_calc (j : Fin 31) : psiBox 0 0 36 j QBox0 DBox0 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD36 j)=psiD36 j := by
  revert j
  decide +kernel
lemma envelopeExpD37_mem (j : Fin 31) : (envelopeExpD37 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*37)) := by
  rw [← envelopeExpD37_calc]
  have hh := decayExpBox_mem 0 0 37 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD37_pre j)
lemma psiD37_calc (j : Fin 31) : psiBox 0 0 37 j QBox1 DBox1 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD37 j)=psiD37 j := by
  revert j
  decide +kernel
lemma envelopeExpD39_mem (j : Fin 31) : (envelopeExpD39 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*39)) := by
  rw [← envelopeExpD39_calc]
  have hh := decayExpBox_mem 0 0 39 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD39_pre j)
lemma psiD39_calc (j : Fin 31) : psiBox 0 0 39 j QBox3 DBox3 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD39 j)=psiD39 j := by
  revert j
  decide +kernel
lemma envelopeExpD40_mem (j : Fin 31) : (envelopeExpD40 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*40)) := by
  rw [← envelopeExpD40_calc]
  have hh := decayExpBox_mem 0 0 40 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD40_pre j)
lemma psiD40_calc (j : Fin 31) : psiBox 0 0 40 j QBox4 DBox4 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD40 j)=psiD40 j := by
  revert j
  decide +kernel
lemma envelopeExpD43_mem (j : Fin 31) : (envelopeExpD43 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*43)) := by
  rw [← envelopeExpD43_calc]
  have hh := decayExpBox_mem 0 0 43 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD43_pre j)
lemma psiD43_calc (j : Fin 31) : psiBox 0 0 43 j QBox7 DBox7 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD43 j)=psiD43 j := by
  revert j
  decide +kernel
lemma envelopeExpD45_mem (j : Fin 31) : (envelopeExpD45 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*45)) := by
  rw [← envelopeExpD45_calc]
  have hh := decayExpBox_mem 0 0 45 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD45_pre j)
lemma psiD45_calc (j : Fin 31) : psiBox 0 0 45 j QBox9 DBox9 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD45 j)=psiD45 j := by
  revert j
  decide +kernel
lemma envelopeExpD48_mem (j : Fin 31) : (envelopeExpD48 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*48)) := by
  rw [← envelopeExpD48_calc]
  have hh := decayExpBox_mem 0 0 48 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD48_pre j)
lemma psiD48_calc (j : Fin 31) : psiBox 0 0 48 j QBox12 DBox12 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD48 j)=psiD48 j := by
  revert j
  decide +kernel
lemma envelopeExpD49_mem (j : Fin 31) : (envelopeExpD49 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*49)) := by
  rw [← envelopeExpD49_calc]
  have hh := decayExpBox_mem 0 0 49 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD49_pre j)
lemma psiD49_calc (j : Fin 31) : psiBox 0 0 49 j QBox13 DBox13 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD49 j)=psiD49 j := by
  revert j
  decide +kernel
lemma envelopeExpD52_mem (j : Fin 31) : (envelopeExpD52 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*52)) := by
  rw [← envelopeExpD52_calc]
  have hh := decayExpBox_mem 0 0 52 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD52_pre j)
lemma psiD52_calc (j : Fin 31) : psiBox 0 0 52 j QBox16 DBox16 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD52 j)=psiD52 j := by
  revert j
  decide +kernel
lemma envelopeExpD55_mem (j : Fin 31) : (envelopeExpD55 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*55)) := by
  rw [← envelopeExpD55_calc]
  have hh := decayExpBox_mem 0 0 55 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD55_pre j)
lemma psiD55_calc (j : Fin 31) : psiBox 0 0 55 j QBox19 DBox19 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD55 j)=psiD55 j := by
  revert j
  decide +kernel
lemma envelopeExpD57_mem (j : Fin 31) : (envelopeExpD57 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*57)) := by
  rw [← envelopeExpD57_calc]
  have hh := decayExpBox_mem 0 0 57 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD57_pre j)
lemma psiD57_calc (j : Fin 31) : psiBox 0 0 57 j QBox21 DBox21 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD57 j)=psiD57 j := by
  revert j
  decide +kernel
lemma psiD25_calc (j : Fin 31) : psiBox 0 0 25 j QBox25 DBox25 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD25 j)=psiD25 j := by
  revert j
  decide +kernel
lemma psiD27_calc (j : Fin 31) : psiBox 0 0 27 j QBox27 DBox27 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD27 j)=psiD27 j := by
  revert j
  decide +kernel
lemma psiD28_calc (j : Fin 31) : psiBox 0 0 28 j QBox28 DBox28 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD28 j)=psiD28 j := by
  revert j
  decide +kernel
lemma envelopeExpD31_mem (j : Fin 31) : (envelopeExpD31 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*31)) := by
  rw [← envelopeExpD31_calc]
  have hh := decayExpBox_mem 0 0 31 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase00_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpD31_pre j)
lemma psiD31_calc (j : Fin 31) : psiBox 0 0 31 j QBox31 DBox31 (lambdaNorm0 j) (phaseNorm00 j) (envelopeExpD31 j)=psiD31 j := by
  revert j
  decide +kernel
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
lemma envelopeSumBoxD_calc (j : Fin 31) : (RI.sum (fun i : Fin 15 => psiTableD i j)).mul ((RI.point 1).sub (periodExpD j)).invPos=envelopeSumBoxD j := by
  revert j
  decide +kernel
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

def splitL (e : Fin 2) : FiniteCoefficients →L[ℝ] FiniteCoefficients :=
  if e.val=0 then Lplus else Lminus
end AtomicTriangular.Construction
end

end OAI
end


