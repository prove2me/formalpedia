-- Prove2me | Definitions.Def_OAIQ262T193
-- name    : OAIQ262T193
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T20:46:19.409508+00:00
-- url     : https://prove2.me/theorems/0763bc16-80cf-414a-8e72-d01b827090ca
-- title:
--   Definitions bundle OAIQ262T193 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 174 declarations of OpenAI's Lean: 13 definitions and 161 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.CallOperator`, `OAI.AtomicTriangular.Construction.Coperator`, `OAI.AtomicTriangular.Construction.Doperator`, `OAI.AtomicTriangular.Construction.actualFiniteError`, `OAI.AtomicTriangular.Construction.actualFiniteSplit`, `OAI.AtomicTriangular.Construction.actualTail`, `OAI.AtomicTriangular.Construction.actualTailSplit`, `OAI.AtomicTriangular.Construction.approximationTailResidual`, `OAI.AtomicTriangular.Construction.correctionFinite`, `OAI.AtomicTriangular.Construction.correctionTail`, `OAI.AtomicTriangular.Construction.splitD`, `OAI.AtomicTriangular.Construction.splitK`, `OAI.AtomicTriangular.FiniteCertificate.rhsPlusBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_Inverse`, `Triangular_Certificate_JetMatrix`, `Triangular_Certificate_ParamInterval`, `Triangular_Certificate_WaveExpData`, `Triangular_Certificate_WaveJetsData`, `Triangular_Construction_ActualCorrection`, `Triangular_Construction_ActualInput`, `Triangular_Construction_ActualTail`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_ConcreteSchur`, `Triangular_Construction_FiniteSystem`, `Triangular_Construction_RepetitionOperators`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_KernelBounds`, `Triangular_Taylor_TaylorPhase`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T151`, `OAIQ262T152`, `OAIQ262T153`, `OAIQ262T154`, `OAIQ262T155`, `OAIQ262T156`, `OAIQ262T157` and `OAIQ262T158` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T253`, `OAIQ262T254`, `OAIQ262T255` and `OAIQ262T256`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T151
import Definitions.Def_OAIQ262T152
import Definitions.Def_OAIQ262T153
import Definitions.Def_OAIQ262T154
import Definitions.Def_OAIQ262T155
import Definitions.Def_OAIQ262T156
import Definitions.Def_OAIQ262T157
import Definitions.Def_OAIQ262T158

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
lemma waveExpTable_mem (q : Fin 2) (n : Fin 10) (j : Fin 31) : (waveExpTable q n j).Mem
    (exp (I*Real.pi*zeta (damping q) (damping 1) (frequency j)*(finiteNode n:ℂ))) := by
  fin_cases q <;> fin_cases n
  · exact waveExp0_1_mem j
  · exact waveExp0_3_mem j
  · exact waveExp0_4_mem j
  · exact waveExp0_7_mem j
  · exact waveExp0_9_mem j
  · exact waveExp0_12_mem j
  · exact waveExp0_13_mem j
  · exact waveExp0_16_mem j
  · exact waveExp0_19_mem j
  · exact waveExp0_21_mem j
  · exact waveExp1_1_mem j
  · exact waveExp1_3_mem j
  · exact waveExp1_4_mem j
  · exact waveExp1_7_mem j
  · exact waveExp1_9_mem j
  · exact waveExp1_12_mem j
  · exact waveExp1_13_mem j
  · exact waveExp1_16_mem j
  · exact waveExp1_19_mem j
  · exact waveExp1_21_mem j

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
lemma jetMultiplierBox_mem (q : Fin 2) (i : Fin 20) (j : Fin 31) : (jetMultiplierBox q i j).Mem
    (jetMultiplier (damping q) H (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (frequency j)) := by
  let n : Fin 10 := ⟨i.val/2,by omega⟩
  have hq := CI.mem_ofReal (RI.mem_invPos (QTable_mem n) (QTable_pos n))
  have he := waveExpTable_mem q n j
  have hp := phaseHTable_mem q j
  have hh := CI.mem_mul (CI.mem_mul hq (lambdaTable_mem q j)) he
  unfold jetMultiplier transformedWave
  rw [← mul_assoc,← Complex.ofReal_inv]
  change ((jetMultiplierBox q i j)).Mem _
  unfold jetMultiplierBox
  split_ifs with hi
  · simpa only [damping, Fin.val_one, one_ne_zero, ↓reduceIte, Fin.val_mk, hi,
      Complex.ofReal_intCast, Int.cast_neg, Int.cast_ofNat, Nat.cast_one, Int.cast_one] using CI.mem_mul hh (CI.mem_point (-1))
  · simpa only [damping, Fin.val_one, one_ne_zero, ↓reduceIte, Fin.val_mk, hi] using
      CI.mem_mul hh (CI.mem_sub (CI.mem_ofReal (DTable_mem n)) hp)

lemma jetTable0_0_mem (j : Fin 31) : (jetTable0_0 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨0,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_0_calc]
  exact jetMultiplierBox_mem 0 0 j
lemma jetTable0_1_mem (j : Fin 31) : (jetTable0_1 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨0,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_1_calc]
  exact jetMultiplierBox_mem 0 1 j
lemma jetTable0_2_mem (j : Fin 31) : (jetTable0_2 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨1,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_2_calc]
  exact jetMultiplierBox_mem 0 2 j
lemma jetTable0_3_mem (j : Fin 31) : (jetTable0_3 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨1,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_3_calc]
  exact jetMultiplierBox_mem 0 3 j
lemma jetTable0_4_mem (j : Fin 31) : (jetTable0_4 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨2,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_4_calc]
  exact jetMultiplierBox_mem 0 4 j
lemma jetTable0_5_mem (j : Fin 31) : (jetTable0_5 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨2,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_5_calc]
  exact jetMultiplierBox_mem 0 5 j
lemma jetTable0_6_mem (j : Fin 31) : (jetTable0_6 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨3,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_6_calc]
  exact jetMultiplierBox_mem 0 6 j
lemma jetTable0_7_mem (j : Fin 31) : (jetTable0_7 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨3,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_7_calc]
  exact jetMultiplierBox_mem 0 7 j
lemma jetTable0_8_mem (j : Fin 31) : (jetTable0_8 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨4,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_8_calc]
  exact jetMultiplierBox_mem 0 8 j
lemma jetTable0_9_mem (j : Fin 31) : (jetTable0_9 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨4,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_9_calc]
  exact jetMultiplierBox_mem 0 9 j
lemma jetTable0_10_mem (j : Fin 31) : (jetTable0_10 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨5,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_10_calc]
  exact jetMultiplierBox_mem 0 10 j
lemma jetTable0_11_mem (j : Fin 31) : (jetTable0_11 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨5,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_11_calc]
  exact jetMultiplierBox_mem 0 11 j
lemma jetTable0_12_mem (j : Fin 31) : (jetTable0_12 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨6,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_12_calc]
  exact jetMultiplierBox_mem 0 12 j
lemma jetTable0_13_mem (j : Fin 31) : (jetTable0_13 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨6,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_13_calc]
  exact jetMultiplierBox_mem 0 13 j
lemma jetTable0_14_mem (j : Fin 31) : (jetTable0_14 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨7,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_14_calc]
  exact jetMultiplierBox_mem 0 14 j
lemma jetTable0_15_mem (j : Fin 31) : (jetTable0_15 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨7,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_15_calc]
  exact jetMultiplierBox_mem 0 15 j
lemma jetTable0_16_mem (j : Fin 31) : (jetTable0_16 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨8,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_16_calc]
  exact jetMultiplierBox_mem 0 16 j
lemma jetTable0_17_mem (j : Fin 31) : (jetTable0_17 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨8,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_17_calc]
  exact jetMultiplierBox_mem 0 17 j
lemma jetTable0_18_mem (j : Fin 31) : (jetTable0_18 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨9,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_18_calc]
  exact jetMultiplierBox_mem 0 18 j
lemma jetTable0_19_mem (j : Fin 31) : (jetTable0_19 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨9,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_19_calc]
  exact jetMultiplierBox_mem 0 19 j
lemma jetTable1_0_mem (j : Fin 31) : (jetTable1_0 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨0,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_0_calc]
  exact jetMultiplierBox_mem 1 0 j
lemma jetTable1_1_mem (j : Fin 31) : (jetTable1_1 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨0,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_1_calc]
  exact jetMultiplierBox_mem 1 1 j
lemma jetTable1_2_mem (j : Fin 31) : (jetTable1_2 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨1,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_2_calc]
  exact jetMultiplierBox_mem 1 2 j
lemma jetTable1_3_mem (j : Fin 31) : (jetTable1_3 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨1,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_3_calc]
  exact jetMultiplierBox_mem 1 3 j
lemma jetTable1_4_mem (j : Fin 31) : (jetTable1_4 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨2,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_4_calc]
  exact jetMultiplierBox_mem 1 4 j
lemma jetTable1_5_mem (j : Fin 31) : (jetTable1_5 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨2,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_5_calc]
  exact jetMultiplierBox_mem 1 5 j
lemma jetTable1_6_mem (j : Fin 31) : (jetTable1_6 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨3,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_6_calc]
  exact jetMultiplierBox_mem 1 6 j
lemma jetTable1_7_mem (j : Fin 31) : (jetTable1_7 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨3,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_7_calc]
  exact jetMultiplierBox_mem 1 7 j
lemma jetTable1_8_mem (j : Fin 31) : (jetTable1_8 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨4,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_8_calc]
  exact jetMultiplierBox_mem 1 8 j
lemma jetTable1_9_mem (j : Fin 31) : (jetTable1_9 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨4,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_9_calc]
  exact jetMultiplierBox_mem 1 9 j
lemma jetTable1_10_mem (j : Fin 31) : (jetTable1_10 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨5,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_10_calc]
  exact jetMultiplierBox_mem 1 10 j
lemma jetTable1_11_mem (j : Fin 31) : (jetTable1_11 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨5,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_11_calc]
  exact jetMultiplierBox_mem 1 11 j
lemma jetTable1_12_mem (j : Fin 31) : (jetTable1_12 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨6,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_12_calc]
  exact jetMultiplierBox_mem 1 12 j
lemma jetTable1_13_mem (j : Fin 31) : (jetTable1_13 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨6,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_13_calc]
  exact jetMultiplierBox_mem 1 13 j
lemma jetTable1_14_mem (j : Fin 31) : (jetTable1_14 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨7,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_14_calc]
  exact jetMultiplierBox_mem 1 14 j
lemma jetTable1_15_mem (j : Fin 31) : (jetTable1_15 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨7,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_15_calc]
  exact jetMultiplierBox_mem 1 15 j
lemma jetTable1_16_mem (j : Fin 31) : (jetTable1_16 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨8,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_16_calc]
  exact jetMultiplierBox_mem 1 16 j
lemma jetTable1_17_mem (j : Fin 31) : (jetTable1_17 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨8,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_17_calc]
  exact jetMultiplierBox_mem 1 17 j
lemma jetTable1_18_mem (j : Fin 31) : (jetTable1_18 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨9,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_18_calc]
  exact jetMultiplierBox_mem 1 18 j
lemma jetTable1_19_mem (j : Fin 31) : (jetTable1_19 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨9,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_19_calc]
  exact jetMultiplierBox_mem 1 19 j
lemma jetTable_mem (q : Fin 2) (i : Fin 20) (j : Fin 31) : (jetTable q i j).Mem
    (jetMultiplier (damping q) H (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (frequency j)) := by
  fin_cases q <;> fin_cases i
  · exact jetTable0_0_mem j
  · exact jetTable0_1_mem j
  · exact jetTable0_2_mem j
  · exact jetTable0_3_mem j
  · exact jetTable0_4_mem j
  · exact jetTable0_5_mem j
  · exact jetTable0_6_mem j
  · exact jetTable0_7_mem j
  · exact jetTable0_8_mem j
  · exact jetTable0_9_mem j
  · exact jetTable0_10_mem j
  · exact jetTable0_11_mem j
  · exact jetTable0_12_mem j
  · exact jetTable0_13_mem j
  · exact jetTable0_14_mem j
  · exact jetTable0_15_mem j
  · exact jetTable0_16_mem j
  · exact jetTable0_17_mem j
  · exact jetTable0_18_mem j
  · exact jetTable0_19_mem j
  · exact jetTable1_0_mem j
  · exact jetTable1_1_mem j
  · exact jetTable1_2_mem j
  · exact jetTable1_3_mem j
  · exact jetTable1_4_mem j
  · exact jetTable1_5_mem j
  · exact jetTable1_6_mem j
  · exact jetTable1_7_mem j
  · exact jetTable1_8_mem j
  · exact jetTable1_9_mem j
  · exact jetTable1_10_mem j
  · exact jetTable1_11_mem j
  · exact jetTable1_12_mem j
  · exact jetTable1_13_mem j
  · exact jetTable1_14_mem j
  · exact jetTable1_15_mem j
  · exact jetTable1_16_mem j
  · exact jetTable1_17_mem j
  · exact jetTable1_18_mem j
  · exact jetTable1_19_mem j
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
lemma fullJetBox_mem (i : Fin 20) (col : Fin 23) : (fullJetBox i col).Mem (fullJetMatrix i col) := by
  have hh := (CI.mem_sum (fun j => CI.mem_mul (jetTable_mem (if col.val=22 then 0 else 1) i j)
    (columnTable_mem col j))).1
  by_cases hc : col.val=22
  · simpa [fullJetBox, fullJetMatrix, jet, damping, hc] using hh
  · simpa [fullJetBox, fullJetMatrix, jet, damping, hc] using hh

lemma fullJetRow0_mem (col : Fin 23) : (fullJetRow0 col).Mem (fullJetMatrix 0 col) := by
  rw [← fullJetRow0_calc]
  exact fullJetBox_mem 0 col
lemma fullJetRow1_mem (col : Fin 23) : (fullJetRow1 col).Mem (fullJetMatrix 1 col) := by
  rw [← fullJetRow1_calc]
  exact fullJetBox_mem 1 col
lemma fullJetRow2_mem (col : Fin 23) : (fullJetRow2 col).Mem (fullJetMatrix 2 col) := by
  rw [← fullJetRow2_calc]
  exact fullJetBox_mem 2 col
lemma fullJetRow3_mem (col : Fin 23) : (fullJetRow3 col).Mem (fullJetMatrix 3 col) := by
  rw [← fullJetRow3_calc]
  exact fullJetBox_mem 3 col
lemma fullJetRow4_mem (col : Fin 23) : (fullJetRow4 col).Mem (fullJetMatrix 4 col) := by
  rw [← fullJetRow4_calc]
  exact fullJetBox_mem 4 col
lemma fullJetRow5_mem (col : Fin 23) : (fullJetRow5 col).Mem (fullJetMatrix 5 col) := by
  rw [← fullJetRow5_calc]
  exact fullJetBox_mem 5 col
lemma fullJetRow6_mem (col : Fin 23) : (fullJetRow6 col).Mem (fullJetMatrix 6 col) := by
  rw [← fullJetRow6_calc]
  exact fullJetBox_mem 6 col
lemma fullJetRow7_mem (col : Fin 23) : (fullJetRow7 col).Mem (fullJetMatrix 7 col) := by
  rw [← fullJetRow7_calc]
  exact fullJetBox_mem 7 col
lemma fullJetRow8_mem (col : Fin 23) : (fullJetRow8 col).Mem (fullJetMatrix 8 col) := by
  rw [← fullJetRow8_calc]
  exact fullJetBox_mem 8 col
lemma fullJetRow9_mem (col : Fin 23) : (fullJetRow9 col).Mem (fullJetMatrix 9 col) := by
  rw [← fullJetRow9_calc]
  exact fullJetBox_mem 9 col
lemma fullJetRow10_mem (col : Fin 23) : (fullJetRow10 col).Mem (fullJetMatrix 10 col) := by
  rw [← fullJetRow10_calc]
  exact fullJetBox_mem 10 col
lemma fullJetRow11_mem (col : Fin 23) : (fullJetRow11 col).Mem (fullJetMatrix 11 col) := by
  rw [← fullJetRow11_calc]
  exact fullJetBox_mem 11 col
lemma fullJetRow12_mem (col : Fin 23) : (fullJetRow12 col).Mem (fullJetMatrix 12 col) := by
  rw [← fullJetRow12_calc]
  exact fullJetBox_mem 12 col
lemma fullJetRow13_mem (col : Fin 23) : (fullJetRow13 col).Mem (fullJetMatrix 13 col) := by
  rw [← fullJetRow13_calc]
  exact fullJetBox_mem 13 col
lemma fullJetRow14_mem (col : Fin 23) : (fullJetRow14 col).Mem (fullJetMatrix 14 col) := by
  rw [← fullJetRow14_calc]
  exact fullJetBox_mem 14 col
lemma fullJetRow15_mem (col : Fin 23) : (fullJetRow15 col).Mem (fullJetMatrix 15 col) := by
  rw [← fullJetRow15_calc]
  exact fullJetBox_mem 15 col
lemma fullJetRow16_mem (col : Fin 23) : (fullJetRow16 col).Mem (fullJetMatrix 16 col) := by
  rw [← fullJetRow16_calc]
  exact fullJetBox_mem 16 col
lemma fullJetRow17_mem (col : Fin 23) : (fullJetRow17 col).Mem (fullJetMatrix 17 col) := by
  rw [← fullJetRow17_calc]
  exact fullJetBox_mem 17 col
lemma fullJetRow18_mem (col : Fin 23) : (fullJetRow18 col).Mem (fullJetMatrix 18 col) := by
  rw [← fullJetRow18_calc]
  exact fullJetBox_mem 18 col
lemma fullJetRow19_mem (col : Fin 23) : (fullJetRow19 col).Mem (fullJetMatrix 19 col) := by
  rw [← fullJetRow19_calc]
  exact fullJetBox_mem 19 col
lemma jetMatrixTable_mem (i : Fin 20) (col : Fin 23) : (jetMatrixTable i col).Mem (fullJetMatrix i col) := by
  fin_cases i
  · exact fullJetRow0_mem col
  · exact fullJetRow1_mem col
  · exact fullJetRow2_mem col
  · exact fullJetRow3_mem col
  · exact fullJetRow4_mem col
  · exact fullJetRow5_mem col
  · exact fullJetRow6_mem col
  · exact fullJetRow7_mem col
  · exact fullJetRow8_mem col
  · exact fullJetRow9_mem col
  · exact fullJetRow10_mem col
  · exact fullJetRow11_mem col
  · exact fullJetRow12_mem col
  · exact fullJetRow13_mem col
  · exact fullJetRow14_mem col
  · exact fullJetRow15_mem col
  · exact fullJetRow16_mem col
  · exact fullJetRow17_mem col
  · exact fullJetRow18_mem col
  · exact fullJetRow19_mem col
lemma RBox_mem (i j : Fin 20) : (RBox i j).Mem (Construction.R i j) := jetMatrixTable_mem i ⟨j.val+2,by omega⟩
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
lemma minusBlockBox_mem (i j : Fin 20) : (minusBlockBox i j).Mem ((1 - Construction.R) i j) :=
  RI.mem_sub (matrixOne_mem i j) (RBox_mem i j)
lemma minusResidualBox_mem (i j : Fin 20) :
    (minusResidualBox i j).Mem ((minusApprox*(1 - Construction.R)-1) i j) :=
  RI.mem_sub (matrixMul_mem minusApproxBox_mem minusBlockBox_mem i j) (matrixOne_mem i j)
lemma minusResidualRow0_calc (j : Fin 20) : minusResidualBox 0 j = minusResidualRow0 j := by
  revert j
  decide +kernel
lemma minusResidualRow0_mem (j : Fin 20) :
    (minusResidualRow0 j).Mem ((minusApprox*(1 - Construction.R)-1) 0 j) := by
  rw [← minusResidualRow0_calc]
  exact minusResidualBox_mem 0 j
lemma minusResidualRow1_calc (j : Fin 20) : minusResidualBox 1 j = minusResidualRow1 j := by
  revert j
  decide +kernel
lemma minusResidualRow1_mem (j : Fin 20) :
    (minusResidualRow1 j).Mem ((minusApprox*(1 - Construction.R)-1) 1 j) := by
  rw [← minusResidualRow1_calc]
  exact minusResidualBox_mem 1 j
lemma minusResidualRow2_calc (j : Fin 20) : minusResidualBox 2 j = minusResidualRow2 j := by
  revert j
  decide +kernel
lemma minusResidualRow2_mem (j : Fin 20) :
    (minusResidualRow2 j).Mem ((minusApprox*(1 - Construction.R)-1) 2 j) := by
  rw [← minusResidualRow2_calc]
  exact minusResidualBox_mem 2 j
lemma minusResidualRow3_calc (j : Fin 20) : minusResidualBox 3 j = minusResidualRow3 j := by
  revert j
  decide +kernel
lemma minusResidualRow3_mem (j : Fin 20) :
    (minusResidualRow3 j).Mem ((minusApprox*(1 - Construction.R)-1) 3 j) := by
  rw [← minusResidualRow3_calc]
  exact minusResidualBox_mem 3 j
lemma minusResidualRow4_calc (j : Fin 20) : minusResidualBox 4 j = minusResidualRow4 j := by
  revert j
  decide +kernel
lemma minusResidualRow4_mem (j : Fin 20) :
    (minusResidualRow4 j).Mem ((minusApprox*(1 - Construction.R)-1) 4 j) := by
  rw [← minusResidualRow4_calc]
  exact minusResidualBox_mem 4 j
lemma minusResidualRow5_calc (j : Fin 20) : minusResidualBox 5 j = minusResidualRow5 j := by
  revert j
  decide +kernel
lemma minusResidualRow5_mem (j : Fin 20) :
    (minusResidualRow5 j).Mem ((minusApprox*(1 - Construction.R)-1) 5 j) := by
  rw [← minusResidualRow5_calc]
  exact minusResidualBox_mem 5 j
lemma minusResidualRow6_calc (j : Fin 20) : minusResidualBox 6 j = minusResidualRow6 j := by
  revert j
  decide +kernel
lemma minusResidualRow6_mem (j : Fin 20) :
    (minusResidualRow6 j).Mem ((minusApprox*(1 - Construction.R)-1) 6 j) := by
  rw [← minusResidualRow6_calc]
  exact minusResidualBox_mem 6 j
lemma minusResidualRow7_calc (j : Fin 20) : minusResidualBox 7 j = minusResidualRow7 j := by
  revert j
  decide +kernel
lemma minusResidualRow7_mem (j : Fin 20) :
    (minusResidualRow7 j).Mem ((minusApprox*(1 - Construction.R)-1) 7 j) := by
  rw [← minusResidualRow7_calc]
  exact minusResidualBox_mem 7 j
lemma minusResidualRow8_calc (j : Fin 20) : minusResidualBox 8 j = minusResidualRow8 j := by
  revert j
  decide +kernel
lemma minusResidualRow8_mem (j : Fin 20) :
    (minusResidualRow8 j).Mem ((minusApprox*(1 - Construction.R)-1) 8 j) := by
  rw [← minusResidualRow8_calc]
  exact minusResidualBox_mem 8 j
lemma minusResidualRow9_calc (j : Fin 20) : minusResidualBox 9 j = minusResidualRow9 j := by
  revert j
  decide +kernel
lemma minusResidualRow9_mem (j : Fin 20) :
    (minusResidualRow9 j).Mem ((minusApprox*(1 - Construction.R)-1) 9 j) := by
  rw [← minusResidualRow9_calc]
  exact minusResidualBox_mem 9 j
lemma minusResidualRow10_calc (j : Fin 20) : minusResidualBox 10 j = minusResidualRow10 j := by
  revert j
  decide +kernel
lemma minusResidualRow10_mem (j : Fin 20) :
    (minusResidualRow10 j).Mem ((minusApprox*(1 - Construction.R)-1) 10 j) := by
  rw [← minusResidualRow10_calc]
  exact minusResidualBox_mem 10 j
lemma minusResidualRow11_calc (j : Fin 20) : minusResidualBox 11 j = minusResidualRow11 j := by
  revert j
  decide +kernel
lemma minusResidualRow11_mem (j : Fin 20) :
    (minusResidualRow11 j).Mem ((minusApprox*(1 - Construction.R)-1) 11 j) := by
  rw [← minusResidualRow11_calc]
  exact minusResidualBox_mem 11 j
lemma minusResidualRow12_calc (j : Fin 20) : minusResidualBox 12 j = minusResidualRow12 j := by
  revert j
  decide +kernel
lemma minusResidualRow12_mem (j : Fin 20) :
    (minusResidualRow12 j).Mem ((minusApprox*(1 - Construction.R)-1) 12 j) := by
  rw [← minusResidualRow12_calc]
  exact minusResidualBox_mem 12 j
lemma minusResidualRow13_calc (j : Fin 20) : minusResidualBox 13 j = minusResidualRow13 j := by
  revert j
  decide +kernel
lemma minusResidualRow13_mem (j : Fin 20) :
    (minusResidualRow13 j).Mem ((minusApprox*(1 - Construction.R)-1) 13 j) := by
  rw [← minusResidualRow13_calc]
  exact minusResidualBox_mem 13 j
lemma minusResidualRow14_calc (j : Fin 20) : minusResidualBox 14 j = minusResidualRow14 j := by
  revert j
  decide +kernel
lemma minusResidualRow14_mem (j : Fin 20) :
    (minusResidualRow14 j).Mem ((minusApprox*(1 - Construction.R)-1) 14 j) := by
  rw [← minusResidualRow14_calc]
  exact minusResidualBox_mem 14 j
lemma minusResidualRow15_calc (j : Fin 20) : minusResidualBox 15 j = minusResidualRow15 j := by
  revert j
  decide +kernel
lemma minusResidualRow15_mem (j : Fin 20) :
    (minusResidualRow15 j).Mem ((minusApprox*(1 - Construction.R)-1) 15 j) := by
  rw [← minusResidualRow15_calc]
  exact minusResidualBox_mem 15 j
lemma minusResidualRow16_calc (j : Fin 20) : minusResidualBox 16 j = minusResidualRow16 j := by
  revert j
  decide +kernel
lemma minusResidualRow16_mem (j : Fin 20) :
    (minusResidualRow16 j).Mem ((minusApprox*(1 - Construction.R)-1) 16 j) := by
  rw [← minusResidualRow16_calc]
  exact minusResidualBox_mem 16 j
lemma minusResidualRow17_calc (j : Fin 20) : minusResidualBox 17 j = minusResidualRow17 j := by
  revert j
  decide +kernel
lemma minusResidualRow17_mem (j : Fin 20) :
    (minusResidualRow17 j).Mem ((minusApprox*(1 - Construction.R)-1) 17 j) := by
  rw [← minusResidualRow17_calc]
  exact minusResidualBox_mem 17 j
lemma minusResidualRow18_calc (j : Fin 20) : minusResidualBox 18 j = minusResidualRow18 j := by
  revert j
  decide +kernel
lemma minusResidualRow18_mem (j : Fin 20) :
    (minusResidualRow18 j).Mem ((minusApprox*(1 - Construction.R)-1) 18 j) := by
  rw [← minusResidualRow18_calc]
  exact minusResidualBox_mem 18 j
lemma minusResidualRow19_calc (j : Fin 20) : minusResidualBox 19 j = minusResidualRow19 j := by
  revert j
  decide +kernel
lemma minusResidualRow19_mem (j : Fin 20) :
    (minusResidualRow19 j).Mem ((minusApprox*(1 - Construction.R)-1) 19 j) := by
  rw [← minusResidualRow19_calc]
  exact minusResidualBox_mem 19 j
lemma minusResidualTable_mem (i j : Fin 20) :
    (minusResidualTable i j).Mem ((minusApprox*(1 - Construction.R)-1) i j) := by
  fin_cases i
  · exact minusResidualRow0_mem j
  · exact minusResidualRow1_mem j
  · exact minusResidualRow2_mem j
  · exact minusResidualRow3_mem j
  · exact minusResidualRow4_mem j
  · exact minusResidualRow5_mem j
  · exact minusResidualRow6_mem j
  · exact minusResidualRow7_mem j
  · exact minusResidualRow8_mem j
  · exact minusResidualRow9_mem j
  · exact minusResidualRow10_mem j
  · exact minusResidualRow11_mem j
  · exact minusResidualRow12_mem j
  · exact minusResidualRow13_mem j
  · exact minusResidualRow14_mem j
  · exact minusResidualRow15_mem j
  · exact minusResidualRow16_mem j
  · exact minusResidualRow17_mem j
  · exact minusResidualRow18_mem j
  · exact minusResidualRow19_mem j
lemma minusResidual_bound : matNorm (minusApprox*(1 - Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) minusResidualTable_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh ⊢
  exact hh
lemma minusBlock_isUnit : IsUnit (1 - Construction.R) :=
  isUnit_of_residual _ minusApprox (minusResidual_bound.trans_lt (by norm_num))
lemma minusInverse_bound : matNorm (1 - Construction.R)⁻¹ < (1616/100:ℝ) := by
  exact (inverse_bound_of_residual _ _ (16155/1000) ((1:ℝ)/10^26)
    minusApprox_bound minusResidual_bound (by norm_num) (by norm_num)).trans_lt (by norm_num)
lemma plusBlockBox_mem (i j : Fin 20) : (plusBlockBox i j).Mem ((1 + Construction.R) i j) :=
  RI.mem_add (matrixOne_mem i j) (RBox_mem i j)
lemma plusResidualBox_mem (i j : Fin 20) :
    (plusResidualBox i j).Mem ((plusApprox*(1 + Construction.R)-1) i j) :=
  RI.mem_sub (matrixMul_mem plusApproxBox_mem plusBlockBox_mem i j) (matrixOne_mem i j)
lemma plusResidualRow0_mem (j : Fin 20) :
    (plusResidualRow0 j).Mem ((plusApprox*(1 + Construction.R)-1) 0 j) := by
  rw [← plusResidualRow0_calc]
  exact plusResidualBox_mem 0 j
lemma plusResidualRow1_mem (j : Fin 20) :
    (plusResidualRow1 j).Mem ((plusApprox*(1 + Construction.R)-1) 1 j) := by
  rw [← plusResidualRow1_calc]
  exact plusResidualBox_mem 1 j
lemma plusResidualRow2_mem (j : Fin 20) :
    (plusResidualRow2 j).Mem ((plusApprox*(1 + Construction.R)-1) 2 j) := by
  rw [← plusResidualRow2_calc]
  exact plusResidualBox_mem 2 j
lemma plusResidualRow3_mem (j : Fin 20) :
    (plusResidualRow3 j).Mem ((plusApprox*(1 + Construction.R)-1) 3 j) := by
  rw [← plusResidualRow3_calc]
  exact plusResidualBox_mem 3 j
lemma plusResidualRow4_mem (j : Fin 20) :
    (plusResidualRow4 j).Mem ((plusApprox*(1 + Construction.R)-1) 4 j) := by
  rw [← plusResidualRow4_calc]
  exact plusResidualBox_mem 4 j
lemma plusResidualRow5_mem (j : Fin 20) :
    (plusResidualRow5 j).Mem ((plusApprox*(1 + Construction.R)-1) 5 j) := by
  rw [← plusResidualRow5_calc]
  exact plusResidualBox_mem 5 j
lemma plusResidualRow6_mem (j : Fin 20) :
    (plusResidualRow6 j).Mem ((plusApprox*(1 + Construction.R)-1) 6 j) := by
  rw [← plusResidualRow6_calc]
  exact plusResidualBox_mem 6 j
lemma plusResidualRow7_mem (j : Fin 20) :
    (plusResidualRow7 j).Mem ((plusApprox*(1 + Construction.R)-1) 7 j) := by
  rw [← plusResidualRow7_calc]
  exact plusResidualBox_mem 7 j
lemma plusResidualRow8_mem (j : Fin 20) :
    (plusResidualRow8 j).Mem ((plusApprox*(1 + Construction.R)-1) 8 j) := by
  rw [← plusResidualRow8_calc]
  exact plusResidualBox_mem 8 j
lemma plusResidualRow9_mem (j : Fin 20) :
    (plusResidualRow9 j).Mem ((plusApprox*(1 + Construction.R)-1) 9 j) := by
  rw [← plusResidualRow9_calc]
  exact plusResidualBox_mem 9 j
lemma plusResidualRow10_mem (j : Fin 20) :
    (plusResidualRow10 j).Mem ((plusApprox*(1 + Construction.R)-1) 10 j) := by
  rw [← plusResidualRow10_calc]
  exact plusResidualBox_mem 10 j
lemma plusResidualRow11_mem (j : Fin 20) :
    (plusResidualRow11 j).Mem ((plusApprox*(1 + Construction.R)-1) 11 j) := by
  rw [← plusResidualRow11_calc]
  exact plusResidualBox_mem 11 j
lemma plusResidualRow12_mem (j : Fin 20) :
    (plusResidualRow12 j).Mem ((plusApprox*(1 + Construction.R)-1) 12 j) := by
  rw [← plusResidualRow12_calc]
  exact plusResidualBox_mem 12 j
lemma plusResidualRow13_mem (j : Fin 20) :
    (plusResidualRow13 j).Mem ((plusApprox*(1 + Construction.R)-1) 13 j) := by
  rw [← plusResidualRow13_calc]
  exact plusResidualBox_mem 13 j
lemma plusResidualRow14_mem (j : Fin 20) :
    (plusResidualRow14 j).Mem ((plusApprox*(1 + Construction.R)-1) 14 j) := by
  rw [← plusResidualRow14_calc]
  exact plusResidualBox_mem 14 j
lemma plusResidualRow15_mem (j : Fin 20) :
    (plusResidualRow15 j).Mem ((plusApprox*(1 + Construction.R)-1) 15 j) := by
  rw [← plusResidualRow15_calc]
  exact plusResidualBox_mem 15 j
lemma plusResidualRow16_mem (j : Fin 20) :
    (plusResidualRow16 j).Mem ((plusApprox*(1 + Construction.R)-1) 16 j) := by
  rw [← plusResidualRow16_calc]
  exact plusResidualBox_mem 16 j
lemma plusResidualRow17_mem (j : Fin 20) :
    (plusResidualRow17 j).Mem ((plusApprox*(1 + Construction.R)-1) 17 j) := by
  rw [← plusResidualRow17_calc]
  exact plusResidualBox_mem 17 j
lemma plusResidualRow18_mem (j : Fin 20) :
    (plusResidualRow18 j).Mem ((plusApprox*(1 + Construction.R)-1) 18 j) := by
  rw [← plusResidualRow18_calc]
  exact plusResidualBox_mem 18 j
lemma plusResidualRow19_mem (j : Fin 20) :
    (plusResidualRow19 j).Mem ((plusApprox*(1 + Construction.R)-1) 19 j) := by
  rw [← plusResidualRow19_calc]
  exact plusResidualBox_mem 19 j
lemma plusResidualTable_mem (i j : Fin 20) :
    (plusResidualTable i j).Mem ((plusApprox*(1 + Construction.R)-1) i j) := by
  fin_cases i
  · exact plusResidualRow0_mem j
  · exact plusResidualRow1_mem j
  · exact plusResidualRow2_mem j
  · exact plusResidualRow3_mem j
  · exact plusResidualRow4_mem j
  · exact plusResidualRow5_mem j
  · exact plusResidualRow6_mem j
  · exact plusResidualRow7_mem j
  · exact plusResidualRow8_mem j
  · exact plusResidualRow9_mem j
  · exact plusResidualRow10_mem j
  · exact plusResidualRow11_mem j
  · exact plusResidualRow12_mem j
  · exact plusResidualRow13_mem j
  · exact plusResidualRow14_mem j
  · exact plusResidualRow15_mem j
  · exact plusResidualRow16_mem j
  · exact plusResidualRow17_mem j
  · exact plusResidualRow18_mem j
  · exact plusResidualRow19_mem j
lemma plusResidual_bound : matNorm (plusApprox*(1 + Construction.R)-1) ≤ (1:ℝ)/10^26 := by
  have hh := matrixNorm_bound (b := 10000000000000000000000000000000000) plusResidualTable_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh ⊢
  exact hh
lemma plusBlock_isUnit : IsUnit (1 + Construction.R) :=
  isUnit_of_residual _ plusApprox (plusResidual_bound.trans_lt (by norm_num))
lemma plusInverse_bound : matNorm (1 + Construction.R)⁻¹ < (389/100:ℝ) := by
  exact (inverse_bound_of_residual _ _ (3885/1000) ((1:ℝ)/10^26)
    plusApprox_bound plusResidual_bound (by norm_num) (by norm_num)).trans_lt (by norm_num)
lemma plusInverse_error : matNorm ((1 + Construction.R)⁻¹-plusApprox) ≤ (1:ℝ)/10^23 := by
  exact (inverse_error_of_residual _ _ (3885/1000) ((1:ℝ)/10^26)
    plusApprox_bound plusResidual_bound (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)

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

def rhsPlusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).add (gammaBox 0 k j)) i j)

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
lemma psiTableD_mem (i : Fin 15) (j : Fin 31) : (psiTableD i j).Mem (normJetEnvelope (damping 0) (damping 0) (tailBase i) (frequency j)) := by
  fin_cases i
  · exact psiD36_mem j
  · exact psiD37_mem j
  · exact psiD39_mem j
  · exact psiD40_mem j
  · exact psiD43_mem j
  · exact psiD45_mem j
  · exact psiD48_mem j
  · exact psiD49_mem j
  · exact psiD52_mem j
  · exact psiD55_mem j
  · exact psiD57_mem j
  · exact psiD25_mem j
  · exact psiD27_mem j
  · exact psiD28_mem j
  · exact psiD31_mem j
lemma envelopeSumBoxD_mem (j : Fin 31) : (envelopeSumBoxD j).Mem (tailEnvelopeSum 0 0 j) := by
  rw [← envelopeSumBoxD_calc]
  exact RI.mem_mul (RI.mem_sum (fun i => psiTableD_mem i j))
    (RI.mem_invPos (RI.mem_sub ri1_mem (periodExpD_mem j)) (periodDenD_pos j))
lemma boundD_mem (c : Fin 2) : (boundD c).Mem (tailTailEnvelope c) := by
  rw [← boundD_calc]
  exact RI.mem_sum (fun i => RI.mem_mul (envelopeSumBoxD_mem _) (fullWTable_mem i c))
lemma tailTailEnvelope_bound (c : Fin 2) : tailTailEnvelope c < (23/1000000000:ℝ) := by
  apply ri_mem_lt (boundD_mem c) 23 1000000000 (by norm_num)
  revert c
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
lemma tail_tail_column_bound (n : ℤ) (c : Fin 2) :
    (∑' p : TailNode × Fin 2, |tailJet h h p.1.val.val n c p.2|) < 23/10^9 := by
  exact (tail_tail_column_bounds 0 0 n c).2.trans_lt (by norm_num [tailTailEnvelope,damping,H,h] at ⊢; simpa [tailTailEnvelope] using FiniteCertificate.tailTailEnvelope_bound c)
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
def Coperator : FiniteCoefficients →L[ℝ] TailCoefficients :=
  operator Ckernel Ckernel_summable (7/10^15) Ckernel_bound
lemma Coperator_norm : ‖Coperator‖ ≤ 7/10^15 := operator_norm _ _ _ (by norm_num) _
lemma Dkernel_bound (q : TailNode × Fin 2) : (∑' p, |Dkernel p q|) ≤ 23/10^9 :=
  (tail_tail_column_bound q.1.val.val q.2).le
def Doperator : TailCoefficients →L[ℝ] TailCoefficients :=
  operator Dkernel Dkernel_summable (23/10^9) Dkernel_bound
lemma Doperator_norm : ‖Doperator‖ ≤ 23/10^9 := operator_norm _ _ _ (by norm_num) _
lemma Lplus_norm : ‖Lplus‖ ≤ 17 :=
  ((l1Matrix_norm _).trans_lt FiniteCertificate.minusInverse_bound).le.trans (by norm_num)
lemma Lminus_norm : ‖Lminus‖ ≤ 5 :=
  ((l1Matrix_norm _).trans_lt FiniteCertificate.plusInverse_bound).le.trans (by norm_num)
lemma Lplus_left_inverse : (1-Roperator).comp Lplus=1 := by
  have hh := (l1Matrix_inverse (1-R) FiniteCertificate.minusBlock_isUnit).1
  simpa [Lplus,l1Matrix_sub,l1Matrix_one,Roperator] using hh
lemma Lminus_left_inverse : (1+Roperator).comp Lminus=1 := by
  have hh := (l1Matrix_inverse (1+R) FiniteCertificate.plusBlock_isUnit).1
  simpa [Lminus,l1Matrix_add,l1Matrix_one,Roperator] using hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_RepetitionOperators
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

def splitK (e : Fin 2) : FiniteCoefficients →L[ℝ] TailCoefficients :=
  if e.val=0 then Coperator-Aoperator else -Coperator-Aoperator
def splitD (e : Fin 2) : TailCoefficients →L[ℝ] TailCoefficients :=
  if e.val=0 then Doperator else -Doperator

def correctionTail (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) : TailCoefficients :=
  tailSolution (splitL e) (splitB e) (splitK e) (splitD e) r s
def correctionFinite (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients) : FiniteCoefficients :=
  AtomicTriangular.Schur.finiteSolution (splitL e) (splitB e) (splitK e) (splitD e) r s
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualCorrection
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

def actualTailSplit (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  correctionTail e (finiteResidual z) (approximationTailResidual e z hz hzB)
def actualFiniteSplit (e : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : FiniteCoefficients :=
  correctionFinite e (finiteResidual z) (approximationTailResidual e z hz hzB)

def actualTail (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : TailCoefficients :=
  (1/2:ℝ) • (actualTailSplit 0 z hz hzB + (if side.val=0 then actualTailSplit 1 z hz hzB else -actualTailSplit 1 z hz hzB))
def actualFiniteError (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : FiniteCoefficients :=
  (1/2:ℝ) • (actualFiniteSplit 0 z hz hzB + (if side.val=0 then actualFiniteSplit 1 z hz hzB else -actualFiniteSplit 1 z hz hzB))
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma correctionFinite_plus (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionFinite 0 r s = Roperator (correctionFinite 0 r s)+Boperator (correctionTail 0 r s)+r := by
  have hh := congrArg (fun T : FiniteCoefficients →L[ℝ] FiniteCoefficients => T (r+Boperator (correctionTail 0 r s))) Lplus_left_inverse
  change correctionFinite 0 r s-Roperator (correctionFinite 0 r s)=r+Boperator (correctionTail 0 r s) at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (by abel)
lemma correctionFinite_minus (r : FiniteCoefficients) (s : TailCoefficients) :
    correctionFinite 1 r s = -Roperator (correctionFinite 1 r s)-Boperator (correctionTail 1 r s)+r := by
  have hh := congrArg (fun T : FiniteCoefficients →L[ℝ] FiniteCoefficients => T (r-Boperator (correctionTail 1 r s))) Lminus_left_inverse
  change correctionFinite 1 r s+Roperator (correctionFinite 1 r s)=r-Boperator (correctionTail 1 r s) at hh
  exact eq_sub_of_add_eq hh |>.trans (by abel)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_ActualTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma CallOperator_extend (u : FiniteCoefficients) :
    CallOperator (extendFiniteError u)=Coperator u := by
  ext p
  unfold CallOperator Coperator
  erw [operator_apply,operator_apply,tsum_fintype,tsum_fintype]
  change (∑ i : Fin 22, (if hi : i.val<2 then 0 else u ⟨i.val-2,by omega⟩)*CallKernel p i)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,show 0<2 by omega,show 0+1<2 by omega,↓reduceDIte,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show ¬(i.val+1+1<2) by omega,↓reduceDIte]
  congr 1
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_FiniteSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Matrix

lemma Uplus_equation : (1-R)*Uplus = Yf+R0*(gamma 1+gamma 0) := by
  unfold Uplus
  apply Matrix.mul_nonsing_inv_cancel_left
  exact (Matrix.isUnit_iff_isUnit_det _).mp FiniteCertificate.minusBlock_isUnit
lemma Uminus_equation : (1+R)*Uminus = Yf+R0*(gamma 1-gamma 0) := by
  unfold Uminus
  apply Matrix.mul_nonsing_inv_cancel_left
  exact (Matrix.isUnit_iff_isUnit_det _).mp FiniteCertificate.plusBlock_isUnit
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorPhase0_0_mem (j : Fin 31) : (taylorPhase0_0 j).Mem (taylorPhase 0 0 (frequency j)) := by
  rw [← taylorPhase0_0_calc]
  exact taylorPhaseBox_mem 0 0 j
lemma taylorPhase0_1_mem (j : Fin 31) : (taylorPhase0_1 j).Mem (taylorPhase 0 1 (frequency j)) := by
  rw [← taylorPhase0_1_calc]
  exact taylorPhaseBox_mem 0 1 j

end AtomicTriangular.FiniteCertificate
end

end OAI
end


