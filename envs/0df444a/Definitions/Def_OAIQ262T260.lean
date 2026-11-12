-- Prove2me | Definitions.Def_OAIQ262T260
-- name    : OAIQ262T260
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T21:15:39.204251+00:00
-- url     : https://prove2.me/theorems/f679f488-33ef-4ea2-a878-2de30a2c6c62
-- title:
--   Definitions bundle OAIQ262T260 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 51 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Signs_RemainderBoxes`, `Triangular_Signs_RemainderData0`, `Triangular_Signs_RemainderData1`, `Triangular_Signs_RemainderData2`, `Triangular_Signs_RemainderData3`, `Triangular_Signs_RemainderData4`, `Triangular_Signs_RemainderData5`, `Triangular_Signs_RemainderSums0`, `Triangular_Signs_RemainderSums1`, `Triangular_Signs_RemainderSums2`, `Triangular_Signs_RemainderSums3`, `Triangular_Signs_RemainderSums4`, `Triangular_Signs_RemainderSums5`, `Triangular_Taylor_TaylorSpectrum`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T160`, `OAIQ262T161`, `OAIQ262T162` and `OAIQ262T253` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T160
import Definitions.Def_OAIQ262T161
import Definitions.Def_OAIQ262T162
import Definitions.Def_OAIQ262T253

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ATable_mem (side : Fin 2) (i : Fin 23) (r : Fin 8) : (ATable side i r).Mem (Acoefficient side i r) := by
  fin_cases side
  · exact A1Table_mem i r
  · exact A2Table_mem i r

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderBox_mem (q br : Fin 2) (n : Fin 7) (j : Fin 31) {dnorm : RI}
    (hd : dnorm.Mem ‖taylorPhase q br (frequency j)‖)
    (hp : (remainderExpInput q br n j).normSq.hi ≤ scale*1024^2)
    (hden : 0<((RI.point 1).sub (((nearRadiusBox n).mul dnorm).divNat 24)).lo) :
    (remainderBox q br n j dnorm).Mem
      (remainderWave q br (nearNode n) (nearRadius n) (frequency j)) := by
  have hs := CI.mem_normSq (taylorPhaseTable_mem q br j)
  rw [Complex.normSq_eq_norm_sq] at hs
  have he := ri_exp_mem (RI.mem_mul (taylorPhaseTable_mem q br j).1 (RI.mem_point (nearNode n))) hp
  have hy := RI.mem_mul (nearRadiusBox_mem n) hd
  have hc := RI.mem_mul (RI.mem_mul hs (amplitudeNormBox_mem q br j)) he
  have hh := RI.mem_mul (RI.mem_divNat (RI.mem_mul hc (RI.mem_pow hy 21)) (by decide : 0<(23).factorial))
    (RI.mem_invPos (RI.mem_sub ri1_mem (RI.mem_divNat hy (by norm_num : 0<24))) hden)
  simpa only [remainderBox,remainderWave,curvatureWave,div_eq_mul_inv,Nat.cast_ofNat,remainderExpInput] using hh
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData0_00_mem (j : Fin 31) : (remainderData0_00 j).Mem (remainderWave 0 0 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_00_calc]
  exact remainderBox_mem 0 0 0 j (taylorNormTable_mem 0 0 j) (remainderData0_00_pre j).1 (remainderData0_00_pre j).2
lemma remainderData0_01_mem (j : Fin 31) : (remainderData0_01 j).Mem (remainderWave 0 1 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_01_calc]
  exact remainderBox_mem 0 1 0 j (taylorNormTable_mem 0 1 j) (remainderData0_01_pre j).1 (remainderData0_01_pre j).2
lemma remainderData0_10_mem (j : Fin 31) : (remainderData0_10 j).Mem (remainderWave 1 0 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_10_calc]
  exact remainderBox_mem 1 0 0 j (taylorNormTable_mem 1 0 j) (remainderData0_10_pre j).1 (remainderData0_10_pre j).2
lemma remainderData0_11_mem (j : Fin 31) : (remainderData0_11 j).Mem (remainderWave 1 1 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_11_calc]
  exact remainderBox_mem 1 1 0 j (taylorNormTable_mem 1 1 j) (remainderData0_11_pre j).1 (remainderData0_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData1_00_mem (j : Fin 31) : (remainderData1_00 j).Mem (remainderWave 0 0 (nearNode 1) (nearRadius 1) (frequency j)) := by
  rw [← remainderData1_00_calc]
  exact remainderBox_mem 0 0 1 j (taylorNormTable_mem 0 0 j) (remainderData1_00_pre j).1 (remainderData1_00_pre j).2
lemma remainderData1_01_mem (j : Fin 31) : (remainderData1_01 j).Mem (remainderWave 0 1 (nearNode 1) (nearRadius 1) (frequency j)) := by
  rw [← remainderData1_01_calc]
  exact remainderBox_mem 0 1 1 j (taylorNormTable_mem 0 1 j) (remainderData1_01_pre j).1 (remainderData1_01_pre j).2
lemma remainderData1_10_mem (j : Fin 31) : (remainderData1_10 j).Mem (remainderWave 1 0 (nearNode 1) (nearRadius 1) (frequency j)) := by
  rw [← remainderData1_10_calc]
  exact remainderBox_mem 1 0 1 j (taylorNormTable_mem 1 0 j) (remainderData1_10_pre j).1 (remainderData1_10_pre j).2
lemma remainderData1_11_mem (j : Fin 31) : (remainderData1_11 j).Mem (remainderWave 1 1 (nearNode 1) (nearRadius 1) (frequency j)) := by
  rw [← remainderData1_11_calc]
  exact remainderBox_mem 1 1 1 j (taylorNormTable_mem 1 1 j) (remainderData1_11_pre j).1 (remainderData1_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_00_mem (j : Fin 31) : (remainderData2_00 j).Mem (remainderWave 0 0 (nearNode 2) (nearRadius 2) (frequency j)) := by
  rw [← remainderData2_00_calc]
  exact remainderBox_mem 0 0 2 j (taylorNormTable_mem 0 0 j) (remainderData2_00_pre j).1 (remainderData2_00_pre j).2
lemma remainderData2_01_mem (j : Fin 31) : (remainderData2_01 j).Mem (remainderWave 0 1 (nearNode 2) (nearRadius 2) (frequency j)) := by
  rw [← remainderData2_01_calc]
  exact remainderBox_mem 0 1 2 j (taylorNormTable_mem 0 1 j) (remainderData2_01_pre j).1 (remainderData2_01_pre j).2
lemma remainderData2_10_mem (j : Fin 31) : (remainderData2_10 j).Mem (remainderWave 1 0 (nearNode 2) (nearRadius 2) (frequency j)) := by
  rw [← remainderData2_10_calc]
  exact remainderBox_mem 1 0 2 j (taylorNormTable_mem 1 0 j) (remainderData2_10_pre j).1 (remainderData2_10_pre j).2
lemma remainderData2_11_mem (j : Fin 31) : (remainderData2_11 j).Mem (remainderWave 1 1 (nearNode 2) (nearRadius 2) (frequency j)) := by
  rw [← remainderData2_11_calc]
  exact remainderBox_mem 1 1 2 j (taylorNormTable_mem 1 1 j) (remainderData2_11_pre j).1 (remainderData2_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData3_00_mem (j : Fin 31) : (remainderData3_00 j).Mem (remainderWave 0 0 (nearNode 3) (nearRadius 3) (frequency j)) := by
  rw [← remainderData3_00_calc]
  exact remainderBox_mem 0 0 3 j (taylorNormTable_mem 0 0 j) (remainderData3_00_pre j).1 (remainderData3_00_pre j).2
lemma remainderData3_01_mem (j : Fin 31) : (remainderData3_01 j).Mem (remainderWave 0 1 (nearNode 3) (nearRadius 3) (frequency j)) := by
  rw [← remainderData3_01_calc]
  exact remainderBox_mem 0 1 3 j (taylorNormTable_mem 0 1 j) (remainderData3_01_pre j).1 (remainderData3_01_pre j).2
lemma remainderData3_10_mem (j : Fin 31) : (remainderData3_10 j).Mem (remainderWave 1 0 (nearNode 3) (nearRadius 3) (frequency j)) := by
  rw [← remainderData3_10_calc]
  exact remainderBox_mem 1 0 3 j (taylorNormTable_mem 1 0 j) (remainderData3_10_pre j).1 (remainderData3_10_pre j).2
lemma remainderData3_11_mem (j : Fin 31) : (remainderData3_11 j).Mem (remainderWave 1 1 (nearNode 3) (nearRadius 3) (frequency j)) := by
  rw [← remainderData3_11_calc]
  exact remainderBox_mem 1 1 3 j (taylorNormTable_mem 1 1 j) (remainderData3_11_pre j).1 (remainderData3_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData4_00_mem (j : Fin 31) : (remainderData4_00 j).Mem (remainderWave 0 0 (nearNode 4) (nearRadius 4) (frequency j)) := by
  rw [← remainderData4_00_calc]
  exact remainderBox_mem 0 0 4 j (taylorNormTable_mem 0 0 j) (remainderData4_00_pre j).1 (remainderData4_00_pre j).2
lemma remainderData4_01_mem (j : Fin 31) : (remainderData4_01 j).Mem (remainderWave 0 1 (nearNode 4) (nearRadius 4) (frequency j)) := by
  rw [← remainderData4_01_calc]
  exact remainderBox_mem 0 1 4 j (taylorNormTable_mem 0 1 j) (remainderData4_01_pre j).1 (remainderData4_01_pre j).2
lemma remainderData4_10_mem (j : Fin 31) : (remainderData4_10 j).Mem (remainderWave 1 0 (nearNode 4) (nearRadius 4) (frequency j)) := by
  rw [← remainderData4_10_calc]
  exact remainderBox_mem 1 0 4 j (taylorNormTable_mem 1 0 j) (remainderData4_10_pre j).1 (remainderData4_10_pre j).2
lemma remainderData4_11_mem (j : Fin 31) : (remainderData4_11 j).Mem (remainderWave 1 1 (nearNode 4) (nearRadius 4) (frequency j)) := by
  rw [← remainderData4_11_calc]
  exact remainderBox_mem 1 1 4 j (taylorNormTable_mem 1 1 j) (remainderData4_11_pre j).1 (remainderData4_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData5_10_mem (j : Fin 31) : (remainderData5_10 j).Mem (remainderWave 1 0 (nearNode 5) (nearRadius 5) (frequency j)) := by
  rw [← remainderData5_10_calc]
  exact remainderBox_mem 1 0 5 j (taylorNormTable_mem 1 0 j) (remainderData5_10_pre j).1 (remainderData5_10_pre j).2
lemma remainderData5_11_mem (j : Fin 31) : (remainderData5_11 j).Mem (remainderWave 1 1 (nearNode 5) (nearRadius 5) (frequency j)) := by
  rw [← remainderData5_11_calc]
  exact remainderBox_mem 1 1 5 j (taylorNormTable_mem 1 1 j) (remainderData5_11_pre j).1 (remainderData5_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns0_0_bound (c : Fin 22) : rawRemainderColumn 0 0 c < (72/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData0_10_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns0_0_calc] at hh
  have hb := ri_mem_lt hh 72 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderColumns0_1_bound (c : Fin 22) : rawRemainderColumn 1 0 c < (27319409896/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData0_11_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns0_1_calc] at hh
  have hb := ri_mem_lt hh 27319409896 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst0_0_bound : rawRemainderConstant 0 0 < (520/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData0_00_mem j) (fourierNorm_mem j))
  rw [remainderConst0_0_calc] at hh
  have hb := ri_mem_lt hh 520 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst0_1_bound : rawRemainderConstant 1 0 < (253857234449457/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData0_01_mem j) (fourierNorm_mem j))
  rw [remainderConst0_1_calc] at hh
  have hb := ri_mem_lt hh 253857234449457 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable0 (c d : Fin 22) : 3*(rawRemainderColumn 0 0 c+rawRemainderColumn 1 0 d)+(6/1000)*(rawRemainderConstant 0 0+rawRemainderConstant 1 0) < (161/100000:ℝ) := by
  have h0 := remainderColumns0_0_bound c
  have h1 := remainderColumns0_1_bound d
  have h2 := remainderConst0_0_bound
  have h3 := remainderConst0_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns1_0_bound (c : Fin 22) : rawRemainderColumn 0 1 c < (21/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData1_10_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns1_0_calc] at hh
  have hb := ri_mem_lt hh 21 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderColumns1_1_bound (c : Fin 22) : rawRemainderColumn 1 1 c < (1304809/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData1_11_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns1_1_calc] at hh
  have hb := ri_mem_lt hh 1304809 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst1_0_bound : rawRemainderConstant 0 1 < (520/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData1_00_mem j) (fourierNorm_mem j))
  rw [remainderConst1_0_calc] at hh
  have hb := ri_mem_lt hh 520 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst1_1_bound : rawRemainderConstant 1 1 < (2220946915/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData1_01_mem j) (fourierNorm_mem j))
  rw [remainderConst1_1_calc] at hh
  have hb := ri_mem_lt hh 2220946915 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable1 (c d : Fin 22) : 3*(rawRemainderColumn 0 1 c+rawRemainderColumn 1 1 d)+(6/1000)*(rawRemainderConstant 0 1+rawRemainderConstant 1 1) < (75/10000000:ℝ) := by
  have h0 := remainderColumns1_0_bound c
  have h1 := remainderColumns1_1_bound d
  have h2 := remainderConst1_0_bound
  have h3 := remainderConst1_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns2_0_bound (c : Fin 22) : rawRemainderColumn 0 2 c < (57439/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData2_10_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns2_0_calc] at hh
  have hb := ri_mem_lt hh 57439 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderColumns2_1_bound (c : Fin 22) : rawRemainderColumn 1 2 c < (406492932/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData2_11_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns2_1_calc] at hh
  have hb := ri_mem_lt hh 406492932 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst2_0_bound : rawRemainderConstant 0 2 < (2754364/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData2_00_mem j) (fourierNorm_mem j))
  rw [remainderConst2_0_calc] at hh
  have hb := ri_mem_lt hh 2754364 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst2_1_bound : rawRemainderConstant 1 2 < (1040413389772/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData2_01_mem j) (fourierNorm_mem j))
  rw [remainderConst2_1_calc] at hh
  have hb := ri_mem_lt hh 1040413389772 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable2 (c d : Fin 22) : 3*(rawRemainderColumn 0 2 c+rawRemainderColumn 1 2 d)+(6/1000)*(rawRemainderConstant 0 2+rawRemainderConstant 1 2) < (75/10000000:ℝ) := by
  have h0 := remainderColumns2_0_bound c
  have h1 := remainderColumns2_1_bound d
  have h2 := remainderConst2_0_bound
  have h3 := remainderConst2_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns3_0_bound (c : Fin 22) : rawRemainderColumn 0 3 c < (8722/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData3_10_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns3_0_calc] at hh
  have hb := ri_mem_lt hh 8722 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderColumns3_1_bound (c : Fin 22) : rawRemainderColumn 1 3 c < (1033019/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData3_11_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns3_1_calc] at hh
  have hb := ri_mem_lt hh 1033019 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst3_0_bound : rawRemainderConstant 0 3 < (2754364/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData3_00_mem j) (fourierNorm_mem j))
  rw [remainderConst3_0_calc] at hh
  have hb := ri_mem_lt hh 2754364 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst3_1_bound : rawRemainderConstant 1 3 < (12287957045/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData3_01_mem j) (fourierNorm_mem j))
  rw [remainderConst3_1_calc] at hh
  have hb := ri_mem_lt hh 12287957045 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable3 (c d : Fin 22) : 3*(rawRemainderColumn 0 3 c+rawRemainderColumn 1 3 d)+(6/1000)*(rawRemainderConstant 0 3+rawRemainderConstant 1 3) < (75/10000000:ℝ) := by
  have h0 := remainderColumns3_0_bound c
  have h1 := remainderColumns3_1_bound d
  have h2 := remainderConst3_0_bound
  have h3 := remainderConst3_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns4_0_bound (c : Fin 22) : rawRemainderColumn 0 4 c < (2483/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData4_10_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns4_0_calc] at hh
  have hb := ri_mem_lt hh 2483 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderColumns4_1_bound (c : Fin 22) : rawRemainderColumn 1 4 c < (44313/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData4_11_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns4_1_calc] at hh
  have hb := ri_mem_lt hh 44313 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst4_0_bound : rawRemainderConstant 0 4 < (2754364/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData4_00_mem j) (fourierNorm_mem j))
  rw [remainderConst4_0_calc] at hh
  have hb := ri_mem_lt hh 2754364 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst4_1_bound : rawRemainderConstant 1 4 < (1761620613/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData4_01_mem j) (fourierNorm_mem j))
  rw [remainderConst4_1_calc] at hh
  have hb := ri_mem_lt hh 1761620613 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable4 (c d : Fin 22) : 3*(rawRemainderColumn 0 4 c+rawRemainderColumn 1 4 d)+(6/1000)*(rawRemainderConstant 0 4+rawRemainderConstant 1 4) < (75/10000000:ℝ) := by
  have h0 := remainderColumns4_0_bound c
  have h1 := remainderColumns4_1_bound d
  have h2 := remainderConst4_0_bound
  have h3 := remainderConst4_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns5_0_bound (c : Fin 22) : rawRemainderColumn 0 5 c < (377/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData5_10_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns5_0_calc] at hh
  have hb := ri_mem_lt hh 377 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderColumns5_1_bound (c : Fin 22) : rawRemainderColumn 1 5 c < (624/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData5_11_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns5_1_calc] at hh
  have hb := ri_mem_lt hh 624 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
end AtomicTriangular.FiniteCertificate
end

end OAI
end


