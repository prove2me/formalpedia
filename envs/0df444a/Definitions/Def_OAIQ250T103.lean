-- Prove2me | Definitions.Def_OAIQ250T103
-- name    : OAIQ250T103
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:47:08.076578+00:00
-- url     : https://prove2.me/theorems/b4ffaa6b-32fe-4ceb-9172-97df97bef0fd
-- title:
--   Definitions bundle OAIQ250T103 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 60 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_ParamU`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Construction_CurvatureBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureBoxes.lean), [`Triangular_Construction_CurvatureSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureSums.lean), [`Triangular_Taylor_CurvatureData10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/CurvatureData10.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T083`, `OAIQ250T084` and `OAIQ250T151` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T112` and `OAIQ250T113`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T083
import Definitions.Def_OAIQ250T084
import Definitions.Def_OAIQ250T151

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
lemma fullJetRow2_calc (col : Fin 23) : fullJetBox 2 col = fullJetRow2 col := by
  revert col
  decide +kernel
lemma fullJetRow3_calc (col : Fin 23) : fullJetBox 3 col = fullJetRow3 col := by
  revert col
  decide +kernel
lemma fullJetRow4_calc (col : Fin 23) : fullJetBox 4 col = fullJetRow4 col := by
  revert col
  decide +kernel
lemma fullJetRow5_calc (col : Fin 23) : fullJetBox 5 col = fullJetRow5 col := by
  revert col
  decide +kernel
lemma fullJetRow6_calc (col : Fin 23) : fullJetBox 6 col = fullJetRow6 col := by
  revert col
  decide +kernel
lemma fullJetRow7_calc (col : Fin 23) : fullJetBox 7 col = fullJetRow7 col := by
  revert col
  decide +kernel
lemma fullJetRow8_calc (col : Fin 23) : fullJetBox 8 col = fullJetRow8 col := by
  revert col
  decide +kernel
lemma fullJetRow9_calc (col : Fin 23) : fullJetBox 9 col = fullJetRow9 col := by
  revert col
  decide +kernel
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
lemma minusApprox_bound : matNorm minusApprox ≤ (16155/1000:ℝ) := by
  have hh := matrixNorm_bound (b := 16155000000000000000000000000000000000000000000000000000000000) minusApproxBox_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma minusResidualRow0_calc (j : Fin 20) : minusResidualBox 0 j = minusResidualRow0 j := by
  revert j
  decide +kernel
lemma minusResidualRow1_calc (j : Fin 20) : minusResidualBox 1 j = minusResidualRow1 j := by
  revert j
  decide +kernel
lemma minusResidualRow2_calc (j : Fin 20) : minusResidualBox 2 j = minusResidualRow2 j := by
  revert j
  decide +kernel
lemma minusResidualRow3_calc (j : Fin 20) : minusResidualBox 3 j = minusResidualRow3 j := by
  revert j
  decide +kernel
lemma minusResidualRow4_calc (j : Fin 20) : minusResidualBox 4 j = minusResidualRow4 j := by
  revert j
  decide +kernel
lemma minusResidualRow5_calc (j : Fin 20) : minusResidualBox 5 j = minusResidualRow5 j := by
  revert j
  decide +kernel
lemma minusResidualRow6_calc (j : Fin 20) : minusResidualBox 6 j = minusResidualRow6 j := by
  revert j
  decide +kernel
lemma minusResidualRow7_calc (j : Fin 20) : minusResidualBox 7 j = minusResidualRow7 j := by
  revert j
  decide +kernel
lemma minusResidualRow8_calc (j : Fin 20) : minusResidualBox 8 j = minusResidualRow8 j := by
  revert j
  decide +kernel
lemma minusResidualRow9_calc (j : Fin 20) : minusResidualBox 9 j = minusResidualRow9 j := by
  revert j
  decide +kernel
lemma minusResidualRow10_calc (j : Fin 20) : minusResidualBox 10 j = minusResidualRow10 j := by
  revert j
  decide +kernel
lemma minusResidualRow11_calc (j : Fin 20) : minusResidualBox 11 j = minusResidualRow11 j := by
  revert j
  decide +kernel
lemma minusResidualRow12_calc (j : Fin 20) : minusResidualBox 12 j = minusResidualRow12 j := by
  revert j
  decide +kernel
lemma minusResidualRow13_calc (j : Fin 20) : minusResidualBox 13 j = minusResidualRow13 j := by
  revert j
  decide +kernel
lemma minusResidualRow14_calc (j : Fin 20) : minusResidualBox 14 j = minusResidualRow14 j := by
  revert j
  decide +kernel
lemma minusResidualRow15_calc (j : Fin 20) : minusResidualBox 15 j = minusResidualRow15 j := by
  revert j
  decide +kernel
lemma minusResidualRow16_calc (j : Fin 20) : minusResidualBox 16 j = minusResidualRow16 j := by
  revert j
  decide +kernel
lemma minusResidualRow17_calc (j : Fin 20) : minusResidualBox 17 j = minusResidualRow17 j := by
  revert j
  decide +kernel
lemma minusResidualRow18_calc (j : Fin 20) : minusResidualBox 18 j = minusResidualRow18 j := by
  revert j
  decide +kernel
lemma minusResidualRow19_calc (j : Fin 20) : minusResidualBox 19 j = minusResidualRow19 j := by
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
lemma UplusTableRow1_calc (j : Fin 8) : UplusCachedBox 1 j = UplusTableRow1 j := by
  revert j
  decide +kernel
lemma UplusTableRow2_calc (j : Fin 8) : UplusCachedBox 2 j = UplusTableRow2 j := by
  revert j
  decide +kernel
lemma UplusTableRow3_calc (j : Fin 8) : UplusCachedBox 3 j = UplusTableRow3 j := by
  revert j
  decide +kernel
lemma UplusTableRow4_calc (j : Fin 8) : UplusCachedBox 4 j = UplusTableRow4 j := by
  revert j
  decide +kernel
lemma UplusTableRow5_calc (j : Fin 8) : UplusCachedBox 5 j = UplusTableRow5 j := by
  revert j
  decide +kernel
lemma UplusTableRow6_calc (j : Fin 8) : UplusCachedBox 6 j = UplusTableRow6 j := by
  revert j
  decide +kernel
lemma UplusTableRow7_calc (j : Fin 8) : UplusCachedBox 7 j = UplusTableRow7 j := by
  revert j
  decide +kernel
lemma UplusTableRow8_calc (j : Fin 8) : UplusCachedBox 8 j = UplusTableRow8 j := by
  revert j
  decide +kernel
lemma UplusTableRow9_calc (j : Fin 8) : UplusCachedBox 9 j = UplusTableRow9 j := by
  revert j
  decide +kernel
lemma UplusTableRow10_calc (j : Fin 8) : UplusCachedBox 10 j = UplusTableRow10 j := by
  revert j
  decide +kernel
lemma UplusTableRow11_calc (j : Fin 8) : UplusCachedBox 11 j = UplusTableRow11 j := by
  revert j
  decide +kernel
lemma UplusTableRow12_calc (j : Fin 8) : UplusCachedBox 12 j = UplusTableRow12 j := by
  revert j
  decide +kernel
lemma UplusTableRow13_calc (j : Fin 8) : UplusCachedBox 13 j = UplusTableRow13 j := by
  revert j
  decide +kernel
lemma UplusTableRow14_calc (j : Fin 8) : UplusCachedBox 14 j = UplusTableRow14 j := by
  revert j
  decide +kernel
lemma UplusTableRow15_calc (j : Fin 8) : UplusCachedBox 15 j = UplusTableRow15 j := by
  revert j
  decide +kernel
lemma UplusTableRow16_calc (j : Fin 8) : UplusCachedBox 16 j = UplusTableRow16 j := by
  revert j
  decide +kernel
lemma UplusTableRow17_calc (j : Fin 8) : UplusCachedBox 17 j = UplusTableRow17 j := by
  revert j
  decide +kernel
lemma UplusTableRow18_calc (j : Fin 8) : UplusCachedBox 18 j = UplusTableRow18 j := by
  revert j
  decide +kernel
lemma UplusTableRow19_calc (j : Fin 8) : UplusCachedBox 19 j = UplusTableRow19 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma targetEnvf21_mem : targetEnvf21.Mem (targetEnvelope (damping 1) 21) := by
  rw [← targetEnvf21_calc]
  apply targetEnvBox_mem 1 21 _ _ targetExpf21_mem (by decide +kernel)
  · exact QBox21_mem
  · exact DBox21_mem
lemma targetEnvTablef_mem (i : Fin 6) : (targetEnvTablef i).Mem (targetEnvelope (damping 1) (finiteNode ⟨i.val+4,by omega⟩)) := by
  fin_cases i
  · exact targetEnvf9_mem
  · exact targetEnvf12_mem
  · exact targetEnvf13_mem
  · exact targetEnvf16_mem
  · exact targetEnvf19_mem
  · exact targetEnvf21_mem
lemma finiteTargetEnvelope_bound : finiteTargetEnvelope < (81/10^9:ℝ) := by
  have hh := RI.mem_sum targetEnvTablef_mem
  rw [finiteTargetBox_calc] at hh
  have hb := ri_mem_lt hh 81 (10^9) (by norm_num) (by decide +kernel)
  simpa [finiteTargetEnvelope,tailTargetEnvelope,damping,div_eq_mul_inv,show (10:ℝ)^9=1000000000 by norm_num,show (10:ℝ)^30=1000000000000000000000000000000 by norm_num] using hb
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma amplitudeNormBox_mem (q br : Fin 2) (j : Fin 31) :
    (amplitudeNormBox q br j).Mem ‖taylorAmplitude q br (frequency j)‖ := by
  fin_cases br
  · simpa [amplitudeNormBox,taylorAmplitude] using ri1_mem
  · fin_cases q
    · simpa [amplitudeNormBox,taylorAmplitude] using lambdaNorm0_mem j
    · simpa [amplitudeNormBox,taylorAmplitude] using lambdaNorm1_mem j

lemma curvatureBox_mem (q br : Fin 2) (i : Fin 5) (j : Fin 31)
    (hp : (curvatureExpInput q br i j).normSq.hi ≤ scale*1024^2) :
    (curvatureBox q br i j).Mem (curvatureWave q br (curvaturePoint i) (frequency j)) := by
  have hs := CI.mem_normSq (taylorPhaseTable_mem q br j)
  rw [Complex.normSq_eq_norm_sq] at hs
  exact RI.mem_mul (RI.mem_mul hs (amplitudeNormBox_mem q br j))
    (ri_exp_mem (RI.mem_mul (taylorPhaseTable_mem q br j).1 (curvaturePointBox_mem i)) hp)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_CurvatureData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData10_0_mem (j : Fin 31) : (curvatureData10_0 j).Mem (curvatureWave 1 0 (curvaturePoint 0) (frequency j)) := by
  rw [← curvatureData10_0_calc]
  exact curvatureBox_mem 1 0 0 j (curvatureData10_0_pre j)
lemma curvatureData10_1_mem (j : Fin 31) : (curvatureData10_1 j).Mem (curvatureWave 1 0 (curvaturePoint 1) (frequency j)) := by
  rw [← curvatureData10_1_calc]
  exact curvatureBox_mem 1 0 1 j (curvatureData10_1_pre j)
lemma curvatureData10_2_mem (j : Fin 31) : (curvatureData10_2 j).Mem (curvatureWave 1 0 (curvaturePoint 2) (frequency j)) := by
  rw [← curvatureData10_2_calc]
  exact curvatureBox_mem 1 0 2 j (curvatureData10_2_pre j)
lemma curvatureData10_3_mem (j : Fin 31) : (curvatureData10_3 j).Mem (curvatureWave 1 0 (curvaturePoint 3) (frequency j)) := by
  rw [← curvatureData10_3_calc]
  exact curvatureBox_mem 1 0 3 j (curvatureData10_3_pre j)
lemma curvatureData10_4_mem (j : Fin 31) : (curvatureData10_4 j).Mem (curvatureWave 1 0 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData10_4_calc]
  exact curvatureBox_mem 1 0 4 j (curvatureData10_4_pre j)
lemma curvatureTable10_mem (i : Fin 5) (j : Fin 31) : (curvatureTable10 i j).Mem (curvatureWave 1 0 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData10_0_mem j
  · exact curvatureData10_1_mem j
  · exact curvatureData10_2_mem j
  · exact curvatureData10_3_mem j
  · exact curvatureData10_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureColumn0_0_bound (c : Fin 22) : rawCurvatureColumn 0 (curvaturePoint 0) c < (828/10:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (curvatureTable10_mem 0 j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [curvatureColumn0_0_calc] at hh
  have hb := ri_mem_lt hh 828 10 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawCurvatureColumn, Nat.cast_ofNat, Nat.cast_one, Int.cast_ofNat, Int.cast_one] using hb
end AtomicTriangular.FiniteCertificate
end

end OAI
end


