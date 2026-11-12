-- Prove2me | Definitions.Def_OAIQ262T157
-- name    : OAIQ262T157
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:57:20.50005+00:00
-- url     : https://prove2.me/theorems/b4e0011a-5bb7-4f31-be21-563870eafbeb
-- title:
--   Definitions bundle OAIQ262T157 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 16 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_Inverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean), [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_ParamU`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean), [`Triangular_Taylor_VariationBound`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/VariationBound.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T137`, `OAIQ262T139`, `OAIQ262T140`, `OAIQ262T141`, `OAIQ262T142` and `OAIQ262T143` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T193` and `OAIQ262T194`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T137
import Definitions.Def_OAIQ262T139
import Definitions.Def_OAIQ262T140
import Definitions.Def_OAIQ262T141
import Definitions.Def_OAIQ262T142
import Definitions.Def_OAIQ262T143

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
lemma fullJetRow0_calc (col : Fin 23) : fullJetBox 0 col = fullJetRow0 col := by
  revert col
  decide +kernel
lemma fullJetRow1_calc (col : Fin 23) : fullJetBox 1 col = fullJetRow1 col := by
  revert col
  decide +kernel
lemma fullJetRow2_calc (col : Fin 23) : fullJetBox 2 col = fullJetRow2 col := by
  revert col
  decide +kernel
lemma fullJetRow10_calc (col : Fin 23) : fullJetBox 10 col = fullJetRow10 col := by
  revert col
  decide +kernel
lemma fullJetRow11_calc (col : Fin 23) : fullJetBox 11 col = fullJetRow11 col := by
  revert col
  decide +kernel
lemma fullJetRow12_calc (col : Fin 23) : fullJetBox 12 col = fullJetRow12 col := by
  revert col
  decide +kernel
lemma fullJetRow13_calc (col : Fin 23) : fullJetBox 13 col = fullJetRow13 col := by
  revert col
  decide +kernel
lemma fullJetRow14_calc (col : Fin 23) : fullJetBox 14 col = fullJetRow14 col := by
  revert col
  decide +kernel
lemma fullJetRow15_calc (col : Fin 23) : fullJetBox 15 col = fullJetRow15 col := by
  revert col
  decide +kernel
lemma fullJetRow16_calc (col : Fin 23) : fullJetBox 16 col = fullJetRow16 col := by
  revert col
  decide +kernel
lemma fullJetRow17_calc (col : Fin 23) : fullJetBox 17 col = fullJetRow17 col := by
  revert col
  decide +kernel
lemma fullJetRow18_calc (col : Fin 23) : fullJetBox 18 col = fullJetRow18 col := by
  revert col
  decide +kernel
lemma fullJetRow19_calc (col : Fin 23) : fullJetBox 19 col = fullJetRow19 col := by
  revert col
  decide +kernel
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
lemma minusApprox_bound : matNorm minusApprox ≤ (16155/1000:ℝ) := by
  have hh := matrixNorm_bound (b := 16155000000000000000000000000000000000000000000000000000000000) minusApproxBox_mem (by
    intro j
    revert j
    decide +kernel)
  norm_num [scale] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

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
lemma UminusTable_calc (i : Fin 20) (j : Fin 8) : UminusCachedBox i j = UminusTable i j := by
  fin_cases i
  · exact UminusTableRow0_calc j
  · exact UminusTableRow1_calc j
  · exact UminusTableRow2_calc j
  · exact UminusTableRow3_calc j
  · exact UminusTableRow4_calc j
  · exact UminusTableRow5_calc j
  · exact UminusTableRow6_calc j
  · exact UminusTableRow7_calc j
  · exact UminusTableRow8_calc j
  · exact UminusTableRow9_calc j
  · exact UminusTableRow10_calc j
  · exact UminusTableRow11_calc j
  · exact UminusTableRow12_calc j
  · exact UminusTableRow13_calc j
  · exact UminusTableRow14_calc j
  · exact UminusTableRow15_calc j
  · exact UminusTableRow16_calc j
  · exact UminusTableRow17_calc j
  · exact UminusTableRow18_calc j
  · exact UminusTableRow19_calc j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_VariationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

lemma dVariationBox_mem : dVariationBox.Mem dVariation := by
  have hx := RI.mem_mul (RI.mem_sum (fun j : Fin 31 => RI.mem_mul (fourierNorm_mem j) (RI.mem_pow (varFreqBox_mem j) 1))) (RI.mem_pow piBox_mem 1)
  simpa only [dVariationBox,dVariation,coeffAbs,pow_one] using hx
end AtomicTriangular.FiniteCertificate
end

end OAI
end


