-- Prove2me | Definitions.Def_OAIQ250T102
-- name    : OAIQ250T102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T14:41:58.212308+00:00
-- url     : https://prove2.me/theorems/b91e9117-8eff-4409-8b81-2c2efb000bce
-- title:
--   Definitions bundle OAIQ250T102 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 20 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_JetMatrix`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean), [`Triangular_Certificate_ParamU`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean), [`Triangular_Certificate_TargetInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/TargetInterval.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T083`, `OAIQ250T084` and `OAIQ250T151` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T112`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T083
import Definitions.Def_OAIQ250T084
import Definitions.Def_OAIQ250T151

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
lemma jetTable1_5_calc (j : Fin 31) : jetMultiplierBox 1 5 j = jetTable1_5 j := by
  revert j
  decide +kernel
lemma jetTable1_6_calc (j : Fin 31) : jetMultiplierBox 1 6 j = jetTable1_6 j := by
  revert j
  decide +kernel
lemma jetTable1_7_calc (j : Fin 31) : jetMultiplierBox 1 7 j = jetTable1_7 j := by
  revert j
  decide +kernel
lemma jetTable1_8_calc (j : Fin 31) : jetMultiplierBox 1 8 j = jetTable1_8 j := by
  revert j
  decide +kernel
lemma jetTable1_9_calc (j : Fin 31) : jetMultiplierBox 1 9 j = jetTable1_9 j := by
  revert j
  decide +kernel
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
lemma fullJetRow0_calc (col : Fin 23) : fullJetBox 0 col = fullJetRow0 col := by
  revert col
  decide +kernel
lemma fullJetRow1_calc (col : Fin 23) : fullJetBox 1 col = fullJetRow1 col := by
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
lemma UplusTableRow0_calc (j : Fin 8) : UplusCachedBox 0 j = UplusTableRow0 j := by
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
lemma targetEnvt57_mem : targetEnvt57.Mem (targetEnvelope (damping 0) 57) := by
  rw [← targetEnvt57_calc]
  apply targetEnvBox_mem 0 57 _ _ targetExpt57_mem (by decide +kernel)
  · rw [Q_emod 57]; norm_num; exact QBox21_mem
  · rw [D_emod 57]; norm_num; exact DBox21_mem
lemma targetEnvTablet_mem (i : Fin 15) : (targetEnvTablet i).Mem (targetEnvelope (damping 0) (tailBase i)) := by
  fin_cases i
  · exact targetEnvt36_mem
  · exact targetEnvt37_mem
  · exact targetEnvt39_mem
  · exact targetEnvt40_mem
  · exact targetEnvt43_mem
  · exact targetEnvt45_mem
  · exact targetEnvt48_mem
  · exact targetEnvt49_mem
  · exact targetEnvt52_mem
  · exact targetEnvt55_mem
  · exact targetEnvt57_mem
  · exact targetEnvt25_mem
  · exact targetEnvt27_mem
  · exact targetEnvt28_mem
  · exact targetEnvt31_mem
end AtomicTriangular.FiniteCertificate
end

end OAI
end


