-- Prove2me | Definitions.Def_OAIQ262T167
-- name    : OAIQ262T167
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:16:28.201025+00:00
-- url     : https://prove2.me/theorems/a50d011b-4055-423c-bed7-ccd7ca64cff6
-- title:
--   Definitions bundle OAIQ262T167 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 26 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave005`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave005.lean), [`Triangular_Taylor_TaylorWave006`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave006.lean).
--
--   **Imports.** It imports the bundle `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_5_2_calc (j : Fin 31) : taylorWaveBox 0 0 5 2 j = tw0_0_5_2 j := by
  revert j
  decide +kernel
lemma tw0_0_5_3_calc (j : Fin 31) : taylorWaveBox 0 0 5 3 j = tw0_0_5_3 j := by
  revert j
  decide +kernel
lemma tw0_0_5_4_calc (j : Fin 31) : taylorWaveBox 0 0 5 4 j = tw0_0_5_4 j := by
  revert j
  decide +kernel
lemma tw0_0_5_5_calc (j : Fin 31) : taylorWaveBox 0 0 5 5 j = tw0_0_5_5 j := by
  revert j
  decide +kernel
lemma tw0_0_5_6_calc (j : Fin 31) : taylorWaveBox 0 0 5 6 j = tw0_0_5_6 j := by
  revert j
  decide +kernel
lemma tw0_0_5_7_calc (j : Fin 31) : taylorWaveBox 0 0 5 7 j = tw0_0_5_7 j := by
  revert j
  decide +kernel
lemma tw0_0_5_8_calc (j : Fin 31) : taylorWaveBox 0 0 5 8 j = tw0_0_5_8 j := by
  revert j
  decide +kernel
lemma tw0_0_5_9_calc (j : Fin 31) : taylorWaveBox 0 0 5 9 j = tw0_0_5_9 j := by
  revert j
  decide +kernel
lemma tw0_0_5_20_calc (j : Fin 31) : taylorWaveBox 0 0 5 20 j = tw0_0_5_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_6_0_calc (j : Fin 31) : taylorWaveBox 0 0 6 0 j = tw0_0_6_0 j := by
  revert j
  decide +kernel
lemma tw0_0_6_1_calc (j : Fin 31) : taylorWaveBox 0 0 6 1 j = tw0_0_6_1 j := by
  revert j
  decide +kernel
lemma tw0_0_6_2_calc (j : Fin 31) : taylorWaveBox 0 0 6 2 j = tw0_0_6_2 j := by
  revert j
  decide +kernel
lemma tw0_0_6_3_calc (j : Fin 31) : taylorWaveBox 0 0 6 3 j = tw0_0_6_3 j := by
  revert j
  decide +kernel
lemma tw0_0_6_4_calc (j : Fin 31) : taylorWaveBox 0 0 6 4 j = tw0_0_6_4 j := by
  revert j
  decide +kernel
lemma tw0_0_6_5_calc (j : Fin 31) : taylorWaveBox 0 0 6 5 j = tw0_0_6_5 j := by
  revert j
  decide +kernel
lemma tw0_0_6_10_calc (j : Fin 31) : taylorWaveBox 0 0 6 10 j = tw0_0_6_10 j := by
  revert j
  decide +kernel
lemma tw0_0_6_11_calc (j : Fin 31) : taylorWaveBox 0 0 6 11 j = tw0_0_6_11 j := by
  revert j
  decide +kernel
lemma tw0_0_6_12_calc (j : Fin 31) : taylorWaveBox 0 0 6 12 j = tw0_0_6_12 j := by
  revert j
  decide +kernel
lemma tw0_0_6_13_calc (j : Fin 31) : taylorWaveBox 0 0 6 13 j = tw0_0_6_13 j := by
  revert j
  decide +kernel
lemma tw0_0_6_14_calc (j : Fin 31) : taylorWaveBox 0 0 6 14 j = tw0_0_6_14 j := by
  revert j
  decide +kernel
lemma tw0_0_6_15_calc (j : Fin 31) : taylorWaveBox 0 0 6 15 j = tw0_0_6_15 j := by
  revert j
  decide +kernel
lemma tw0_0_6_16_calc (j : Fin 31) : taylorWaveBox 0 0 6 16 j = tw0_0_6_16 j := by
  revert j
  decide +kernel
lemma tw0_0_6_17_calc (j : Fin 31) : taylorWaveBox 0 0 6 17 j = tw0_0_6_17 j := by
  revert j
  decide +kernel
lemma tw0_0_6_18_calc (j : Fin 31) : taylorWaveBox 0 0 6 18 j = tw0_0_6_18 j := by
  revert j
  decide +kernel
lemma tw0_0_6_19_calc (j : Fin 31) : taylorWaveBox 0 0 6 19 j = tw0_0_6_19 j := by
  revert j
  decide +kernel
lemma tw0_0_6_20_calc (j : Fin 31) : taylorWaveBox 0 0 6 20 j = tw0_0_6_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


