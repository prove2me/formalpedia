-- Prove2me | Definitions.Def_OAIQ262T165
-- name    : OAIQ262T165
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:05:24.528773+00:00
-- url     : https://prove2.me/theorems/bc02aa52-1f60-4533-89b2-473b963bc5ee
-- title:
--   Definitions bundle OAIQ262T165 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 28 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Taylor_TaylorWave002`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave002.lean), [`Triangular_Taylor_TaylorWave003`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave003.lean), [`Triangular_Taylor_TaylorWave004`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave004.lean).
--
--   **Imports.** It imports the bundle `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_2_8_calc (j : Fin 31) : taylorWaveBox 0 0 2 8 j = tw0_0_2_8 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_3_0_calc (j : Fin 31) : taylorWaveBox 0 0 3 0 j = tw0_0_3_0 j := by
  revert j
  decide +kernel
lemma tw0_0_3_1_calc (j : Fin 31) : taylorWaveBox 0 0 3 1 j = tw0_0_3_1 j := by
  revert j
  decide +kernel
lemma tw0_0_3_2_calc (j : Fin 31) : taylorWaveBox 0 0 3 2 j = tw0_0_3_2 j := by
  revert j
  decide +kernel
lemma tw0_0_3_3_calc (j : Fin 31) : taylorWaveBox 0 0 3 3 j = tw0_0_3_3 j := by
  revert j
  decide +kernel
lemma tw0_0_3_4_calc (j : Fin 31) : taylorWaveBox 0 0 3 4 j = tw0_0_3_4 j := by
  revert j
  decide +kernel
lemma tw0_0_3_5_calc (j : Fin 31) : taylorWaveBox 0 0 3 5 j = tw0_0_3_5 j := by
  revert j
  decide +kernel
lemma tw0_0_3_6_calc (j : Fin 31) : taylorWaveBox 0 0 3 6 j = tw0_0_3_6 j := by
  revert j
  decide +kernel
lemma tw0_0_3_7_calc (j : Fin 31) : taylorWaveBox 0 0 3 7 j = tw0_0_3_7 j := by
  revert j
  decide +kernel
lemma tw0_0_3_8_calc (j : Fin 31) : taylorWaveBox 0 0 3 8 j = tw0_0_3_8 j := by
  revert j
  decide +kernel
lemma tw0_0_3_9_calc (j : Fin 31) : taylorWaveBox 0 0 3 9 j = tw0_0_3_9 j := by
  revert j
  decide +kernel
lemma tw0_0_3_10_calc (j : Fin 31) : taylorWaveBox 0 0 3 10 j = tw0_0_3_10 j := by
  revert j
  decide +kernel
lemma tw0_0_3_11_calc (j : Fin 31) : taylorWaveBox 0 0 3 11 j = tw0_0_3_11 j := by
  revert j
  decide +kernel
lemma tw0_0_3_12_calc (j : Fin 31) : taylorWaveBox 0 0 3 12 j = tw0_0_3_12 j := by
  revert j
  decide +kernel
lemma tw0_0_3_13_calc (j : Fin 31) : taylorWaveBox 0 0 3 13 j = tw0_0_3_13 j := by
  revert j
  decide +kernel
lemma tw0_0_3_14_calc (j : Fin 31) : taylorWaveBox 0 0 3 14 j = tw0_0_3_14 j := by
  revert j
  decide +kernel
lemma tw0_0_3_15_calc (j : Fin 31) : taylorWaveBox 0 0 3 15 j = tw0_0_3_15 j := by
  revert j
  decide +kernel
lemma tw0_0_3_16_calc (j : Fin 31) : taylorWaveBox 0 0 3 16 j = tw0_0_3_16 j := by
  revert j
  decide +kernel
lemma tw0_0_3_17_calc (j : Fin 31) : taylorWaveBox 0 0 3 17 j = tw0_0_3_17 j := by
  revert j
  decide +kernel
lemma tw0_0_3_18_calc (j : Fin 31) : taylorWaveBox 0 0 3 18 j = tw0_0_3_18 j := by
  revert j
  decide +kernel
lemma tw0_0_3_19_calc (j : Fin 31) : taylorWaveBox 0 0 3 19 j = tw0_0_3_19 j := by
  revert j
  decide +kernel
lemma tw0_0_3_20_calc (j : Fin 31) : taylorWaveBox 0 0 3 20 j = tw0_0_3_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_4_0_calc (j : Fin 31) : taylorWaveBox 0 0 4 0 j = tw0_0_4_0 j := by
  revert j
  decide +kernel
lemma tw0_0_4_10_calc (j : Fin 31) : taylorWaveBox 0 0 4 10 j = tw0_0_4_10 j := by
  revert j
  decide +kernel
lemma tw0_0_4_11_calc (j : Fin 31) : taylorWaveBox 0 0 4 11 j = tw0_0_4_11 j := by
  revert j
  decide +kernel
lemma tw0_0_4_12_calc (j : Fin 31) : taylorWaveBox 0 0 4 12 j = tw0_0_4_12 j := by
  revert j
  decide +kernel
lemma tw0_0_4_13_calc (j : Fin 31) : taylorWaveBox 0 0 4 13 j = tw0_0_4_13 j := by
  revert j
  decide +kernel
lemma tw0_0_4_14_calc (j : Fin 31) : taylorWaveBox 0 0 4 14 j = tw0_0_4_14 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end


