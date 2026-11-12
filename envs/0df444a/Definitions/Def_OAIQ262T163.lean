-- Prove2me | Definitions.Def_OAIQ262T163
-- name    : OAIQ262T163
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:14:10.890195+00:00
-- url     : https://prove2.me/theorems/ab641217-f911-4a5a-b2bb-d02ff30a5224
-- title:
--   Definitions bundle OAIQ262T163 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 16 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_RemainderData6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData6.lean), [`Triangular_Taylor_TaylorWave001`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave001.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T144` and `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T144
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_1_0_calc (j : Fin 31) : taylorWaveBox 0 0 1 0 j = tw0_0_1_0 j := by
  revert j
  decide +kernel
lemma tw0_0_1_1_calc (j : Fin 31) : taylorWaveBox 0 0 1 1 j = tw0_0_1_1 j := by
  revert j
  decide +kernel
lemma tw0_0_1_2_calc (j : Fin 31) : taylorWaveBox 0 0 1 2 j = tw0_0_1_2 j := by
  revert j
  decide +kernel
lemma tw0_0_1_10_calc (j : Fin 31) : taylorWaveBox 0 0 1 10 j = tw0_0_1_10 j := by
  revert j
  decide +kernel
lemma tw0_0_1_12_calc (j : Fin 31) : taylorWaveBox 0 0 1 12 j = tw0_0_1_12 j := by
  revert j
  decide +kernel
lemma tw0_0_1_13_calc (j : Fin 31) : taylorWaveBox 0 0 1 13 j = tw0_0_1_13 j := by
  revert j
  decide +kernel
lemma tw0_0_1_14_calc (j : Fin 31) : taylorWaveBox 0 0 1 14 j = tw0_0_1_14 j := by
  revert j
  decide +kernel
lemma tw0_0_1_15_calc (j : Fin 31) : taylorWaveBox 0 0 1 15 j = tw0_0_1_15 j := by
  revert j
  decide +kernel
lemma tw0_0_1_16_calc (j : Fin 31) : taylorWaveBox 0 0 1 16 j = tw0_0_1_16 j := by
  revert j
  decide +kernel
lemma tw0_0_1_18_calc (j : Fin 31) : taylorWaveBox 0 0 1 18 j = tw0_0_1_18 j := by
  revert j
  decide +kernel
lemma tw0_0_1_19_calc (j : Fin 31) : taylorWaveBox 0 0 1 19 j = tw0_0_1_19 j := by
  revert j
  decide +kernel
lemma tw0_0_1_20_calc (j : Fin 31) : taylorWaveBox 0 0 1 20 j = tw0_0_1_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData6_00_calc (j : Fin 31) : remainderBox 0 0 6 j (taylorNormTable 0 0 j)=remainderData6_00 j := by
  revert j
  decide +kernel
lemma remainderData6_01_calc (j : Fin 31) : remainderBox 0 1 6 j (taylorNormTable 0 1 j)=remainderData6_01 j := by
  revert j
  decide +kernel
lemma remainderData6_10_calc (j : Fin 31) : remainderBox 1 0 6 j (taylorNormTable 1 0 j)=remainderData6_10 j := by
  revert j
  decide +kernel
lemma remainderData6_11_calc (j : Fin 31) : remainderBox 1 1 6 j (taylorNormTable 1 1 j)=remainderData6_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


