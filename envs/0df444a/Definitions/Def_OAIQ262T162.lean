-- Prove2me | Definitions.Def_OAIQ262T162
-- name    : OAIQ262T162
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T17:30:22.88258+00:00
-- url     : https://prove2.me/theorems/e3b497f9-c7d8-43a5-8b9a-e34b5c15738a
-- title:
--   Definitions bundle OAIQ262T162 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_RemainderData4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData4.lean), [`Triangular_Signs_RemainderData5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData5.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T018`, `OAIQ262T019` and `OAIQ262T144` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T260`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T018
import Definitions.Def_OAIQ262T019
import Definitions.Def_OAIQ262T144

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
lemma remainderData4_00_calc (j : Fin 31) : remainderBox 0 0 4 j (taylorNormTable 0 0 j)=remainderData4_00 j := by
  revert j
  decide +kernel
lemma remainderData4_01_calc (j : Fin 31) : remainderBox 0 1 4 j (taylorNormTable 0 1 j)=remainderData4_01 j := by
  revert j
  decide +kernel
lemma remainderData4_11_calc (j : Fin 31) : remainderBox 1 1 4 j (taylorNormTable 1 1 j)=remainderData4_11 j := by
  revert j
  decide +kernel
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
lemma remainderData5_00_calc (j : Fin 31) : remainderBox 0 0 5 j (taylorNormTable 0 0 j)=remainderData5_00 j := by
  revert j
  decide +kernel
lemma remainderData5_01_calc (j : Fin 31) : remainderBox 0 1 5 j (taylorNormTable 0 1 j)=remainderData5_01 j := by
  revert j
  decide +kernel
lemma remainderData5_10_calc (j : Fin 31) : remainderBox 1 0 5 j (taylorNormTable 1 0 j)=remainderData5_10 j := by
  revert j
  decide +kernel
lemma remainderData5_11_calc (j : Fin 31) : remainderBox 1 1 5 j (taylorNormTable 1 1 j)=remainderData5_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


