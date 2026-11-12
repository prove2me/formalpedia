-- Prove2me | Definitions.Def_OAIQ262T160
-- name    : OAIQ262T160
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:07:03.793874+00:00
-- url     : https://prove2.me/theorems/1593ea0f-2b47-441f-b21e-b6e95995f84b
-- title:
--   Definitions bundle OAIQ262T160 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_RemainderData1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData1.lean), [`Triangular_Signs_RemainderData2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData2.lean), [`Triangular_Taylor_TaylorWave000`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave000.lean), [`Triangular_Taylor_TaylorWave001`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave001.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T144` and `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T260`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T144
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_7_calc (j : Fin 31) : taylorWaveBox 0 0 0 7 j = tw0_0_0_7 j := by
  revert j
  decide +kernel
lemma tw0_0_0_8_calc (j : Fin 31) : taylorWaveBox 0 0 0 8 j = tw0_0_0_8 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

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
lemma tw0_0_1_17_calc (j : Fin 31) : taylorWaveBox 0 0 1 17 j = tw0_0_1_17 j := by
  revert j
  decide +kernel

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
lemma remainderData1_00_calc (j : Fin 31) : remainderBox 0 0 1 j (taylorNormTable 0 0 j)=remainderData1_00 j := by
  revert j
  decide +kernel
lemma remainderData1_01_calc (j : Fin 31) : remainderBox 0 1 1 j (taylorNormTable 0 1 j)=remainderData1_01 j := by
  revert j
  decide +kernel
lemma remainderData1_10_calc (j : Fin 31) : remainderBox 1 0 1 j (taylorNormTable 1 0 j)=remainderData1_10 j := by
  revert j
  decide +kernel
lemma remainderData1_11_calc (j : Fin 31) : remainderBox 1 1 1 j (taylorNormTable 1 1 j)=remainderData1_11 j := by
  revert j
  decide +kernel
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
lemma remainderData2_10_calc (j : Fin 31) : remainderBox 1 0 2 j (taylorNormTable 1 0 j)=remainderData2_10 j := by
  revert j
  decide +kernel
lemma remainderData2_11_calc (j : Fin 31) : remainderBox 1 1 2 j (taylorNormTable 1 1 j)=remainderData2_11 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


