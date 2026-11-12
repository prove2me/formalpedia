-- Prove2me | Definitions.Def_OAIQ262T161
-- name    : OAIQ262T161
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:16:14.28098+00:00
-- url     : https://prove2.me/theorems/cc07a63b-f1be-4ac9-9b71-e9d6f1f92e50
-- title:
--   Definitions bundle OAIQ262T161 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 1 definition and 8 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.taylorRowBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_RemainderData2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData2.lean), [`Triangular_Signs_RemainderData3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData3.lean), [`Triangular_Signs_RemainderData4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData4.lean), [`Triangular_Taylor_TaylorRowsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean), [`Triangular_Taylor_TaylorWave001`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave001.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T143`, `OAIQ262T144` and `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T196`, `OAIQ262T197`, `OAIQ262T198`, `OAIQ262T199`, `OAIQ262T200`, `OAIQ262T201`, `OAIQ262T202`, `OAIQ262T203`, `OAIQ262T204`, `OAIQ262T205`, `OAIQ262T206`, `OAIQ262T207`, `OAIQ262T208`, `OAIQ262T209`, `OAIQ262T210`, `OAIQ262T211`, `OAIQ262T212`, `OAIQ262T213`, `OAIQ262T214`, `OAIQ262T215`, `OAIQ262T216`, `OAIQ262T217`, `OAIQ262T218`, `OAIQ262T219`, `OAIQ262T220`, `OAIQ262T221`, `OAIQ262T222`, `OAIQ262T223`, `OAIQ262T224`, `OAIQ262T225`, `OAIQ262T226`, `OAIQ262T227`, `OAIQ262T228`, `OAIQ262T229`, `OAIQ262T230`, `OAIQ262T231`, `OAIQ262T232`, `OAIQ262T233`, `OAIQ262T234`, `OAIQ262T235`, `OAIQ262T236`, `OAIQ262T237`, `OAIQ262T238`, `OAIQ262T239`, `OAIQ262T240`, `OAIQ262T241`, `OAIQ262T242`, `OAIQ262T243`, `OAIQ262T244`, `OAIQ262T245`, `OAIQ262T246`, `OAIQ262T247`, `OAIQ262T248`, `OAIQ262T249`, `OAIQ262T250`, `OAIQ262T251`, `OAIQ262T252` and `OAIQ262T260`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T143
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
lemma tw0_0_1_11_calc (j : Fin 31) : taylorWaveBox 0 0 1 11 j = tw0_0_1_11 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def taylorRowBox (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) : RI :=
  ((nearDisplacementBox n y).pow l.val).mul
    (CI.sum (fun q : Fin 2 => CI.sum (fun j : Fin 31 =>
      ((spectrumTable side q j r).mul (taylorWaveTable q 0 n l j)).add
      ((spectrumTable (otherSide side) q j r).mul (taylorWaveTable q 1 n l j))))).re
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
lemma remainderData2_00_calc (j : Fin 31) : remainderBox 0 0 2 j (taylorNormTable 0 0 j)=remainderData2_00 j := by
  revert j
  decide +kernel
lemma remainderData2_01_calc (j : Fin 31) : remainderBox 0 1 2 j (taylorNormTable 0 1 j)=remainderData2_01 j := by
  revert j
  decide +kernel
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
lemma remainderData3_00_calc (j : Fin 31) : remainderBox 0 0 3 j (taylorNormTable 0 0 j)=remainderData3_00 j := by
  revert j
  decide +kernel
lemma remainderData3_01_calc (j : Fin 31) : remainderBox 0 1 3 j (taylorNormTable 0 1 j)=remainderData3_01 j := by
  revert j
  decide +kernel
lemma remainderData3_10_calc (j : Fin 31) : remainderBox 1 0 3 j (taylorNormTable 1 0 j)=remainderData3_10 j := by
  revert j
  decide +kernel
lemma remainderData3_11_calc (j : Fin 31) : remainderBox 1 1 3 j (taylorNormTable 1 1 j)=remainderData3_11 j := by
  revert j
  decide +kernel
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
lemma remainderData4_10_calc (j : Fin 31) : remainderBox 1 0 4 j (taylorNormTable 1 0 j)=remainderData4_10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


