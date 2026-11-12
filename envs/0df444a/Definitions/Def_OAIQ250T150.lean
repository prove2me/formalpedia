-- Prove2me | Definitions.Def_OAIQ250T150
-- name    : OAIQ250T150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:42:45.448652+00:00
-- url     : https://prove2.me/theorems/fcc340a9-a6c5-4151-9e67-d16309348b70
-- title:
--   Definitions bundle OAIQ250T150 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_RemainderSums0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums0.lean), [`Triangular_Signs_RemainderSums1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums1.lean), [`Triangular_Signs_RemainderSums5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums5.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T003`, `OAIQ250T011`, `OAIQ250T012` and `OAIQ250T013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T086`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T013

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst0_0_calc : RI.sum (fun j : Fin 31 => (remainderData0_00 j).mul (columnNorm22 j))=remainderConst0_0 := by decide +kernel
lemma remainderConst0_1_calc : RI.sum (fun j : Fin 31 => (remainderData0_01 j).mul (columnNorm22 j))=remainderConst0_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns1_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData1_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns1_0 c := by
  revert c
  decide +kernel
lemma remainderColumns1_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData1_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns1_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns5_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData5_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns5_0 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors20 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 20 k j) ∧ cellBarrier 20 < ∏ j : Fin 15,(cellFactor 20 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 20 k j) ∧ cellBarrier 20 < ∏ j : Fin 15,(cellFactor 20 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors21 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


