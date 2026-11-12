-- Prove2me | Definitions.Def_OAIQ250T080
-- name    : OAIQ250T080
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:21:25.155361+00:00
-- url     : https://prove2.me/theorems/4ecb5497-ebe7-49d9-8c11-4ff7626f7470
-- title:
--   Definitions bundle OAIQ250T080 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 1 definition and 9 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.spectrum0_0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_RemainderSums2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums2.lean), [`Triangular_Signs_RemainderSums3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T003`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T013` and `OAIQ250T014` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ250T086`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T013
import Definitions.Def_OAIQ250T014

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def spectrum0_0 : Fin 31 → Fin 8 → CI := ![spectrum0_0_0,spectrum0_0_1,spectrum0_0_2,spectrum0_0_3,spectrum0_0_4,spectrum0_0_5,spectrum0_0_6,spectrum0_0_7,spectrum0_0_8,spectrum0_0_9,spectrum0_0_10,spectrum0_0_11,spectrum0_0_12,spectrum0_0_13,spectrum0_0_14,spectrum0_0_15,spectrum0_0_16,spectrum0_0_17,spectrum0_0_18,spectrum0_0_19,spectrum0_0_20,spectrum0_0_21,spectrum0_0_22,spectrum0_0_23,spectrum0_0_24,spectrum0_0_25,spectrum0_0_26,spectrum0_0_27,spectrum0_0_28,spectrum0_0_29,spectrum0_0_30]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0b10_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 10 r = ex0b10 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst2_0_calc : RI.sum (fun j : Fin 31 => (remainderData2_00 j).mul (columnNorm22 j))=remainderConst2_0 := by decide +kernel
lemma remainderConst2_1_calc : RI.sum (fun j : Fin 31 => (remainderData2_01 j).mul (columnNorm22 j))=remainderConst2_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns3_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData3_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns3_0 c := by
  revert c
  decide +kernel
lemma remainderColumns3_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData3_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns3_1 c := by
  revert c
  decide +kernel
lemma remainderConst3_0_calc : RI.sum (fun j : Fin 31 => (remainderData3_00 j).mul (columnNorm22 j))=remainderConst3_0 := by decide +kernel
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
lemma cellGeometry22 (k : Fin 100) :
    0 ≤ cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0 ≤ cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0 ≤ cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry23 (k : Fin 100) :
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0 ≤ cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry24 (k : Fin 100) :
    0 ≤ cellMagnitude 24 k ∧ cellMagnitude 24 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 24 → 0 ≤ cellSeparation 24 k j ∧ cellSeparation 24 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 24 k ∧ cellMagnitude 24 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 24 → 0 ≤ cellSeparation 24 k j ∧ cellSeparation 24 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


