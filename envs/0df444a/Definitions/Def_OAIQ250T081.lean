-- Prove2me | Definitions.Def_OAIQ250T081
-- name    : OAIQ250T081
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:20:17.244288+00:00
-- url     : https://prove2.me/theorems/495644b0-6fcd-4077-8188-864e958b5c7e
-- title:
--   Definitions bundle OAIQ250T081 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 definition and 10 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.ex0b`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_RemainderSums3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean), [`Triangular_Signs_RemainderSums4`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums4.lean), [`Triangular_Signs_RemainderSums5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums5.lean), [`Triangular_Signs_RemainderSums6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums6.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean).
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
def ex0b : Fin 23 → Fin 8 → RI := ![ex0b0,ex0b1,ex0b2,ex0b3,ex0b4,ex0b5,ex0b6,ex0b7,ex0b8,ex0b9,ex0b10,ex0b11,ex0b12,ex0b13,ex0b14,ex0b15,ex0b16,ex0b17,ex0b18,ex0b19,ex0b20,ex0b21,ex0b22]
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
lemma remainderConst3_1_calc : RI.sum (fun j : Fin 31 => (remainderData3_01 j).mul (columnNorm22 j))=remainderConst3_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns4_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData4_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns4_0 c := by
  revert c
  decide +kernel
lemma remainderColumns4_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData4_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns4_1 c := by
  revert c
  decide +kernel
lemma remainderConst4_0_calc : RI.sum (fun j : Fin 31 => (remainderData4_00 j).mul (columnNorm22 j))=remainderConst4_0 := by decide +kernel
lemma remainderConst4_1_calc : RI.sum (fun j : Fin 31 => (remainderData4_01 j).mul (columnNorm22 j))=remainderConst4_1 := by decide +kernel
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
lemma remainderColumns5_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData5_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns5_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns6_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData6_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns6_0 c := by
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
lemma cellGeometry25 (k : Fin 100) :
    0 ≤ cellMagnitude 25 k ∧ cellMagnitude 25 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 25 → 0 ≤ cellSeparation 25 k j ∧ cellSeparation 25 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 25 k ∧ cellMagnitude 25 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 25 → 0 ≤ cellSeparation 25 k j ∧ cellSeparation 25 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry26 (k : Fin 100) :
    0 ≤ cellMagnitude 26 k ∧ cellMagnitude 26 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 26 → 0 ≤ cellSeparation 26 k j ∧ cellSeparation 26 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 26 k ∧ cellMagnitude 26 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 26 → 0 ≤ cellSeparation 26 k j ∧ cellSeparation 26 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry27 (k : Fin 100) :
    0 ≤ cellMagnitude 27 k ∧ cellMagnitude 27 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 27 → 0 ≤ cellSeparation 27 k j ∧ cellSeparation 27 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 27 k ∧ cellMagnitude 27 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 27 → 0 ≤ cellSeparation 27 k j ∧ cellSeparation 27 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


