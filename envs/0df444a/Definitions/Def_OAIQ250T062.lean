-- Prove2me | Definitions.Def_OAIQ250T062
-- name    : OAIQ250T062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:33.996634+00:00
-- url     : https://prove2.me/theorems/ff450492-9c9a-46de-be3d-c60908fc0548
-- title:
--   Definitions bundle OAIQ250T062 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 1 definition and 9 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.spectrum1_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_RemainderSums1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums1.lean), [`Triangular_Signs_RemainderSums2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums2.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T003`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T013`, `OAIQ250T014` and `OAIQ250T015` of this split.
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
import Definitions.Def_OAIQ250T015

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
def spectrum1_1 : Fin 31 → Fin 8 → CI := ![spectrum1_1_0,spectrum1_1_1,spectrum1_1_2,spectrum1_1_3,spectrum1_1_4,spectrum1_1_5,spectrum1_1_6,spectrum1_1_7,spectrum1_1_8,spectrum1_1_9,spectrum1_1_10,spectrum1_1_11,spectrum1_1_12,spectrum1_1_13,spectrum1_1_14,spectrum1_1_15,spectrum1_1_16,spectrum1_1_17,spectrum1_1_18,spectrum1_1_19,spectrum1_1_20,spectrum1_1_21,spectrum1_1_22,spectrum1_1_23,spectrum1_1_24,spectrum1_1_25,spectrum1_1_26,spectrum1_1_27,spectrum1_1_28,spectrum1_1_29,spectrum1_1_30]
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
lemma ex0b11_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 11 r = ex0b11 r := by
  revert r
  decide +kernel
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
lemma remainderConst1_0_calc : RI.sum (fun j : Fin 31 => (remainderData1_00 j).mul (columnNorm22 j))=remainderConst1_0 := by decide +kernel
lemma remainderConst1_1_calc : RI.sum (fun j : Fin 31 => (remainderData1_01 j).mul (columnNorm22 j))=remainderConst1_1 := by decide +kernel
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
lemma remainderColumns2_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData2_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns2_0 c := by
  revert c
  decide +kernel
lemma remainderColumns2_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData2_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns2_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors14 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 14 k j) ∧ cellBarrier 14 < ∏ j : Fin 15,(cellFactor 14 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 14 k j) ∧ cellBarrier 14 < ∏ j : Fin 15,(cellFactor 14 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors15 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors16 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 16 k j) ∧ cellBarrier 16 < ∏ j : Fin 15,(cellFactor 16 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 16 k j) ∧ cellBarrier 16 < ∏ j : Fin 15,(cellFactor 16 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors17 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


