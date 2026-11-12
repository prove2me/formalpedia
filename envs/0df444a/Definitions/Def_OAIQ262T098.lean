-- Prove2me | Definitions.Def_OAIQ262T098
-- name    : OAIQ262T098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:52:30.97631+00:00
-- url     : https://prove2.me/theorems/67e3e9e9-5664-4a50-9861-fbd3164ac985
-- title:
--   Definitions bundle OAIQ262T098 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.tw0_0_2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_RemainderSums0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums0.lean), [`Triangular_Signs_RemainderSums1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums1.lean), [`Triangular_Signs_RemainderSums2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums2.lean), [`Triangular_Signs_RemainderSums3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorRowsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean), [`Triangular_Taylor_TaylorWave002`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave002.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T013`, `OAIQ262T015`, `OAIQ262T016`, `OAIQ262T017`, `OAIQ262T018`, `OAIQ262T020`, `OAIQ262T023` and `OAIQ262T024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T146` and `OAIQ262T148`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T016
import Definitions.Def_OAIQ262T017
import Definitions.Def_OAIQ262T018
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T023
import Definitions.Def_OAIQ262T024

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
def tw0_0_2 : Fin 21 → Fin 31 → CI := ![tw0_0_2_0,tw0_0_2_1,tw0_0_2_2,tw0_0_2_3,tw0_0_2_4,tw0_0_2_5,tw0_0_2_6,tw0_0_2_7,tw0_0_2_8,tw0_0_2_9,tw0_0_2_10,tw0_0_2_11,tw0_0_2_12,tw0_0_2_13,tw0_0_2_14,tw0_0_2_15,tw0_0_2_16,tw0_0_2_17,tw0_0_2_18,tw0_0_2_19,tw0_0_2_20]

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

lemma bernsteinRowsBox_mem (n : ℕ) {a : Fin (n+1) → Fin 8 → RI}
    {v : Fin (n+1) → Fin 8 → ℝ} (hv : ∀ l r, (a l r).Mem (v l r))
    (d : Fin (n+1)) (r : Fin 8) :
    (bernsteinRowsBox n a d r).Mem (bernsteinRows n v d r) := by
  apply RI.mem_sum
  intro l
  apply RI.mem_mul _ (hv l r)
  have hh := RI.mem_divNat (RI.mem_point (d.val.choose l.val))
    (Nat.choose_pos (show l.val≤n by omega))
  simpa only [Int.cast_natCast] using hh
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma ep6 : (RI.point 6).Mem (6 : ℝ) := by simpa using RI.mem_point 6

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums0
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums1
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums2
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst3_0_calc : RI.sum (fun j : Fin 31 => (remainderData3_00 j).mul (columnNorm22 j))=remainderConst3_0 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors02 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors03 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 3 k j) ∧ cellBarrier 3 < ∏ j : Fin 15,(cellFactor 3 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 3 k j) ∧ cellBarrier 3 < ∏ j : Fin 15,(cellFactor 3 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


