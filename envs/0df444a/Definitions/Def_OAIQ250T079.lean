-- Prove2me | Definitions.Def_OAIQ250T079
-- name    : OAIQ250T079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:20:31.843224+00:00
-- url     : https://prove2.me/theorems/aba30aa1-2288-43e9-9cf5-c96684d6757a
-- title:
--   Definitions bundle OAIQ250T079 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.ex1r`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_DeletedAccuracy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/DeletedAccuracy.lean), [`Triangular_Signs_ExceptionalSign1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign1.lean), [`Triangular_Signs_RemainderSums5`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums5.lean), [`Triangular_Signs_RemainderSums6`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums6.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorRowsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T003`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T013`, `OAIQ250T020`, `OAIQ250T025` and `OAIQ250T026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086`, `OAIQ250T087`, `OAIQ250T088`, `OAIQ250T089`, `OAIQ250T090`, `OAIQ250T091`, `OAIQ250T092`, `OAIQ250T093`, `OAIQ250T094`, `OAIQ250T096`, `OAIQ250T097` and `OAIQ250T098`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T013
import Definitions.Def_OAIQ250T020
import Definitions.Def_OAIQ250T025
import Definitions.Def_OAIQ250T026

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRowsBase
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
lemma remainderConst5_0_calc : RI.sum (fun j : Fin 31 => (remainderData5_00 j).mul (columnNorm22 j))=remainderConst5_0 := by decide +kernel
lemma remainderConst5_1_calc : RI.sum (fun j : Fin 31 => (remainderData5_01 j).mul (columnNorm22 j))=remainderConst5_1 := by decide +kernel
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
lemma remainderColumns6_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData6_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns6_1 c := by
  revert c
  decide +kernel
lemma remainderConst6_0_calc : RI.sum (fun j : Fin 31 => (remainderData6_00 j).mul (columnNorm22 j))=remainderConst6_0 := by decide +kernel
lemma remainderConst6_1_calc : RI.sum (fun j : Fin 31 => (remainderData6_01 j).mul (columnNorm22 j))=remainderConst6_1 := by decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_DeletedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma nearDisplacement_radius (n : Fin 7) (y : Fin 2) : |nearDisplacement n y| ≤ nearRadius n := by
  fin_cases n <;> fin_cases y <;> (first | (simp [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; all_goals first | (norm_num [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | rfl | decide) | (norm_num [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]; done) | norm_num [nearDisplacement,nearDisplacementNum,nearRadius,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail])
lemma nearBase_le_cell (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    curvaturePoint (nearBase n y) ≤ (nearNode n:ℝ)+nearDisplacement n y*τ := by
  obtain ⟨ht0,ht1⟩ := hτ
  fin_cases n <;> fin_cases y <;> norm_num [nearBase,curvaturePoint,nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail] <;> linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def ex1r : Fin 23 → Fin 8 → RI := ![ex1r0,ex1r1,ex1r2,ex1r3,ex1r4,ex1r5,ex1r6,ex1r7,ex1r8,ex1r9,ex1r10,ex1r11,ex1r12,ex1r13,ex1r14,ex1r15,ex1r16,ex1r17,ex1r18,ex1r19,ex1r20,ex1r21,ex1r22]
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
lemma cellGeometry19 (k : Fin 100) :
    0 ≤ cellMagnitude 19 k ∧ cellMagnitude 19 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 19 → 0 ≤ cellSeparation 19 k j ∧ cellSeparation 19 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 19 k ∧ cellMagnitude 19 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 19 → 0 ≤ cellSeparation 19 k j ∧ cellSeparation 19 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
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
lemma cellGeometry20 (k : Fin 100) :
    0 ≤ cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0 ≤ cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0 ≤ cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry21 (k : Fin 100) :
    0 ≤ cellMagnitude 21 k ∧ cellMagnitude 21 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 21 → 0 ≤ cellSeparation 21 k j ∧ cellSeparation 21 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 21 k ∧ cellMagnitude 21 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 21 → 0 ≤ cellSeparation 21 k j ∧ cellSeparation 21 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


