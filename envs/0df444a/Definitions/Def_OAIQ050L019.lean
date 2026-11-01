-- Prove2me | Definitions.Def_OAIQ050L019
-- name    : OAIQ050L019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:11:18.944482+00:00
-- url     : https://prove2.me/theorems/7b3207e0-e4d0-4224-858b-9649a309a9fb
-- title:
--   Definitions bundle OAIQ050L019 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 6 definitions and 5 theorems. The definitions and types are `OAI.Laughlin.Spin.genericCoupledBasis`, `OAI.Laughlin.Spin.genericCoupledInclusion`, `OAI.Laughlin.Spin.physicalCoupledInclusion`, `OAI.Laughlin.Spin.physicalThreeBodyLevel`, `OAI.Laughlin.Spin.physicalThreeBodyTraceFormula`, `OAI.Laughlin.Spin.tripleRaise`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_Spin_Basis2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Basis2.lean), [`Laughlin_Spin_Intertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Intertwining.lean), [`Laughlin_Spin_LadderMatrix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/LadderMatrix.lean), [`Laughlin_Spin_Sl2Matrix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Sl2Matrix.lean), [`Laughlin_Spin_TotalSl2Matrix`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TotalSl2Matrix.lean), [`Laughlin_Spin_TripleLadderIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TripleLadderIntertwining.lean), [`Laughlin_ThreeBody_LevelTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/LevelTrace.lean), [`Laughlin_ThreeBody_TraceLimit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/TraceLimit.lean).
--
--   **Imports.** It imports the bundles `OAIQ050L010`, `OAIQ050L011`, `OAIQ050L013` and `OAIQ050L014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L020` and `OAIQ050L021`; the statements `OAI_Laughlin_Spin_physicalThreeBodyTraceFormula_tendsto`, `OAI.Laughlin.Spin.physicalThreeBodyTraceFormula_tendsto_s50`, `OAI_Laughlin_Spin_source_physical_threeBody_trace_formula_tendsto`, `OAI.Laughlin.Spin.source_physical_threeBody_trace_formula_tendsto_s50`, `OAI_Laughlin_Spin_source_threeBody_trace_strict_eventually`, `OAI.Laughlin.Spin.source_threeBody_trace_strict_eventually_s50`, `OAI_Laughlin_Spin_tripleInclusion_transpose_raising` and `OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50`; the proofs of `OAI_Laughlin_Fock_fourPairTargetMatrix_Fock`, `OAI_Laughlin_Spin_fourBody_retained_reconstruction`, `OAI_Laughlin_Spin_pairInclusion_raising`, `OAI.Laughlin.Spin.pairInclusion_raising_s50`, `OAI_Laughlin_Spin_source_physical_threeBody_trace_formula_tendsto`, `OAI.Laughlin.Spin.source_physical_threeBody_trace_formula_tendsto_s50`, `OAI_Laughlin_Spin_source_threeBody_trace_strict_eventually`, `OAI.Laughlin.Spin.source_threeBody_trace_strict_eventually_s50`, `OAI_Laughlin_Spin_threeGram_raising`, `OAI.Laughlin.Spin.threeGram_raising_s50`, `OAI_Laughlin_Spin_tripleInclusion_transpose_raising` and `OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L010
import Definitions.Def_OAIQ050L011
import Definitions.Def_OAIQ050L013
import Definitions.Def_OAIQ050L014

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_LadderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem raiseMatrix_column (A : ℕ) (j : Fin (A+1)) (f : Fin (A+1) → ℝ) :
    (∑ i, f i*raiseMatrix A i j) =
      if hj : 0 < j.val then f ⟨j.val-1,by omega⟩*ladder A (j.val-1) else 0 := by
  by_cases hj : 0 < j.val
  · rw [dite_eq_left hj]
    let prev : Fin (A+1) := ⟨j.val-1,by omega⟩
    rw [Finset.sum_eq_single prev]
    · simp [raiseMatrix,prev,show j.val-1+1=j.val by omega]
    · intro i hi hn
      have hne : i.val+1 ≠ j.val := by
        intro h; apply hn; apply Fin.ext; dsimp [prev]; omega
      simp [raiseMatrix,hne]
    · simp
  · rw [dite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hn : i.val+1 ≠ j.val := by omega
    simp [raiseMatrix,hn]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sl2Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem transpose_mul_raise_entry (A : ℕ) (i j : Fin (A+1)) :
    ((raiseMatrix A)ᵀ * raiseMatrix A) i j =
      if i=j then (i.val : ℝ)*((A : ℝ)-i.val+1) else 0 := by
  change (∑ k, raiseMatrix A k i*raiseMatrix A k j) = _
  have he : (∑ k, raiseMatrix A k i*raiseMatrix A k j) =
      ∑ k, raiseMatrix A k j*raiseMatrix A k i := by
    apply Finset.sum_congr rfl; intro k hk; ring
  rw [he,raiseMatrix_column]
  by_cases hi : 0 < i.val
  · rw [dite_eq_left hi]
    by_cases hij : i=j
    · subst j
      simp only [raiseMatrix,ite_eq_left (show i.val-1+1=i.val by omega),ite_true]
      unfold ladder
      rw [Real.mul_self_sqrt (by positivity)]
      rw [Nat.cast_sub (by omega : i.val-1 ≤ A),Nat.cast_sub (by omega : 1 ≤ i.val)]
      push_cast; ring
    · have hne : i.val-1+1 ≠ j.val := by intro h; apply hij; apply Fin.ext; omega
      simp only [raiseMatrix,ite_eq_right hne,ite_eq_right hij,zero_mul]
  · rw [dite_eq_right hi]
    have hz : i.val=0 := by omega
    simp [hz]

theorem weight_lower_commutator (A : ℕ) :
    weightMatrix A * (raiseMatrix A)ᵀ =
      (raiseMatrix A)ᵀ * weightMatrix A - (2 : ℝ) • (raiseMatrix A)ᵀ := by
  ext i j
  simp only [weightMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.transpose_apply,smul_eq_mul,raiseMatrix]
  by_cases h : j.val+1=i.val
  · rw [ite_eq_left h]
    have hc : (j.val : ℝ)+1=i.val := by exact_mod_cast h
    linear_combination 2*ladder A j.val*hc
  · rw [ite_eq_right h]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TripleLadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def tripleRaise (Q : ℕ) : Matrix (TripleIndex Q) (TripleIndex Q) ℝ :=
  totalRaise Q Q ⊗ₖ (1 : Matrix (Orbital Q) (Orbital Q) ℝ) +
    (1 : Matrix (Orbital Q × Orbital Q) (Orbital Q × Orbital Q) ℝ) ⊗ₖ raiseMatrix Q

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TotalSl2Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem totalRaise_transpose_kronecker (A B : ℕ) :
    (totalRaise A B)ᵀ = (raiseMatrix A)ᵀ ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) ℝ) +
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (raiseMatrix B)ᵀ := by
  ext i j
  simp [totalRaise,Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]

theorem total_weight_lower_commutator (A B : ℕ) :
    totalWeight A B * (totalRaise A B)ᵀ =
      (totalRaise A B)ᵀ * totalWeight A B - (2 : ℝ) • (totalRaise A B)ᵀ := by
  have ha : weightMatrix A*(raiseMatrix A)ᵀ =
      (raiseMatrix A)ᵀ*weightMatrix A+(-2 : ℝ) • (raiseMatrix A)ᵀ := by
    simpa only [sub_eq_add_neg,neg_smul] using weight_lower_commutator A
  have hb : weightMatrix B*(raiseMatrix B)ᵀ =
      (raiseMatrix B)ᵀ*weightMatrix B+(-2 : ℝ) • (raiseMatrix B)ᵀ := by
    simpa only [sub_eq_add_neg,neg_smul] using weight_lower_commutator B
  rw [totalRaise_transpose_kronecker]
  unfold totalWeight
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.mul_one,ha,hb,Matrix.add_kronecker,Matrix.kronecker_add,
    smul_add,neg_smul,sub_eq_add_neg]
  ext i j
  simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,Matrix.kroneckerMap,
    Matrix.of_apply,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Intertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def genericCoupledInclusion (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    Matrix (SpinIndex A B) (Fin (genericCoupledWeight A B z+1)) ℝ :=
  fun i n => genericUnitDescendant A B z hA hB n.val i

noncomputable def physicalCoupledInclusion (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :=
  (-1 : ℂ)^z • (genericCoupledInclusion A B z hA hB).map Complex.ofReal

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basis2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def genericCoupledBasis (A B : ℕ) :
    Matrix (SpinIndex A B) (GenericCoupledIndex A B) ℝ :=
  fun i s => genericUnitDescendant A B s.1.val (by have := s.1.isLt; omega)
    (by have := s.1.isLt; omega) s.2.val i

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def physicalThreeBodyTraceFormula (Q z : ℕ) : ℝ :=
  threeBodyTraceFormula (physicalCouplingCoefficient (2*Q-2) Q) z

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_LevelTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def physicalThreeBodyLevel (Q z T t : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) : ℝ :=
  let a := threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z T t entries
  2*((ell : ℝ)/10^7)*physicalCouplingCoefficient (2*Q-2) Q z T t*a+a^2

end Laughlin.Spin

end OAI
end


