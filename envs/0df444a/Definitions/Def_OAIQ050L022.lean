-- Prove2me | Definitions.Def_OAIQ050L022
-- name    : OAIQ050L022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:14:35.600488+00:00
-- url     : https://prove2.me/theorems/af960386-a409-4117-b7e9-0936df78b378
-- title:
--   Definitions bundle OAIQ050L022 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 13 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_Operators_WedgePairRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/WedgePairRepresentation.lean), [`Laughlin_Pair_CoupledBasis`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/CoupledBasis.lean), [`Laughlin_Pair_CoupledIsometry`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/CoupledIsometry.lean), [`Laughlin_Spin_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Basic.lean), [`Laughlin_Spin_Endpoint`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Endpoint.lean), [`Laughlin_Spin_GenericNormalizedLadder`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/GenericNormalizedLadder.lean), [`Laughlin_Spin_GenericOrthogonality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/GenericOrthogonality.lean), [`Laughlin_Spin_Intertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Intertwining.lean).
--
--   **Imports.** It imports the bundles `OAIQ050L020` and `OAIQ050L021` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ050L024`; the proofs of `OAI_Laughlin_Fock_fourPairEmbedding_contract`, `OAI.Laughlin.Fock.fourPairEmbedding_contract_s50`, `OAI_Laughlin_Spin_fourCoupledBasis_complex_complete`, `OAI.Laughlin.Spin.fourCoupledBasis_complex_complete_s50`, `OAI_Laughlin_Spin_fourPairEmbedding_resolution`, `OAI.Laughlin.Spin.fourPairEmbedding_resolution_s50`, `OAI_Laughlin_Spin_physicalThreeBodyTraceFormula_tendsto`, `OAI.Laughlin.Spin.physicalThreeBodyTraceFormula_tendsto_s50`, `OAI_Laughlin_Spin_source_fourBody_coefficient_tendsto`, `OAI.Laughlin.Spin.source_fourBody_coefficient_tendsto_s50`, `OAI_Laughlin_Spin_source_fourBody_coefficients_norm`, `OAI.Laughlin.Spin.source_fourBody_coefficients_norm_s50`, `OAI_Laughlin_Spin_source_fourBody_local_orthonormal` and `OAI.Laughlin.Spin.source_fourBody_local_orthonormal_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L020
import Definitions.Def_OAIQ050L021

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericDescendant_norm_step (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    vectorNormSq (genericDescendant A B z hA hB (n+1)) =
      (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        vectorNormSq (genericDescendant A B z hA hB n) := by
  exact descendant_norm_step (totalRaise A B) (totalWeight A B) ((totalRaise A B)ᵀ)
    (genericHighest A B z hA hB) (genericCoupledWeight A B z)
    (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (genericHighest_weight A B z hA hB)
    (genericHighest_raising_zero A B z hA hB) n

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_GenericNormalizedLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericUnitDescendant_lowering (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n < genericCoupledWeight A B z) :
    (totalRaise A B)ᵀ *ᵥ genericUnitDescendant A B z hA hB n =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) •
        genericUnitDescendant A B z hA hB (n+1) := by
  have hp := genericDescendant_norm_pos A B z n hA hB (by omega)
  have hp₁ := genericDescendant_norm_pos A B z (n+1) hA hB (by omega)
  have hnreal : (n : ℝ) < genericCoupledWeight A B z := by exact_mod_cast hn
  have hc : 0 < ((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n) := by positivity
  have hden : Real.sqrt (vectorNormSq (genericDescendant A B z hA hB (n+1))) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)) := by
    rw [genericDescendant_norm_step A B z n hA hB,Real.sqrt_mul (le_of_lt hc)]
  have hs : (Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)))⁻¹ =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        (Real.sqrt (vectorNormSq (genericDescendant A B z hA hB (n+1))))⁻¹ := by
    rw [hden,mul_inv_rev]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hc)]
  unfold genericUnitDescendant
  rw [Matrix.mulVec_smul,← genericDescendant_succ,smul_smul,hs]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_GenericOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericDescendant_orthogonal (A B z w n m : ℕ) (hzA : z ≤ A) (hzB : z ≤ B) (hwA : w ≤ A) (hwB : w ≤ B)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, genericDescendant A B z hzA hzB n i*genericDescendant A B w hwA hwB m i) = 0 := by
  apply descendants_orthogonal (totalRaise A B) (totalWeight A B)
    ((totalRaise A B)ᵀ) (genericHighest A B z hzA hzB) (genericHighest A B w hwA hwB)
    (genericCoupledWeight A B w) (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (genericHighest_weight A B w hwA hwB)
    (genericHighest_raising_zero A B z hzA hzB) (genericHighest_raising_zero A B w hwA hwB) n m
  rcases hne with h | h
  · exact Or.inl (genericHighest_orthogonal A B z w hzA hzB hwA hwB h)
  · exact Or.inr h

theorem genericUnitDescendant_orthogonal (A B z w n m : ℕ) (hzA : z ≤ A) (hzB : z ≤ B) (hwA : w ≤ A) (hwB : w ≤ B)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, genericUnitDescendant A B z hzA hzB n i *
      genericUnitDescendant A B w hwA hwB m i) = 0 := by
  unfold genericUnitDescendant
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = (Real.sqrt (vectorNormSq (genericDescendant A B z hzA hzB n)))⁻¹ *
      (Real.sqrt (vectorNormSq (genericDescendant A B w hwA hwB m)))⁻¹ *
      (∑ i, genericDescendant A B z hzA hzB n i*genericDescendant A B w hwA hwB m i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by rw [genericDescendant_orthogonal A B z w n m hzA hzB hwA hwB hne,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledTensor_orthogonal (Q r s n m : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hne : r ≠ s ∨ n ≠ m) :
    (∑ i, pairCoupledTensor Q r hr n i * pairCoupledTensor Q s hs m i) = 0 := by
  unfold pairCoupledTensor
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = ((-1 : ℝ)^r * (-1 : ℝ)^s) *
      (∑ i, genericUnitDescendant Q Q r hr hr n i * genericUnitDescendant Q Q s hs hs m i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by rw [genericUnitDescendant_orthogonal Q Q r s n m hr hr hs hs hne,mul_zero]

theorem pairCoupledWedge_orthogonal (Q r s n m : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s ∨ n ≠ m) :
    (∑ i, pairCoupledWedge Q r hr n i * pairCoupledWedge Q s hs m i) = 0 := by
  rw [pairCoupledWedge,pairCoupledWedge,antisymmetric_pairing Q _ _
    (pairCoupledTensor_antisymmetric Q r n hr hor) (pairCoupledTensor_antisymmetric Q s m hs hos)]
  exact pairCoupledTensor_orthogonal Q r s n m hr hs hne

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledBasis_isometry (Q : ℕ) :
    (pairCoupledBasis Q)ᵀ * pairCoupledBasis Q = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,pairCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      pairCoupledWedge_norm Q (oddPairDeficit s.1) s.2.val (oddPairDeficit_le s.1)
        (oddPairDeficit_odd s.1) (by have := s.2.isLt; omega)
  · rw [ite_eq_right h]
    apply pairCoupledWedge_orthogonal _ _ _ _ _ _ _ (oddPairDeficit_odd s.1) (oddPairDeficit_odd t.1)
    rcases s with ⟨r,n⟩
    rcases t with ⟨s,m⟩
    by_cases hrs : r=s
    · subst s
      right
      intro he
      exact h (by have hn : n=m := Fin.ext he; subst m; rfl)
    · left
      intro he
      apply hrs
      apply Fin.ext
      dsimp [oddPairDeficit] at he
      omega

theorem pairCoupledBasis_complete (Q : ℕ) :
    pairCoupledBasis Q * (pairCoupledBasis Q)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := PairCoupledIndex Q) (n := WedgePairIndex Q)
    (R := ℝ) (pairCoupledIndex_card Q)).mp (pairCoupledBasis_isometry Q)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericDescendant_past_lowest (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    genericDescendant A B z hA hB (genericCoupledWeight A B z+1)=0 := by
  have h := genericDescendant_norm_step A B z (genericCoupledWeight A B z) hA hB
  simp only [sub_self,mul_zero,zero_mul] at h
  funext i
  have hi : (genericDescendant A B z hA hB (genericCoupledWeight A B z+1) i)^2 ≤
      vectorNormSq (genericDescendant A B z hA hB (genericCoupledWeight A B z+1)) :=
    Finset.single_le_sum (fun k hk => sq_nonneg _) (Finset.mem_univ i)
  rw [h] at hi
  change genericDescendant A B z hA hB (genericCoupledWeight A B z+1) i=0
  nlinarith [sq_nonneg (genericDescendant A B z hA hB (genericCoupledWeight A B z+1) i)]

theorem genericUnitDescendant_lowest (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (totalRaise A B)ᵀ *ᵥ genericUnitDescendant A B z hA hB (genericCoupledWeight A B z)=0 := by
  unfold genericUnitDescendant
  rw [Matrix.mulVec_smul,← genericDescendant_succ,genericDescendant_past_lowest,smul_zero]

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

theorem genericCoupledInclusion_lowering (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (totalRaise A B)ᵀ*genericCoupledInclusion A B z hA hB =
      genericCoupledInclusion A B z hA hB*(raiseMatrix (genericCoupledWeight A B z))ᵀ := by
  funext i n
  change ((totalRaise A B)ᵀ *ᵥ genericUnitDescendant A B z hA hB n.val) i =
    ∑ k, genericUnitDescendant A B z hA hB k.val i * raiseMatrix (genericCoupledWeight A B z) n k
  conv_rhs => simp only [mul_comm (genericUnitDescendant A B z hA hB _ i)]
  rw [raiseMatrix_row]
  by_cases hn : n.val < genericCoupledWeight A B z
  · rw [dite_eq_left hn]
    have h := congrFun (genericUnitDescendant_lowering A B z n.val hA hB hn) i
    simpa [ladder,Nat.cast_sub (Nat.le_of_lt hn)] using h
  · rw [dite_eq_right hn]
    have hz : n.val=genericCoupledWeight A B z := by omega
    rw [hz,genericUnitDescendant_lowest]
    rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WedgePairRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem complexPairBasis_isometry (Q : ℕ) :
    (complexPairBasis Q)ᴴ * complexPairBasis Q = 1 := by
  rw [complexPairBasis,real_matrix_adjoint]
  exact real_matrix_inverse_complex _ _ (pairCoupledBasis_isometry Q)

theorem complexPairBasis_complete (Q : ℕ) :
    complexPairBasis Q * (complexPairBasis Q)ᴴ = 1 := by
  rw [complexPairBasis,real_matrix_adjoint]
  exact real_matrix_inverse_complex _ _ (pairCoupledBasis_complete Q)

end Laughlin.Spin

end OAI
end


