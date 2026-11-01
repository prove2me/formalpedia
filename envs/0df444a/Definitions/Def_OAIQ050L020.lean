-- Prove2me | Definitions.Def_OAIQ050L020
-- name    : OAIQ050L020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:12:44.912008+00:00
-- url     : https://prove2.me/theorems/6437ad48-0593-4b60-ab7e-9e8eb387110a
-- title:
--   Definitions bundle OAIQ050L020 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 14 definitions and 12 theorems. The definitions and types are `OAI.Laughlin.Fock.retainedFourTarget`, `OAI.Laughlin.Fock.sourceA3Form`, `OAI.Laughlin.Fock.sourceA4Form`, `OAI.Laughlin.Fock.sourceEntryThree`, `OAI.Laughlin.Fock.sourceKForm`, `OAI.Laughlin.Fock.sourceRowFourEntry`, `OAI.Laughlin.Fock.sourceRowFourForm`, `OAI.Laughlin.Fock.sourceRowLevel`, `OAI.Laughlin.Fock.sourceRowSquareVector`, `OAI.Laughlin.Spin.complexPairBasis`, `OAI.Laughlin.Spin.pairCoupledBasis`, `OAI.Laughlin.Spin.physicalThreeBodyMatrix`, `OAI.Laughlin.Spin.threeBodyLevelMatrix`, `OAI.Laughlin.Spin.threeBodyLevelVector`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_FourBody_Expansion`, `Laughlin_FourBody_GlobalFock`, `Laughlin_FourBody_Levels`, `Laughlin_FourBody_RetainedComparison`, `Laughlin_FourBody_Square`, `Laughlin_FourBody_Ungroup`, `Laughlin_Operators_SevenSquareAverage`, `Laughlin_Operators_WedgePairRepresentation`, `Laughlin_Pair_CoupledBasis`, `Laughlin_Pair_CoupledParity`, `Laughlin_Polynomial_AntisymmetricCoordinates`, `Laughlin_Spin_Basic`, `Laughlin_Spin_GenericOrthogonality`, `Laughlin_Spin_LadderGroupIntertwining`, `Laughlin_Spin_Sl2Matrix`, `Laughlin_Spin_TotalSl2Matrix`, `Laughlin_ThreeBody_PhysicalMatrix`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinPlanar`; the bundles `OAIQ050L016`, `OAIQ050L017`, `OAIQ050L018` and `OAIQ050L019` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ050L022`; the statements `OAI_Laughlin_Fock_physical_fock_sharp_budget_eventually`, `OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_comparison_eventually`, `OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_haar_real`, `OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50`, `OAI_Laughlin_Fock_sourceA4Form_bessel_bound`, `OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50`, `OAI_Laughlin_Fock_sourceA4Form_retained`, `OAI_Laughlin_Fock_sourceA4Form_retained_bessel_bound`, `OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50`, `OAI.Laughlin.Fock.sourceA4Form_retained_s50`, `OAI_Laughlin_Fock_sourceKForm_decomposition`, `OAI.Laughlin.Fock.sourceKForm_decomposition_s50`, `OAI_Laughlin_Fock_sourceRowFourEntry_physical`, `OAI.Laughlin.Fock.sourceRowFourEntry_physical_s50`, `OAI_Laughlin_Fock_source_rows_normal_two_three`, `OAI.Laughlin.Fock.source_rows_normal_two_three_s50`, `OAI_Laughlin_Fock_source_seven_squares_normal_form`, `OAI.Laughlin.Fock.source_seven_squares_normal_form_s50`, `OAI_Laughlin_Spin_fourBody_haar_multiplicity_block`, `OAI_Laughlin_Spin_physical_threeBody_certificate_haar` and `OAI.Laughlin.Spin.physical_threeBody_certificate_haar_s50`; the proofs of `OAI_Laughlin_Fock_complexThreeGram_sub_one_spectral`, `OAI.Laughlin.Fock.complexThreeGram_sub_one_spectral_s50`, `OAI_Laughlin_Fock_physical_fock_sharp_budget_eventually`, `OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_comparison_eventually`, `OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_haar_real`, `OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50`, `OAI_Laughlin_Fock_sourceA4Form_bessel_bound`, `OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50`, `OAI_Laughlin_Fock_sourceA4Form_retained_bessel_bound`, `OAI.Laughlin.Fock.sourceA4Form_retained_bessel_bound_s50`, `OAI_Laughlin_Fock_sourceKForm_decomposition`, `OAI.Laughlin.Fock.sourceKForm_decomposition_s50`, `OAI_Laughlin_Fock_sourceRowFourEntry_physical`, `OAI.Laughlin.Fock.sourceRowFourEntry_physical_s50`, `OAI_Laughlin_Fock_source_rows_normal_two_three`, `OAI.Laughlin.Fock.source_rows_normal_two_three_s50`, `OAI_Laughlin_Fock_source_seven_squares_normal_form`, `OAI.Laughlin.Fock.source_seven_squares_normal_form_s50`, `OAI_Laughlin_Rotation_physicalPairInclusion_SU2`, `OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50`, `OAI_Laughlin_Spin_fourBody_haar_multiplicity_block`, `OAI_Laughlin_Spin_limitSliceCoefficient_antisymmetric`, `OAI.Laughlin.Spin.limitSliceCoefficient_antisymmetric_s50`, `OAI_Laughlin_Spin_physical_threeBody_certificate_haar`, `OAI.Laughlin.Spin.physical_threeBody_certificate_haar_s50`, `OAI_Laughlin_Spin_physical_threeBody_haar_normalization`, `OAI.Laughlin.Spin.physical_threeBody_haar_normalization_s50`, `OAI_Laughlin_Spin_retainedFourReal_outer_trace`, `OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50`, `OAI_Laughlin_Spin_threeBody_haar_compressed` and `OAI.Laughlin.planar_gap`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Definitions.Def_OAIQ050L018
import Definitions.Def_OAIQ050L019

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sl2Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem raise_mul_transpose_entry (A : ℕ) (i j : Fin (A+1)) :
    (raiseMatrix A * (raiseMatrix A)ᵀ) i j =
      if i=j then ((i.val : ℝ)+1)*(A-i.val : ℕ) else 0 := by
  change (∑ k, raiseMatrix A i k*raiseMatrix A j k) = _
  rw [raiseMatrix_row]
  by_cases hi : i.val < A
  · rw [dite_eq_left hi]
    by_cases hij : i=j
    · subst j
      simp only [raiseMatrix,ite_true]
      unfold ladder
      rw [Real.mul_self_sqrt (by positivity)]
    · have hne : j.val+1 ≠ i.val+1 := by intro h; apply hij; apply Fin.ext; omega
      simp only [raiseMatrix,ite_eq_right hne,ite_eq_right hij,mul_zero]
  · rw [dite_eq_right hi]
    have hz : i.val=A := by omega
    simp [hz]

theorem raise_lower_commutator (A : ℕ) :
    raiseMatrix A * (raiseMatrix A)ᵀ - (raiseMatrix A)ᵀ * raiseMatrix A = weightMatrix A := by
  ext i j
  rw [Matrix.sub_apply,raise_mul_transpose_entry,transpose_mul_raise_entry]
  by_cases hij : i=j
  · subst j
    simp only [ite_true,weightMatrix,Matrix.diagonal_apply_eq]
    rw [Nat.cast_sub (by omega : i.val ≤ A)]
    ring
  · simp [hij,weightMatrix]

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

theorem total_raise_lower_commutator (A B : ℕ) :
    totalRaise A B * (totalRaise A B)ᵀ =
      (totalRaise A B)ᵀ * totalRaise A B + totalWeight A B := by
  have ha : raiseMatrix A*(raiseMatrix A)ᵀ = (raiseMatrix A)ᵀ*raiseMatrix A+weightMatrix A := by
    calc
      _ = (raiseMatrix A*(raiseMatrix A)ᵀ - (raiseMatrix A)ᵀ*raiseMatrix A) +
        (raiseMatrix A)ᵀ*raiseMatrix A := by abel
      _ = _ := by rw [raise_lower_commutator A]; abel
  have hb : raiseMatrix B*(raiseMatrix B)ᵀ = (raiseMatrix B)ᵀ*raiseMatrix B+weightMatrix B := by
    calc
      _ = (raiseMatrix B*(raiseMatrix B)ᵀ - (raiseMatrix B)ᵀ*raiseMatrix B) +
        (raiseMatrix B)ᵀ*raiseMatrix B := by abel
      _ = _ := by rw [raise_lower_commutator B]; abel
  rw [totalRaise_transpose_kronecker,totalRaise_kronecker]
  unfold totalWeight
  simp only [Matrix.add_mul,Matrix.mul_add,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.mul_one,ha,hb,Matrix.add_kronecker,Matrix.kronecker_add]
  abel

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_LadderGroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix Kronecker

theorem ladder_intertwiner_SU2 (A B z J : ℕ) (hz : 2*z+J=A+B)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hs : ∀ i n, i.1.val+i.2.val ≠ z+n.val → W i n=0)
    (hr : totalRaiseComplex A B*W=W*spinRaiseComplex J)
    (hl : (totalRaiseComplex A B)ᵀ*W=W*(spinRaiseComplex J)ᵀ)
    (g : SourceSU2) :
    (sourceSpinRepresentation A g ⊗ₖ sourceSpinRepresentation B g)*W =
      W*sourceSpinRepresentation J g := by
  let P : Matrix (Fin 2) (Fin 2) ℂ → Prop := fun M =>
    (generalSpinMatrix A M ⊗ₖ generalSpinMatrix B M)*W=W*generalSpinMatrix J M
  have h : P g.val := by
    apply Matrix.diagonal_transvection_induction P g.val
    · intro D hD
      have hxy : D 0*D 1=1 := by
        simpa [Matrix.det_diagonal,Fin.prod_univ_two] using hD.trans g.property.2
      have he : D=(fun i : Fin 2 => if i=0 then D 0 else D 1) := by
        funext i
        fin_cases i <;> simp
      change (generalSpinMatrix A (Matrix.diagonal D) ⊗ₖ
        generalSpinMatrix B (Matrix.diagonal D))*W=W*generalSpinMatrix J (Matrix.diagonal D)
      rw [he]
      exact weight_support_diagonal_intertwining A B z J hz W hs _ _ hxy
    · rintro ⟨i,j,hij,c⟩
      change (generalSpinMatrix A (Matrix.transvection i j c) ⊗ₖ
        generalSpinMatrix B (Matrix.transvection i j c))*W=W*generalSpinMatrix J (Matrix.transvection i j c)
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact raising_intertwiner_upper A B J W hr c
      · exact lowering_intertwiner_lower A B J W hl c
      · exact False.elim (hij rfl)
    · intro M L hM hL
      change (generalSpinMatrix A (M*L) ⊗ₖ generalSpinMatrix B (M*L))*W=W*generalSpinMatrix J (M*L)
      rw [generalSpinMatrix_mul,generalSpinMatrix_mul,generalSpinMatrix_mul,Matrix.mul_kronecker_mul]
      change (generalSpinMatrix A M ⊗ₖ generalSpinMatrix B M)*
        (generalSpinMatrix A L ⊗ₖ generalSpinMatrix B L)*W=W*(generalSpinMatrix J M*generalSpinMatrix J L)
      rw [Matrix.mul_assoc,hL,← Matrix.mul_assoc,hM,Matrix.mul_assoc]
  exact h

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericHighest_weight (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    totalWeight A B *ᵥ genericHighest A B z hA hB =
      (genericCoupledWeight A B z : ℝ) • genericHighest A B z hA hB := by
  rw [totalWeight_diagonal]
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  change ((A : ℝ)+B-2*((i.1.val : ℝ)+i.2.val))*genericHighest A B z hA hB i =
    (genericCoupledWeight A B z : ℝ)*genericHighest A B z hA hB i
  by_cases hi : i.1.val+i.2.val=z
  · have hc : (i.1.val : ℝ)+i.2.val=z := by exact_mod_cast hi
    rw [hc]
    congr 1
    unfold genericCoupledWeight
    rw [Nat.cast_sub (by omega : 2*z ≤ A+B)]
    push_cast; ring
  · have he : genericHighest A B z hA hB i = 0 :=
      extendWeightSlice_off A B z hA hB _ i hi
    rw [he]; ring

theorem genericDescendant_norm_pos (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n ≤ genericCoupledWeight A B z) :
    0 < vectorNormSq (genericDescendant A B z hA hB n) := by
  apply descendant_norm_pos (totalRaise A B) (totalWeight A B) ((totalRaise A B)ᵀ)
    (genericHighest A B z hA hB) (genericCoupledWeight A B z) n
  · exact total_raise_lower_commutator _ _
  · exact total_weight_lower_commutator _ _
  · exact Matrix.transpose_transpose _
  · exact genericHighest_weight A B z hA hB
  · exact genericHighest_raising_zero A B z hA hB
  · rw [genericHighest_norm]; norm_num
  · exact hn

theorem genericUnitDescendant_norm (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n ≤ genericCoupledWeight A B z) :
    vectorNormSq (genericUnitDescendant A B z hA hB n) = 1 := by
  have hp := genericDescendant_norm_pos A B z n hA hB hn
  unfold genericUnitDescendant vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  change (Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)))⁻¹ ^ 2 *
    vectorNormSq (genericDescendant A B z hA hB n) = 1
  rw [inv_pow,Real.sq_sqrt (le_of_lt hp),inv_mul_cancel₀ (ne_of_gt hp)]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledTensor_norm (Q r n : ℕ) (hr : r ≤ Q)
    (hn : n ≤ genericCoupledWeight Q Q r) :
    vectorNormSq (pairCoupledTensor Q r hr n) = 1 := by
  unfold pairCoupledTensor vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  have h : ((-1 : ℝ)^r)^2 = 1 := by rw [← pow_mul,mul_comm r 2,pow_mul]; norm_num
  rw [h,one_mul]
  exact genericUnitDescendant_norm Q Q r n hr hr hn

theorem pairCoupledTensor_antisymmetric (Q r n : ℕ) (hr : r ≤ Q) (ho : Odd r)
    (i j : Fin (Q+1)) :
    pairCoupledTensor Q r hr n (j,i) = -pairCoupledTensor Q r hr n (i,j) := by
  have h := genericUnitDescendant_swap Q r n hr (i,j)
  have hs : (-1 : ℝ)^r = -1 := ho.neg_one_pow
  simpa [pairCoupledTensor,hs] using congrArg (fun x : ℝ => -x) h

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_AntisymmetricCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem tensorToWedgePair_norm (Q : ℕ) (f : SpinIndex Q Q → ℝ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) :
    vectorNormSq (tensorToWedgePair Q f) = vectorNormSq f := by
  simpa only [vectorNormSq,pow_two] using antisymmetric_pairing Q f f hf hf

theorem pairCoupledWedge_norm (Q r n : ℕ) (hr : r ≤ Q) (ho : Odd r)
    (hn : n ≤ genericCoupledWeight Q Q r) :
    vectorNormSq (pairCoupledWedge Q r hr n) = 1 := by
  rw [pairCoupledWedge,tensorToWedgePair_norm Q _ (pairCoupledTensor_antisymmetric Q r n hr ho)]
  exact pairCoupledTensor_norm Q r n hr hn

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

theorem genericHighest_orthogonal (A B z w : ℕ) (hzA : z ≤ A) (hzB : z ≤ B) (hwA : w ≤ A) (hwB : w ≤ B)
    (hzw : z ≠ w) :
    (∑ i, genericHighest A B z hzA hzB i*genericHighest A B w hwA hwB i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases he : i.1.val+i.2.val=z
  · have hh : i.1.val+i.2.val ≠ w := by omega
    have hv : genericHighest A B w hwA hwB i = 0 :=
      extendWeightSlice_off A B w hwA hwB _ i hh
    rw [hv,mul_zero]
  · have hv : genericHighest A B z hzA hzB i = 0 :=
      extendWeightSlice_off A B z hzA hzB _ i he
    rw [hv,zero_mul]

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

noncomputable def pairCoupledBasis (Q : ℕ) : Matrix (WedgePairIndex Q) (PairCoupledIndex Q) ℝ :=
  fun i s => pairCoupledWedge Q (oddPairDeficit s.1) (oddPairDeficit_le s.1) s.2.val i

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

noncomputable def complexPairBasis (Q : ℕ) := (pairCoupledBasis Q).map Complex.ofReal

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def threeBodyLevelVector (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ)) :
    PairOrbitalIndex Q → ℝ :=
  (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e • pairOrbitalUnit Q e.1 e.2.1 else 0)).sum

noncomputable def threeBodyLevelMatrix (Q t T : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) :
    Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  let u := pairOrbitalUnit Q t (T-t)
  let a := threeBodyLevelVector Q t T entries
  ((ell : ℝ)/10^7) • (realOuter u a + realOuter a u) + realOuter a a

noncomputable def physicalThreeBodyMatrix (Q : ℕ) :
    Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  (Certificate.rows.map (fun row =>
    (((List.range 16).filter (fun T => row.1 ≤ T)).map
      (fun T => threeBodyLevelMatrix Q row.1 T row.2.1 row.2.2)).sum)).sum

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

noncomputable def sourceRowLevel (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ))
    (x : Space Q) : Space Q :=
  ∑ i, (threeBodyLevelVector Q t T entries i : ℂ) • sourceThreeEnd Q i x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

noncomputable def sourceRowSquareVector (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (x : Space Q) : Space Q :=
  ((row.2.1 : ℂ)/10^7) • sourcePairEnd Q row.1 x +
    ∑ T : RowLevel row.1, create (rowOutputMode Q row.1 hQ T)
      (sourceRowLevel Q row.1 T.val.val row.2.2 x)

noncomputable def sourceRowFourForm (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (x : Space Q) : ℂ :=
  -∑ T : RowLevel row.1, ∑ S : RowLevel row.1,
    occupationInner Q
      (annihilate (rowOutputMode Q row.1 hQ S) (sourceRowLevel Q row.1 T.val.val row.2.2 x))
      (annihilate (rowOutputMode Q row.1 hQ T) (sourceRowLevel Q row.1 S.val.val row.2.2 x))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

noncomputable def sourceEntryThree (Q : ℕ) (e : ℕ × ℕ × ℤ) (x : Space Q) : Space Q :=
  ∑ i, (pairOrbitalUnit Q e.1 e.2.1 i : ℂ) • sourceThreeEnd Q i x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_GlobalFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

noncomputable def sourceA4Form (Q : ℕ) (x : Space Q) : ℝ :=
  ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceFourFamilyEnd Q)
    ((physicalFourBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def retainedFourTarget (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) : ℝ :=
  ∑ d : Fin 23, (contractionForm Q (sourceFourFamilyEnd Q)
    (retainedFourInclusion Q (d.val+1) (by omega) (firstOddPairLabel (d.val+1) (by omega)) *
      (retainedFourInclusion Q (d.val+1) (by omega) (firstOddPairLabel (d.val+1) (by omega)))ᴴ) x).re

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Ungroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

noncomputable def sourceRowFourEntry (Q t : ℕ) (e f : ℕ × ℕ × ℤ) (x : Space Q) : ℂ :=
  -(sourceAlpha t e : ℂ)*(sourceAlpha t f : ℂ) * occupationInner Q
    (boundedAnnihilate Q (f.1+f.2.1-t) (sourceEntryThree Q e x))
    (boundedAnnihilate Q (e.1+e.2.1-t) (sourceEntryThree Q f x))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_SevenSquareAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

noncomputable def sourceKForm (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) : ℝ :=
  ((2*Q-2+1 : ℕ) : ℝ) * ∫ g, (Certificate.rows.map (fun row =>
    occupationNormSq Q (sourceRowSquareVector Q hQ row (exteriorRotation Q g⁻¹ x)))).sum ∂sourceHaar

noncomputable def sourceA3Form (Q : ℕ) (x : Space Q) : ℝ :=
  ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceThreeEnd Q)
    ((physicalThreeBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re

end Laughlin.Fock

end OAI
end


