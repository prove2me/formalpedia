-- Prove2me | Definitions.Def_OAIQ050L014
-- name    : OAIQ050L014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:10:08.87781+00:00
-- url     : https://prove2.me/theorems/76cf2827-dc6a-4197-b697-61a98dab7bf9
-- title:
--   Definitions bundle OAIQ050L014 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 15 definitions and 11 theorems. The definitions and types are `OAI.Laughlin.Spin.RetainedFourColumns`, `OAI.Laughlin.Spin.couplingArray`, `OAI.Laughlin.Spin.highestReadout`, `OAI.Laughlin.Spin.limitSlaterCoefficient`, `OAI.Laughlin.Spin.limitSlaterTerm`, `OAI.Laughlin.Spin.limitThreeBodyTraceFormula`, `OAI.Laughlin.Spin.localFourCountEquiv`, `OAI.Laughlin.Spin.localFourIndexEquiv`, `OAI.Laughlin.Spin.pairTensorLower`, `OAI.Laughlin.Spin.pairTensorRaise`, `OAI.Laughlin.Spin.raiseSlice`, `OAI.Laughlin.Spin.rationalThreeBodyLevel`, `OAI.Laughlin.Spin.threeBodyInner`, `OAI.Laughlin.Spin.threeBodyTraceFormula`, `OAI.Laughlin.Spin.totalWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_FourBody_RetainedSum`, `Laughlin_FourBody_SlaterCoefficient`, `Laughlin_FourBody_SlaterRadical`, `Laughlin_Operators_GramReadout`, `Laughlin_Operators_LocalFourCardinality`, `Laughlin_Operators_LocalFourIndexEquiv`, `Laughlin_Pair_CoupledParity`, `Laughlin_Pair_TensorLower`, `Laughlin_Pair_TensorRaise`, `Laughlin_Spin_Array`, `Laughlin_Spin_Highest2`, `Laughlin_Spin_HighestSpace`, `Laughlin_Spin_Sl2DescendantNorm`, `Laughlin_Spin_TotalSl2Matrix`, `Laughlin_ThreeBody_TraceCertificate`, `Laughlin_ThreeBody_TraceLimit`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinPlanar`; the bundles `OAIQ050L000`, `OAIQ050L001`, `OAIQ050L005`, `OAIQ050L006`, `OAIQ050L007` and `OAIQ050L008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L018` and `OAIQ050L019`; the statements `OAI_Laughlin_Fock_fourCopyForm_allowance_identity`, `OAI_Laughlin_Fock_limitFourCopyEnd_Slater_readout`, `OAI_Laughlin_Fock_physicalFourCopyEnd_truncated`, `OAI_Laughlin_Fock_physical_threeBody_tail_sum`, `OAI_Laughlin_Fock_restrictedSpherePairEnd_high_degree`, `OAI_Laughlin_Fock_retainedFourAllowance_bessel_bound`, `OAI_Laughlin_Fock_source_fourBody_uniform_transfer`, `OAI_Laughlin_Spin_coupledBasis_eigen`, `OAI_Laughlin_Spin_pairCoefficient_tensor_lowering`, `OAI.Laughlin.Spin.pairCoefficient_tensor_lowering_s50`, `OAI_Laughlin_Spin_pairCoefficient_tensor_raising`, `OAI.Laughlin.Spin.pairCoefficient_tensor_raising_s50`, `OAI_Laughlin_Spin_pairTensorLower_weight`, `OAI.Laughlin.Spin.pairTensorLower_weight_s50`, `OAI_Laughlin_Spin_source_coupling_polynomial_tendsto`, `OAI.Laughlin.Spin.source_coupling_polynomial_tendsto_s50`, `OAI_Laughlin_Spin_source_fourBody_Slater_coefficient` and `OAI.Laughlin.Spin.source_fourBody_Slater_coefficient_s50`; the proofs of `OAI_Laughlin_Fock_fourCopyForm_allowance_identity`, `OAI_Laughlin_Fock_limitFourColumn_physical_L`, `OAI.Laughlin.Fock.limitFourColumn_physical_L_s50`, `OAI_Laughlin_Fock_limitFourCopyEnd_Slater_readout`, `OAI_Laughlin_Fock_limitFourCopyEnd_local_sum`, `OAI.Laughlin.Fock.limitFourCopyEnd_local_sum_s50`, `OAI_Laughlin_Fock_physicalFourCopyEnd_truncated`, `OAI_Laughlin_Fock_physical_fourBody_total_bessel_haar_allowance`, `OAI.Laughlin.Fock.physical_fourBody_total_bessel_haar_allowance_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_bound`, `OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50`, `OAI_Laughlin_Fock_physical_threeBody_tail_sum`, `OAI_Laughlin_Fock_restrictedSpherePairEnd_high_degree`, `OAI_Laughlin_Fock_retainedFourAllowance_bessel_bound`, `OAI_Laughlin_Fock_source_fourBody_uniform_transfer`, `OAI_Laughlin_Fock_threeBodyGram_highest_first_coordinate`, `OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50`, `OAI_Laughlin_Spin_fourWeightSlice_sum`, `OAI.Laughlin.Spin.fourWeightSlice_sum_s50`, `OAI_Laughlin_Spin_pairCoefficient_tensor_lowering`, `OAI.Laughlin.Spin.pairCoefficient_tensor_lowering_s50`, `OAI_Laughlin_Spin_pairCoefficient_tensor_raising`, `OAI.Laughlin.Spin.pairCoefficient_tensor_raising_s50`, `OAI_Laughlin_Spin_pairTensorLower_weight`, `OAI.Laughlin.Spin.pairTensorLower_weight_s50`, `OAI_Laughlin_Spin_relativeHighest_tendsto`, `OAI.Laughlin.Spin.relativeHighest_tendsto_s50`, `OAI_Laughlin_Spin_source_coupling_polynomial_tendsto`, `OAI.Laughlin.Spin.source_coupling_polynomial_tendsto_s50`, `OAI_Laughlin_Spin_source_fourBody_Slater_coefficient`, `OAI.Laughlin.Spin.source_fourBody_Slater_coefficient_s50`, `OAI_Laughlin_Spin_source_fourBody_local_normalization` and `OAI.Laughlin.Spin.source_fourBody_local_normalization_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001
import Definitions.Def_OAIQ050L005
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007
import Definitions.Def_OAIQ050L008

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Highest2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem ladder_pos (A p : ℕ) (hp : p < A) : 0 < ladder A p := by
  unfold ladder
  apply Real.sqrt_pos.mpr
  have h : (0 : ℝ) < (A-p : ℕ) := by exact_mod_cast (show 0 < A-p by omega)
  positivity

theorem ladder_div_sqrt_choose (A p : ℕ) (hp : p < A) :
    ladder A p / Real.sqrt (A.choose (p+1) : ℝ) =
      ((p : ℝ)+1) / Real.sqrt (A.choose p : ℝ) := by
  have h₀ : 0 < (A.choose p : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : p ≤ A)
  have h₁ : 0 < (A.choose (p+1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : p+1 ≤ A)
  apply (div_eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr h₁))
    (ne_of_gt (Real.sqrt_pos.mpr h₀))).mpr
  have hc := choose_step_real A p (by omega)
  have he : (ladder A p * Real.sqrt (A.choose p : ℝ))^2 =
      (((p : ℝ)+1)*Real.sqrt (A.choose (p+1) : ℝ))^2 := by
    unfold ladder
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    nlinarith [hc]
  have hn₀ : 0 ≤ ladder A p * Real.sqrt (A.choose p : ℝ) :=
    mul_nonneg (le_of_lt (ladder_pos A p hp)) (Real.sqrt_nonneg _)
  have hn₁ : 0 ≤ ((p : ℝ)+1)*Real.sqrt (A.choose (p+1) : ℝ) := by positivity
  nlinarith

theorem highestRaw_raising (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p < z) :
    ladder A p * highestRaw A B z (p+1) +
      ladder B (z-p-1) * highestRaw A B z p = 0 := by
  have hpA : p < A := by omega
  have hkB : z-p-1 < B := by omega
  have hk : z-(p+1) = z-p-1 := by omega
  have hk' : z-p = (z-p-1)+1 := by omega
  have hca : (Real.sqrt (A.choose p : ℝ)) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr; exact_mod_cast Nat.choose_pos (by omega : p ≤ A)
  have hcb : (Real.sqrt (B.choose (z-p-1) : ℝ)) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr; exact_mod_cast Nat.choose_pos (by omega : z-p-1 ≤ B)
  simp only [highestRaw,ite_eq_left (show p+1 ≤ z by omega),ite_eq_left (show p ≤ z by omega),hk]
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hleft := ladder_div_sqrt_choose A p hpA
  have hright := ladder_div_sqrt_choose B (z-p-1) hkB
  rw [← hk'] at hright
  have hz := choose_step_real z p (by omega)
  have castk : ((z-p-1 : ℕ) : ℝ)+1 = (z-p : ℕ) := by exact_mod_cast hk'.symm
  rw [castk] at hright
  calc
    _ = (-1 : ℝ)^(p+1)*(z.choose (p+1) : ℝ) /
          Real.sqrt (B.choose (z-p-1) : ℝ) *
          (ladder A p / Real.sqrt (A.choose (p+1) : ℝ)) +
        (-1 : ℝ)^p*(z.choose p : ℝ) / Real.sqrt (A.choose p : ℝ) *
          (ladder B (z-p-1) / Real.sqrt (B.choose (z-p) : ℝ)) := by ring
    _ = _ := by rw [hleft,hright]
    _ = 0 := by rw [pow_succ]; field_simp; linear_combination -((-1 : ℝ)^p)*hz

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sl2DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem descendant_norm_step (R H L : Matrix I I ℝ) (v : I → ℝ) (μ : ℝ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L) (ht : Lᵀ=R)
    (hv : H *ᵥ v=μ • v) (hr : R *ᵥ v=0) (n : ℕ) :
    vectorNormSq (L^(n+1) *ᵥ v) = (((n : ℝ)+1)*(μ-n))*vectorNormSq (L^n *ᵥ v) := by
  have hs : L^(n+1) *ᵥ v = L *ᵥ (L^n *ᵥ v) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  unfold vectorNormSq
  simp only [pow_two]
  conv_lhs => arg 2; ext i; arg 1; rw [hs]
  rw [matrix_transpose_pairing,ht,descendant_raising R H L v μ hRL hHL hv hr n]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem descendant_norm_pos (R H L : Matrix I I ℝ) (v : I → ℝ) (μ n : ℕ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L) (ht : Lᵀ=R)
    (hv : H *ᵥ v=(μ : ℝ) • v) (hr : R *ᵥ v=0)
    (hnorm : 0 < vectorNormSq v) (hn : n ≤ μ) : 0 < vectorNormSq (L^n *ᵥ v) := by
  induction n with
  | zero => simpa using hnorm
  | succ n ih =>
    rw [descendant_norm_step R H L v μ hRL hHL ht hv hr n]
    have hp : (n : ℝ) < μ := by exact_mod_cast (show n < μ by omega)
    have hi := ih (by omega)
    positivity

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_TensorLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def pairTensorLower (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  (if h : 0 < x.val then ladder Q (x.val-1) *
    pairCoefficient Q p ⟨x.val-1,by omega⟩ y else 0) +
  (if h : 0 < y.val then ladder Q (y.val-1) *
    pairCoefficient Q p x ⟨y.val-1,by omega⟩ else 0)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_TensorRaise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def pairTensorRaise (Q p : ℕ) (x y : Fin (Q+1)) : ℝ :=
  (if h : x.val < Q then ladder Q x.val *
    pairCoefficient Q p ⟨x.val+1,by omega⟩ y else 0) +
  (if h : y.val < Q then ladder Q y.val *
    pairCoefficient Q p x ⟨y.val+1,by omega⟩ else 0)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_HighestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_ne_zero (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p ≤ z) : highestRaw A B z p ≠ 0 := by
  rw [highestRaw,ite_eq_left hp]
  apply div_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hp))
  · apply ne_of_gt; apply Real.sqrt_pos.mpr
    have ha : 0 < (A.choose p : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : p ≤ A)
    have hb : 0 < (B.choose (z-p) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : z-p ≤ B)
    positivity

theorem highestNorm_pos (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    0 < highestNorm A B z := by
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos'
  · intro p hp; exact sq_nonneg _
  · exact ⟨0,Finset.mem_range.mpr (by omega),sq_pos_of_ne_zero
      (highestRaw_ne_zero A B z 0 hA hB (by omega))⟩

theorem highestUnit_norm (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (∑ p ∈ Finset.range (z+1), (highestUnit A B z p)^2) = 1 := by
  simp only [highestUnit,div_pow,← Finset.sum_div]
  rw [highestNorm,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  apply div_self
  have h := highestNorm_pos A B z hA hB
  exact ne_of_gt (Real.sqrt_pos.mp h)

theorem highestUnit_raising (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p < z) :
    ladder A p*highestUnit A B z (p+1)+ladder B (z-p-1)*highestUnit A B z p = 0 := by
  simp only [highestUnit,← mul_div_assoc,← add_div]
  rw [highestRaw_raising A B z p hA hB hp,zero_div]

noncomputable def raiseSlice (A B z : ℕ) (f : Fin (z+1) → ℝ) (p : Fin z) : ℝ :=
  ladder A p.val * f ⟨p.val+1,by omega⟩ +
    ladder B (z-p.val-1)*f ⟨p.val,by omega⟩

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

noncomputable def totalWeight (A B : ℕ) : Matrix (SpinIndex A B) (SpinIndex A B) ℝ :=
  weightMatrix A ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) ℝ) +
    (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ weightMatrix B

theorem totalWeight_diagonal (A B : ℕ) :
    totalWeight A B = Matrix.diagonal (fun i : SpinIndex A B =>
      (A : ℝ)+B-2*((i.1.val : ℝ)+i.2.val)) := by
  ext i j
  by_cases h₁ : i.1=j.1 <;> by_cases h₂ : i.2=j.2 <;>
    simp [totalWeight,weightMatrix,Matrix.kroneckerMap,
      Matrix.one_apply,Matrix.diagonal_apply,Prod.ext_iff,h₁,h₂]
  ring

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

theorem highestUnit_reverse (Q r p : ℕ) (hp : p ≤ r) :
    highestUnit Q Q r (r-p) = (-1 : ℝ)^r * highestUnit Q Q r p := by
  unfold highestUnit highestRaw
  rw [ite_eq_left (by omega : r-p ≤ r),ite_eq_left hp,Nat.sub_sub_self hp,
    Nat.choose_symm hp,sign_reverse r p hp]
  rw [mul_comm (Q.choose (r-p) : ℝ) (Q.choose p : ℝ)]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_GramReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def highestReadout (Q z : ℕ) : ℝ :=
  if z = 0 then -highestUnit (2*Q-2) Q z 0 else
    -highestUnit (2*Q-2) Q z (z-1) * (z : ℝ) *
      Real.sqrt ((Q.choose z : ℝ)/((Q : ℝ)*((2*Q-2).choose (z-1) : ℝ))) +
    highestUnit (2*Q-2) Q z z * ((z : ℝ)-1) *
      Real.sqrt ((Q.choose z : ℝ)/((2*Q-2).choose z : ℝ))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev RetainedFourColumns (Q : ℕ) :=
  Σ d : Fin 23, OddPairLabel (d.val+1) × Fin (fourSpinWeight Q (d.val+1)+1)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Array
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def couplingArray (A B z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => (-1 : ℝ)^z * highestUnit A B z p
  | n+1, p =>
      ((if p=0 then 0 else ladder A (p-1)*couplingArray A B z n (p-1)) +
       (if p ≤ z+n then ladder B (z+n-p)*couplingArray A B z n p else 0)) /
        Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SlaterRadical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def limitSlaterTerm (D r x y j k : ℕ) : ℝ :=
  (Real.sqrt 2 * pairLimitCoefficient (x+y-1) x y) *
    fourBodyLimitCoefficient r D D (x+y-1) j k

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SlaterCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def limitSlaterCoefficient (D r a b c d : ℕ) : ℝ :=
  limitSlaterTerm D r a b c d - limitSlaterTerm D r a c b d +
  limitSlaterTerm D r a d b c + limitSlaterTerm D r b c a d -
  limitSlaterTerm D r b d a c + limitSlaterTerm D r c d a b

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_LocalFourIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

def localFourIndexEquiv (Q D : ℕ) (hDQ : D ≤ Q) :
    LocalFourIndex D ≃ EmbeddedLocalFourIndex Q D where
  toFun b := ⟨(b.val.1,⟨b.val.2.1.val,by omega⟩,⟨b.val.2.2.val,by omega⟩),b.property⟩
  invFun b := ⟨(b.val.1,⟨b.val.2.1.val,by have := b.property.1; omega⟩,
    ⟨b.val.2.2.val,by have := b.property.1; omega⟩),b.property⟩
  left_inv b := by cases b; rfl
  right_inv b := by cases b; rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_LocalFourCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

def localFourCountEquiv (D : ℕ) :
    LocalFourIndex D ≃ (n : Fin (D+1)) × Fin ((n.val+1)/2) where
  toFun b := ⟨⟨b.val.2.1.val+b.val.2.2.val,by have := b.property.1; omega⟩,
    ⟨b.val.2.1.val,by dsimp; have := b.property.2; omega⟩⟩
  invFun b := ⟨(⟨D-b.1.val,by omega⟩,⟨b.2.val,by have := b.2.isLt; omega⟩,
    ⟨b.1.val-b.2.val,by omega⟩),by
      have := b.2.isLt
      constructor
      · dsimp; omega
      · change b.2.val < b.1.val-b.2.val
        omega⟩
  left_inv b := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; dsimp; have := b.property.1; omega
    · apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp; omega
  right_inv b := by
    rcases b with ⟨n,j⟩
    have hj : j.val ≤ n.val := by have := j.isLt; omega
    dsimp
    have hn : j.val+(n.val-j.val)=n.val := by omega
    apply Sigma.ext
    · exact Fin.ext hn
    · apply (Fin.heq_ext_iff (by dsimp; rw [hn])).mpr
      rfl

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

noncomputable def threeBodyInner (s : ℕ → ℕ → ℕ → ℝ) (z T t : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) : ℝ :=
  (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e * s z T e.1 else 0)).sum

noncomputable def threeBodyTraceFormula (s : ℕ → ℕ → ℕ → ℝ) (z : ℕ) : ℝ :=
  (Certificate.rows.map (fun row =>
    (((List.range 16).filter (fun T => max z row.1 ≤ T)).map (fun T =>
      let a := threeBodyInner s z T row.1 row.2.2
      2*((row.2.1 : ℝ)/10^7)*s z T row.1*a+a^2)).sum)).sum

noncomputable def limitThreeBodyTraceFormula (z : ℕ) : ℝ :=
  threeBodyTraceFormula (fun z T p => couplingPolynomialCoefficient
    (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def rationalThreeBodyLevel (z T : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) : ℚ :=
  ((2 : ℚ)^z * (T.choose z : ℚ) / ((3 : ℚ)^T * (2 : ℚ)^row.1 * (T.choose row.1 : ℚ))) *
    (Certificate.X row.2.2 z T : ℚ) *
    ((Certificate.X row.2.2 z T : ℚ)+2*(row.2.1 : ℚ)*(Certificate.U 2 z T row.1 : ℚ))

end Laughlin.Spin

end OAI
end


