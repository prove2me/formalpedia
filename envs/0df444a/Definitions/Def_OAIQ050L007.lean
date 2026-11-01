-- Prove2me | Definitions.Def_OAIQ050L007
-- name    : OAIQ050L007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:07:40.790311+00:00
-- url     : https://prove2.me/theorems/27d77500-7c88-438d-af2e-409addef4fce
-- title:
--   Definitions bundle OAIQ050L007 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 28 definitions and 14 theorems. The definitions and types are `OAI.Laughlin.Fock.exteriorScaling`, `OAI.Laughlin.Fock.fockInclusion`, `OAI.Laughlin.Fock.includedOccupations`, `OAI.Laughlin.Fock.limitFourEnd`, `OAI.Laughlin.Fock.limitPairEnd`, `OAI.Laughlin.Fock.limitPairWindow`, `OAI.Laughlin.Fock.localOccupation`, `OAI.Laughlin.Fock.modeInclusion`, `OAI.Laughlin.Fock.occupationFourLabels`, `OAI.Laughlin.Fock.occupationNormSq`, `OAI.Laughlin.Fock.orbitalDual`, `OAI.Laughlin.Fock.orbitalScaling`, `OAI.Laughlin.Fock.pairEnd`, `OAI.Laughlin.Fock.physicalPairRowMatrix`, `OAI.Laughlin.Fock.sliceOrbital`, `OAI.Laughlin.Fock.vectorAnnihilate`, `OAI.Laughlin.Fock.weightedFourEnd`, `OAI.Laughlin.Rotation.conjugateOrbit`, `OAI.Laughlin.Rotation.entrywiseIntegral`, `OAI.Laughlin.Rotation.matrixIntegral`, `OAI.Laughlin.Rotation.polynomialMatrixCoeff`, `OAI.Laughlin.Rotation.polynomialMatrixDerivative`, `OAI.Laughlin.Rotation.tensorPermutation`, `OAI.Laughlin.Spin.castSpinColumns`, `OAI.Laughlin.Spin.fourSpinWeight`, `OAI.Laughlin.Spin.genericCoupledWeight`, `OAI.Laughlin.Spin.realOuter`, `OAI.Laughlin.Spin.sourceCopyWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_Asymptotics_TruncatedScaling`, `Laughlin_Exterior_FourConjugation`, `Laughlin_Exterior_OccupationMetric`, `Laughlin_Exterior_PairConjugation`, `Laughlin_Exterior_Scaling`, `Laughlin_Exterior_VectorAdjoint`, `Laughlin_Fock_FourLabels`, `Laughlin_Fock_ModeEmbedding`, `Laughlin_FourBody_RadicalCancellation`, `Laughlin_FourBody_RetainedInclusions`, `Laughlin_FourBody_WeightedReadout`, `Laughlin_Operators_CollectionAnnihilatorBound`, `Laughlin_Polynomial_PolynomialMatrixODE`, `Laughlin_Polynomial_SymmetricTensorOrbit`, `Laughlin_Spin_Basic`, `Laughlin_Spin_Compact`, `Laughlin_Spin_MatrixAverage`, `Laughlin_Spin_Sandwich`, `Laughlin_Spin_TwoBodyCertificateHaar`, `Laughlin_ThreeBody_GramSlice`, `Laughlin_ThreeBody_RankTrace`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinPlanar`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L011`, `OAIQ050L012`, `OAIQ050L013` and `OAIQ050L014`; the statements `OAI_Laughlin_Fock_fockInclusion_normSq`, `OAI.Laughlin.Fock.fockInclusion_normSq_s50`, `OAI_Laughlin_Fock_limitPairEnd_four_create`, `OAI.Laughlin.Fock.limitPairEnd_four_create_s50`, `OAI_Laughlin_Fock_pairEnd_create_create`, `OAI.Laughlin.Fock.pairEnd_create_create_s50`, `OAI_Laughlin_Fock_pairEnd_three_create`, `OAI.Laughlin.Fock.pairEnd_three_create_s50`, `OAI_Laughlin_Fock_row_normal_square`, `OAI.Laughlin.Fock.row_normal_square_s50`, `OAI_Laughlin_Fock_vectorCreate_adjoint`, `OAI.Laughlin.Fock.vectorCreate_adjoint_s50`, `OAI_Laughlin_Fock_weightedFourEnd_readout` and `OAI.Laughlin.Fock.weightedFourEnd_readout_s50`; the proofs of `OAI_Laughlin_Fock_finiteFourMiddle_tendsto`, `OAI_Laughlin_Fock_fockInclusion_normSq`, `OAI.Laughlin.Fock.fockInclusion_normSq_s50`, `OAI_Laughlin_Fock_limitPairEnd_four_create`, `OAI.Laughlin.Fock.limitPairEnd_four_create_s50`, `OAI_Laughlin_Fock_occupationInner_scalar_wedge_zero`, `OAI.Laughlin.Fock.occupationInner_scalar_wedge_zero_s50`, `OAI_Laughlin_Fock_pairEnd_create_create`, `OAI.Laughlin.Fock.pairEnd_create_create_s50`, `OAI_Laughlin_Fock_pairEnd_three_create`, `OAI.Laughlin.Fock.pairEnd_three_create_s50`, `OAI_Laughlin_Fock_physicalLimitError_eq`, `OAI_Laughlin_Spin_source_fourBody_error_matrix` and `OAI.Laughlin.Spin.source_fourBody_error_matrix_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinPlanar

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def orbitalScaling (Q : ℕ) (d : Fin (Q+1) → ℂ) : Orbital Q →ₗ[ℂ] Orbital Q where
  toFun v i := d i*v i
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [mul_left_comm]

noncomputable def exteriorScaling (Q : ℕ) (d : Fin (Q+1) → ℂ) : Space Q →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (orbitalScaling Q d)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_PairConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def pairEnd (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, c i j • (annihilate j * annihilate i)

noncomputable def limitPairEnd (Q p : ℕ) : Module.End ℂ (Space Q) :=
  pairEnd Q (fun i j => ((pairLimitCoefficient p i.val j.val / Real.sqrt 2 : ℝ) : ℂ))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_FourConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

noncomputable def limitFourEnd (Q p : ℕ) (j k : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  annihilate k * annihilate j * limitPairEnd Q p

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

noncomputable def occupationNormSq (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ A : Finset (Fin (Q+1)), ‖(occupationBasis Q).repr x A‖^2

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CollectionAnnihilatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def limitPairWindow (Q : ℕ) (x : Space Q) : ℝ :=
  ∑ p ∈ Finset.range 24, occupationNormSq Q (limitPairEnd Q p x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def localOccupation (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) : Finset (Fin (L+1)) :=
  Finset.univ.filter (fun i => (⟨i.val,by omega⟩ : Fin (Q+1)) ∈ A)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SymmetricTensorOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def tensorPermutation (Q : ℕ) (σ : Equiv.Perm (Fin Q)) :
    (Fin Q → Fin 2) ≃ (Fin Q → Fin 2) where
  toFun a := a ∘ σ
  invFun a := a ∘ σ.symm
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem unitary_entry_norm_le_one (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hA) i) i
  rw [Matrix.star_eq_conjTranspose] at h
  have hs : ∑ k, ‖A i k‖^2 = (1 : ℝ) := by
    have hr := congrArg Complex.re h
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.mul_conj,Complex.normSq_eq_norm_sq,← Complex.ofReal_pow] using hr
  have hj : ‖A i j‖^2 ≤ ∑ k, ‖A i k‖^2 :=
    Finset.single_le_sum (fun k hk => sq_nonneg ‖A i k‖) (Finset.mem_univ j)
  rw [hs] at hj
  nlinarith [norm_nonneg (A i j)]

 theorem sourceSU2_isClosed :
    IsClosed (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  have he : (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
      (unitary (Matrix (Fin 2) (Fin 2) ℂ) : Set _) ∩ {A | A.det=1} := rfl
  rw [he]
  exact isClosed_unitary.inter (isClosed_eq (by fun_prop) continuous_const)

 theorem sourceSU2_isCompact :
    IsCompact (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  let K : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
    {A | ∀ i j, A i j ∈ Metric.closedBall (0 : ℂ) 1}
  have hK : IsCompact K := by
    exact isCompact_pi_infinite (fun i : Fin 2 =>
      isCompact_pi_infinite (fun j : Fin 2 => isCompact_closedBall (0 : ℂ) 1))
  apply hK.of_isClosed_subset sourceSU2_isClosed
  intro A hA i j
  simp only [Metric.mem_closedBall,dist_zero_right]
  exact unitary_entry_norm_le_one A hA.1 i j

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_MatrixAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure

variable {G I : Type*} [MeasurableSpace G] [Fintype I]

noncomputable def matrixIntegral (μ : Measure G) (f : G → Matrix I I ℂ) : Matrix I I ℂ :=
  fun i j => ∫ g, f g i j ∂μ

variable [DecidableEq I]

noncomputable def conjugateOrbit [Group G] (ρ : G →* Matrix I I ℂ) (M : Matrix I I ℂ)
    (g : G) : Matrix I I ℂ := ρ g*M*ρ g⁻¹

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_VectorAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

noncomputable def orbitalDual (Q : ℕ) (v : Orbital Q) : Module.Dual ℂ (Orbital Q) :=
  ∑ i, star (v i) • LinearMap.proj i

noncomputable def vectorAnnihilate (Q : ℕ) (v : Orbital Q) : Module.End ℂ (Space Q) :=
  CliffordAlgebra.contractLeft (orbitalDual Q v)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_FourLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def occupationFourLabels (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    Fin 4 ↪o Fin (Q+1) := Set.powersetCard.ofFinEmbEquiv.symm ⟨A,hA⟩

theorem occupationFourLabels_range (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    Finset.univ.image (occupationFourLabels Q A hA) = A := by
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem ⟨A,hA⟩ i

theorem occupationFourLabels_sum (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    (∑ i ∈ A, i.val) =
      (occupationFourLabels Q A hA 0).val + (occupationFourLabels Q A hA 1).val +
      (occupationFourLabels Q A hA 2).val + (occupationFourLabels Q A hA 3).val := by
  conv_lhs => rw [← occupationFourLabels_range Q A hA]
  rw [Finset.sum_image]
  · simp [Fin.sum_univ_succ,Nat.add_assoc]
  · intro i hi j hj he
    exact (occupationFourLabels Q A hA).injective he

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_ModeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def modeInclusion (L Q : ℕ) (_h : L ≤ Q) : Orbital L →ₗ[ℂ] Orbital Q where
  toFun v j := if hj : j.val ≤ L then v ⟨j.val,by omega⟩ else 0
  map_add' v w := by ext j; dsimp; split_ifs <;> simp
  map_smul' c v := by ext j; dsimp; split_ifs <;> simp

noncomputable def fockInclusion (L Q : ℕ) (h : L ≤ Q) : Space L →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (modeInclusion L Q h)

def includedOccupations (L Q : ℕ) (h : L ≤ Q) (A : Finset (Fin (L+1))) :
    Finset (Fin (Q+1)) := A.map (Fin.castLEEmb (Nat.add_le_add_right h 1))

end Laughlin.Fock

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

def genericCoupledWeight (A B z : ℕ) : ℕ := A+B-2*z

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_GramSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def sliceOrbital (Q z : ℕ) (hz : z ≤ Q) (p : Fin (z+1)) : Fin (Q+1) :=
  ⟨z-p.val,by omega⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RadicalCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def sourceCopyWeight (D r : ℕ) : ℝ :=
  1 / ((r.factorial : ℝ)*((D-r).factorial : ℝ))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_PolynomialMatrixODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open Polynomial
open scoped BigOperators Matrix

noncomputable def polynomialMatrixDerivative {ι κ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) : Matrix ι κ (Polynomial ℂ) := fun i j => (P i j).derivative
noncomputable def polynomialMatrixCoeff {ι κ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) (n : ℕ) : Matrix ι κ ℂ := fun i j => (P i j).coeff n

theorem polynomialMatrixDerivative_coeff {ι κ : Type*} (P : Matrix ι κ (Polynomial ℂ)) (n : ℕ) :
    polynomialMatrixCoeff (polynomialMatrixDerivative P) n =
      (n+1 : ℂ) • polynomialMatrixCoeff P (n+1) := by
  ext i j
  simp [polynomialMatrixCoeff,polynomialMatrixDerivative,coeff_derivative,mul_comm]

theorem polynomialMatrixCoeff_mul_constant {ι κ τ : Type*} [Fintype κ]
    (P : Matrix ι κ (Polynomial ℂ)) (G : Matrix κ τ ℂ) (n : ℕ) :
    polynomialMatrixCoeff (P * G.map C) n = polynomialMatrixCoeff P n * G := by
  ext i j
  simp [polynomialMatrixCoeff,Matrix.mul_apply,coeff_mul_C]

theorem polynomialMatrixCoeff_constant_mul {ι κ τ : Type*} [Fintype κ]
    (G : Matrix ι κ ℂ) (P : Matrix κ τ (Polynomial ℂ)) (n : ℕ) :
    polynomialMatrixCoeff (G.map C * P) n = G * polynomialMatrixCoeff P n := by
  ext i j
  simp [polynomialMatrixCoeff,Matrix.mul_apply,coeff_C_mul]

theorem polynomialMatrixDerivative_mul {ι κ τ : Type*} [Fintype κ]
    (P : Matrix ι κ (Polynomial ℂ)) (Q : Matrix κ τ (Polynomial ℂ)) :
    polynomialMatrixDerivative (P*Q) = polynomialMatrixDerivative P*Q+P*polynomialMatrixDerivative Q := by
  ext i j
  simp [polynomialMatrixDerivative,Matrix.mul_apply,derivative_mul,Finset.sum_add_distrib]

theorem polynomialMatrixDerivative_constant {ι κ : Type*} (G : Matrix ι κ ℂ) :
    polynomialMatrixDerivative (G.map C)=0 := by
  ext i j
  simp [polynomialMatrixDerivative]

theorem polynomialMatrixDerivative_sub {ι κ : Type*}
    (P Q : Matrix ι κ (Polynomial ℂ)) :
    polynomialMatrixDerivative (P-Q)=polynomialMatrixDerivative P-polynomialMatrixDerivative Q := by
  ext i j
  simp [polynomialMatrixDerivative]

theorem polynomialMatrixCoeff_sub {ι κ : Type*}
    (P Q : Matrix ι κ (Polynomial ℂ)) (n : ℕ) :
    polynomialMatrixCoeff (P-Q) n=polynomialMatrixCoeff P n-polynomialMatrixCoeff Q n := by
  ext i j
  simp [polynomialMatrixCoeff]

theorem polynomialMatrix_zero_of_derivative_right {ι κ : Type*} [Fintype κ]
    (P : Matrix ι κ (Polynomial ℂ)) (G : Matrix κ κ ℂ)
    (hd : polynomialMatrixDerivative P=P*G.map C)
    (h0 : polynomialMatrixCoeff P 0=0) : P=0 := by
  have hc : ∀ n, polynomialMatrixCoeff P n=0 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      have h := congrArg (fun M => polynomialMatrixCoeff M n) hd
      rw [polynomialMatrixDerivative_coeff,polynomialMatrixCoeff_mul_constant,ih,Matrix.zero_mul] at h
      exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)
  ext i j n
  exact congrFun (congrFun (hc n) i) j

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

noncomputable def castSpinColumns {I : Type*} (m n : ℕ) (h : m=n)
    (W : Matrix I (Fin (m+1)) ℂ) : Matrix I (Fin (n+1)) ℂ :=
  fun i j => W i (Fin.cast (congrArg (fun k => k+1) h.symm) j)

def fourSpinWeight (Q D : ℕ) : ℕ := 4*Q-2-2*D

theorem four_nested_weight (Q D r : ℕ) (hQ : D+2 ≤ Q) (hr : r ≤ D) :
    genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r) = fourSpinWeight Q D := by
  unfold genericCoupledWeight fourSpinWeight
  omega

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_WeightedReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def weightedFourEnd (Q p : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ) :
    Module.End ℂ (Space Q) :=
  ∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ) • limitFourEnd Q p j k

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators
open MeasureTheory

variable {G I J K L : Type*} [MeasurableSpace G]
  [Fintype I] [Fintype J] [Fintype K] [Fintype L]

noncomputable def entrywiseIntegral (μ : Measure G) (f : G → Matrix I J ℂ) : Matrix I J ℂ :=
  fun i j => ∫ g, f g i j ∂μ

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TwoBodyCertificateHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

noncomputable def physicalPairRowMatrix (Q : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ :=
  fun i j => if i.val=row.1 ∧ j.val=row.1 then ((row.2.1 : ℂ)/10^7)^2 else 0

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_RankTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def realOuter {I : Type*} (u v : I → ℝ) : Matrix I I ℝ :=
  fun i j => u i * v j

end Laughlin.Spin

end OAI
end


