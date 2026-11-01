-- Prove2me | Definitions.Def_OAIQ050L017
-- name    : OAIQ050L017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:11:05.978987+00:00
-- url     : https://prove2.me/theorems/62141ae8-4c82-40d1-b809-f76d4d90baca
-- title:
--   Definitions bundle OAIQ050L017 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 11 definitions, 2 instances and 17 theorems. The definitions and types are `OAI.Laughlin.Fock.sourceThreeEnd`, `OAI.Laughlin.Fock.sourceThreeHighestEnd`, `OAI.Laughlin.Fock.sourceThreeVector`, `OAI.Laughlin.Fock.threeWedge`, `OAI.Laughlin.Fock.truncatedDiagonals`, `OAI.Laughlin.Fock.truncatedScaling`, `OAI.Laughlin.Fock.truncatedScalingInv`, `OAI.Laughlin.Planar.sphereHamiltonian`, `OAI.Laughlin.Rotation.spinRaiseComplex`, `OAI.Laughlin.Rotation.totalRaiseComplex`, `OAI.Laughlin.Spin.PairCoupledIndex`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_Asymptotics_TruncatedScaling`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/TruncatedScaling.lean), [`Laughlin_Asymptotics_UpperSpinCurve`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/UpperSpinCurve.lean), [`Laughlin_Asymptotics_UpperSpinDynamics`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Asymptotics/UpperSpinDynamics.lean), [`Laughlin_Pair_CoupledBasis`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/CoupledBasis.lean), [`Laughlin_Planar_Model`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Planar/Model.lean), [`Laughlin_Spin_GeneralSpinAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/GeneralSpinAction.lean), [`Laughlin_Spin_Haar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/Haar.lean), [`Laughlin_Spin_LadderGroupIntertwining`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/LadderGroupIntertwining.lean), [`Laughlin_Tensor_PolynomialRealization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Tensor/PolynomialRealization.lean), [`Laughlin_ThreeBody_FockHaar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/FockHaar.lean), [`Laughlin_ThreeBody_HighestFock`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/HighestFock.lean), [`Laughlin_ThreeBody_PhysicalKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/PhysicalKernel.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinPlanar`; the bundles `OAIQ050L010`, `OAIQ050L011`, `OAIQ050L012` and `OAIQ050L013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L020` and `OAIQ050L021`; the statements `OAI_Laughlin_Fock_physical_threeBody_Fock_null`, `OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_bound`, `OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_nonneg`, `OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50`, `OAI_Laughlin_Fock_sourceFockHamiltonian_normal_square`, `OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50`, `OAI_Laughlin_Fock_sourceThreeHighestEnd_haar`, `OAI.Laughlin.Fock.sourceThreeHighestEnd_haar_s50`, `OAI_Laughlin_Fock_sourceThreeVector_adjoint`, `OAI.Laughlin.Fock.sourceThreeVector_adjoint_s50`, `OAI_Laughlin_Fock_threeWedge_zero_of_gram_zero`, `OAI.Laughlin.Fock.threeWedge_zero_of_gram_zero_s50`, `OAI_Laughlin_Fock_truncatedQuadratic_error`, `OAI.Laughlin.Fock.truncatedQuadratic_error_s50`, `OAI_Laughlin_Fock_truncatedScalingInv_coordinate`, `OAI.Laughlin.Fock.truncatedScalingInv_coordinate_s50`, `OAI_Laughlin_Fock_truncatedScaling_normSq_le`, `OAI.Laughlin.Fock.truncatedScaling_normSq_le_s50`, `OAI_Laughlin_Fock_truncated_pair_window_return`, `OAI.Laughlin.Fock.truncated_pair_window_return_s50`, `OAI_Laughlin_Fock_truncated_sourceFour_conjugation`, `OAI.Laughlin.Fock.truncated_sourceFour_conjugation_s50` and `OAI_Laughlin_Spin_fourBodyTermMatrix_trace`; the proofs of `OAI_Laughlin_Fock_contractionForm_haar`, `OAI.Laughlin.Fock.contractionForm_haar_s50`, `OAI_Laughlin_Fock_linearMap_rotation_norm_integrable`, `OAI.Laughlin.Fock.linearMap_rotation_norm_integrable_s50`, `OAI_Laughlin_Fock_occupationQuadratic_rotation_integrable`, `OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50`, `OAI_Laughlin_Fock_physical_fourBody_haar_transfer`, `OAI.Laughlin.Fock.physical_fourBody_haar_transfer_s50`, `OAI_Laughlin_Fock_physical_fourCopyOperator_haar`, `OAI.Laughlin.Fock.physical_fourCopyOperator_haar_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_null`, `OAI.Laughlin.Fock.physical_threeBody_Fock_null_s50`, `OAI_Laughlin_Fock_physical_threeBody_budget_eventually`, `OAI_Laughlin_Fock_physical_threeBody_projector_bound`, `OAI.Laughlin.Fock.physical_threeBody_projector_bound_s50`, `OAI_Laughlin_Fock_physical_threeBody_projector_nonneg`, `OAI.Laughlin.Fock.physical_threeBody_projector_nonneg_s50`, `OAI_Laughlin_Fock_sourceFockHamiltonian_normal_square`, `OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50`, `OAI_Laughlin_Fock_sourceThreeVector_adjoint`, `OAI.Laughlin.Fock.sourceThreeVector_adjoint_s50`, `OAI_Laughlin_Fock_threeWedge_zero_of_gram_zero`, `OAI.Laughlin.Fock.threeWedge_zero_of_gram_zero_s50`, `OAI_Laughlin_Fock_truncatedQuadratic_error`, `OAI.Laughlin.Fock.truncatedQuadratic_error_s50`, `OAI_Laughlin_Fock_truncatedScalingInv_coordinate`, `OAI.Laughlin.Fock.truncatedScalingInv_coordinate_s50`, `OAI_Laughlin_Fock_truncatedScaling_normSq_le`, `OAI.Laughlin.Fock.truncatedScaling_normSq_le_s50`, `OAI_Laughlin_Fock_truncated_pair_window_return`, `OAI.Laughlin.Fock.truncated_pair_window_return_s50`, `OAI_Laughlin_Fock_truncated_sourceFour_conjugation`, `OAI.Laughlin.Fock.truncated_sourceFour_conjugation_s50`, `OAI_Laughlin_Planar_finite_degree_endpoint_of_fock_square`, `OAI.Laughlin.Planar.finite_degree_endpoint_of_fock_square_s50`, `OAI_Laughlin_Rotation_embedded_spin_haar`, `OAI.Laughlin.Rotation.embedded_spin_haar_s50`, `OAI_Laughlin_Rotation_source_spin_haar_schur`, `OAI.Laughlin.Rotation.source_spin_haar_schur_s50`, `OAI_Laughlin_Rotation_source_unequal_spin_haar_zero`, `OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50`, `OAI_Laughlin_Spin_coupledBasis_eigen` and `OAI_Laughlin_Spin_fourBodyTermMatrix_trace`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L010
import Definitions.Def_OAIQ050L011
import Definitions.Def_OAIQ050L012
import Definitions.Def_OAIQ050L013

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def truncatedScaling (L Q : ℕ) : Space Q →ₐ[ℂ] Space Q :=
  exteriorScaling Q (fun i => (truncatedModeFactor L Q i : ℂ))

noncomputable def truncatedScalingInv (L Q : ℕ) : Space Q →ₐ[ℂ] Space Q :=
  exteriorScaling Q (fun i => (truncatedModeFactor L Q i : ℂ)⁻¹)

noncomputable def truncatedDiagonals (L Q : ℕ) (A : Finset (Fin (Q+1))) : ℝ :=
  ∏ i ∈ A, truncatedModeFactor L Q i

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open MeasureTheory MeasureTheory.Measure TopologicalSpace

instance sourceHaar_isHaar : IsHaarMeasure sourceHaar :=
  inferInstanceAs (IsHaarMeasure (haarMeasure (⊤ : PositiveCompacts SourceSU2)))

instance sourceHaar_isProbability : IsProbabilityMeasure sourceHaar where
  measure_univ := by
    simpa [sourceHaar] using (haarMeasure_self (K₀ := (⊤ : PositiveCompacts SourceSU2)))

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Tensor_PolynomialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem symmetricTensor_column_sum (Q : ℕ) (p : Fin (Q+1)) :
    (∑ a, symmetricTensorInclusion Q a p) = (Real.sqrt (Q.choose p.val : ℝ) : ℂ) := by
  have hr : (∑ a : Fin Q → Fin 2, symmetricTensorInclusionReal Q a p) =
      Real.sqrt (Q.choose p.val : ℝ) := by
    have hn : Real.sqrt (Q.choose p.val : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ p.isLt))
    have he (a : Fin Q → Fin 2) : symmetricTensorInclusionReal Q a p =
        (Real.sqrt (Q.choose p.val : ℝ))⁻¹ *
          (if tensorWeight Q a=p.val then 1 else 0) := by
      simp [symmetricTensorInclusionReal, mul_ite]
    simp_rw [he, ← Finset.mul_sum, tensorWeight_count]
    apply (mul_left_cancel₀ hn)
    rw [mul_inv_cancel_left₀ hn]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose p.val by positivity)]
  simpa [symmetricTensorInclusion] using congrArg Complex.ofReal hr

theorem symmetricTensor_weighted_column {R : Type*} [CommRing R]
    (f : ℂ →+* R) (Q : ℕ) (p : Fin (Q+1)) (m : ℕ → R) :
    (∑ a, f (symmetricTensorInclusion Q a p) * m (tensorWeight Q a)) =
      f (Real.sqrt (Q.choose p.val : ℝ) : ℂ) * m p.val := by
  have he (a : Fin Q → Fin 2) : f (symmetricTensorInclusion Q a p) * m (tensorWeight Q a) =
      f (symmetricTensorInclusion Q a p) * m p.val := by
    by_cases h : tensorWeight Q a=p.val
    · rw [h]
    · simp [symmetricTensorInclusion, symmetricTensorInclusionReal,h]
  simp_rw [he, ← Finset.sum_mul, ← map_sum, symmetricTensor_column_sum]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_GeneralSpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem general_tensor_spin_intertwining (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    symmetricTensorInclusion Q*generalSpinMatrix Q A = tensorMatrix Q A*symmetricTensorInclusion Q := by
  ext a p
  let v : (Fin Q → Fin 2) → ℂ := fun b => symmetricTensorInclusion Q b p
  have hv : ∀ b c, tensorWeight Q b=tensorWeight Q c → v b=v c := by
    intro b c h
    simp only [v,symmetricTensorInclusion,Matrix.map_apply,symmetricTensorInclusionReal,h]
  have hf := tensorMatrix_preserves_symmetric Q A v hv
  have he := congrFun (symmetricTensor_projector_fixed Q (tensorMatrix Q A *ᵥ v) hf) a
  change (symmetricTensorInclusion Q*((symmetricTensorInclusion Q)ᴴ*tensorMatrix Q A*symmetricTensorInclusion Q)) a p = _
  calc
    _ = ((symmetricTensorInclusion Q*(symmetricTensorInclusion Q)ᴴ)*
      (tensorMatrix Q A*symmetricTensorInclusion Q)) a p := by simp only [Matrix.mul_assoc]
    _ = _ := he

theorem generalSpinMatrix_mul (Q : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    generalSpinMatrix Q (A*B) = generalSpinMatrix Q A*generalSpinMatrix Q B := by
  unfold generalSpinMatrix
  rw [tensorMatrix_mul]
  have he := general_tensor_spin_intertwining Q B
  unfold generalSpinMatrix at he
  calc
    _ = (symmetricTensorInclusion Q)ᴴ*tensorMatrix Q A*
      (tensorMatrix Q B*symmetricTensorInclusion Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← he]; simp only [Matrix.mul_assoc]

theorem generalSpinMatrix_one (Q : ℕ) : generalSpinMatrix Q 1=1 := by
  simp [generalSpinMatrix,tensorMatrix_one,symmetricTensorInclusion_isometry]

theorem generalSpinMatrix_diagonal (Q : ℕ) (x y : ℂ) :
    generalSpinMatrix Q (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) =
      Matrix.diagonal (fun p : Fin (Q+1) => y^p.val*x^(Q-p.val)) := by
  unfold generalSpinMatrix
  rw [tensorMatrix_diagonal,Matrix.mul_assoc,
    symmetricTensor_diagonal_intertwining Q (fun k => y^k*x^(Q-k)),
    ← Matrix.mul_assoc,symmetricTensorInclusion_isometry,Matrix.one_mul]

theorem generalSpinMatrix_polynomial {R : Type*} [CommRing R]
    (f : ℂ →+* R) (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (u v : R) (p : Fin (Q+1)) :
    (∑ q : Fin (Q+1), f (generalSpinMatrix Q A q p) *
      (f (Real.sqrt (Q.choose q.val : ℝ) : ℂ) * v^q.val*u^(Q-q.val))) =
      f (Real.sqrt (Q.choose p.val : ℝ) : ℂ) *
        (f (A 0 1)*u+f (A 1 1)*v)^p.val *
        (f (A 0 0)*u+f (A 1 0)*v)^(Q-p.val) := by
  have h := general_tensor_spin_intertwining Q A
  have hm := congrArg (fun M : Matrix (Fin Q → Fin 2) (Fin (Q+1)) ℂ =>
    ∑ a, f (M a p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) h
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul] at hm
  rw [Finset.sum_comm] at hm
  have hl (q : Fin (Q+1)) : (∑ a, f (symmetricTensorInclusion Q a q) *
      f (generalSpinMatrix Q A q p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      f (generalSpinMatrix Q A q p) *
        (f (Real.sqrt (Q.choose q.val : ℝ) : ℂ)*v^q.val*u^(Q-q.val)) := by
    simp_rw [mul_right_comm _ (f (generalSpinMatrix Q A q p)), ← Finset.sum_mul]
    rw [symmetricTensor_weighted_column f Q q (fun n => v^n*u^(Q-n))]
    ring
  simp_rw [hl] at hm
  rw [Finset.sum_comm] at hm
  have hr (b : Fin Q → Fin 2) : (∑ a, f (tensorMatrix Q A a b) *
      f (symmetricTensorInclusion Q b p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      f (symmetricTensorInclusion Q b p) *
        ((f (A 0 1)*u+f (A 1 1)*v)^(tensorWeight Q b) *
        (f (A 0 0)*u+f (A 1 0)*v)^(Q-tensorWeight Q b)) := by
    simp_rw [mul_right_comm _ (f (symmetricTensorInclusion Q b p)), ← Finset.sum_mul]
    rw [tensorMatrix_polynomial]
    ring
  simp_rw [hr] at hm
  rw [symmetricTensor_weighted_column f Q p (fun n =>
    (f (A 0 1)*u+f (A 1 1)*v)^n*(f (A 0 0)*u+f (A 1 0)*v)^(Q-n))] at hm
  simpa only [mul_assoc] using hm

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_UpperSpinCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open Polynomial
open scoped BigOperators Matrix

theorem upperSpinCurve_eval (Q : ℕ) (c : ℂ) (p q : Fin (Q+1)) :
    (upperSpinCurve Q p q).eval c =
      generalSpinMatrix Q (Matrix.transvection (0 : Fin 2) 1 c) p q := by
  let M := generalSpinMatrix Q (Matrix.transvection (0 : Fin 2) 1 c)
  have h := generalSpinMatrix_polynomial Polynomial.C Q
    (Matrix.transvection (0 : Fin 2) 1 c) (1 : Polynomial ℂ) X q
  have he : (∑ r : Fin (Q+1), C (M r q) * (C (spinBinomialWeight Q r) * X^r.val)) =
      C (spinBinomialWeight Q q) * (X+C c)^q.val := by
    simpa [M,spinBinomialWeight,Matrix.transvection,Matrix.single,Matrix.one_apply,add_comm] using h
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff p.val) he
  simp only [finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero,
    coeff_X_add_C_pow] at hc
  simp only [← Fin.ext_iff,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at hc
  apply (mul_right_cancel₀ (spinBinomialWeight_ne_zero Q p))
  change (upperSpinCurve Q p q).eval c * spinBinomialWeight Q p = M p q * spinBinomialWeight Q p
  rw [hc]
  simp only [upperSpinCurve,eval_monomial]
  field_simp [spinBinomialWeight_ne_zero Q p]

theorem upperSpinCurve_zero (Q : ℕ) (p q : Fin (Q+1)) :
    (upperSpinCurve Q p q).coeff 0 = if p=q then 1 else 0 := by
  rw [coeff_zero_eq_eval_zero,upperSpinCurve_eval,Matrix.transvection_zero,generalSpinMatrix_one,
    Matrix.one_apply]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_UpperSpinDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open Polynomial
open scoped BigOperators Matrix Kronecker

noncomputable def spinRaiseComplex (Q : ℕ) := (Spin.raiseMatrix Q).map Complex.ofReal
noncomputable def totalRaiseComplex (A B : ℕ) := (Spin.totalRaise A B).map Complex.ofReal

theorem upperSpinCurve_derivative (Q : ℕ) :
    polynomialMatrixDerivative (upperSpinCurve Q) = upperSpinCurve Q * (spinRaiseComplex Q).map C := by
  funext p q
  induction q using Fin.cases with
  | zero =>
    change (upperSpinCurve Q p 0).derivative = _
    rw [upperSpinCurve_derivative_zero]
    simp [Matrix.mul_apply,spinRaiseComplex,Spin.raiseMatrix]
  | succ q =>
    change (upperSpinCurve Q p q.succ).derivative = _
    rw [upperSpinCurve_derivative_succ,Matrix.mul_apply]
    have he (r : Fin (Q+1)) : r.val+1=q.succ.val ↔ r=q.castSucc := by
      simp [Fin.ext_iff]
    simp only [spinRaiseComplex,Matrix.map_apply,Spin.raiseMatrix,he,apply_ite,
      Complex.ofReal_zero,map_zero,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Fin.val_castSucc]

theorem upperSpinCurve_initial (Q : ℕ) : polynomialMatrixCoeff (upperSpinCurve Q) 0=1 := by
  ext p q
  exact upperSpinCurve_zero Q p q

theorem totalRaiseComplex_polynomial (A B : ℕ) :
    (totalRaiseComplex A B).map C =
      (spinRaiseComplex A).map C ⊗ₖ (1 : Matrix (Fin (B+1)) (Fin (B+1)) (Polynomial ℂ)) +
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) (Polynomial ℂ)) ⊗ₖ (spinRaiseComplex B).map C := by
  ext ⟨i,j⟩ ⟨k,l⟩ : 2
  by_cases hik : i=k <;> by_cases hjl : j=l <;>
    simp [totalRaiseComplex,spinRaiseComplex,Spin.totalRaise,Matrix.kroneckerMap,
      Matrix.one_apply,hik,hjl]

theorem upperSpinTensor_derivative (A B : ℕ) :
    polynomialMatrixDerivative (upperSpinCurve A ⊗ₖ upperSpinCurve B) =
      (upperSpinCurve A ⊗ₖ upperSpinCurve B)*(totalRaiseComplex A B).map C := by
  rw [polynomialMatrixDerivative_kronecker,upperSpinCurve_derivative,upperSpinCurve_derivative,
    totalRaiseComplex_polynomial,Matrix.mul_add]
  simp only [← Matrix.mul_kronecker_mul,Matrix.mul_one]

theorem upperSpinTensor_initial (A B : ℕ) :
    polynomialMatrixCoeff (upperSpinCurve A ⊗ₖ upperSpinCurve B) 0=1 := by
  rw [polynomialMatrixCoeff_kronecker_zero,upperSpinCurve_initial,upperSpinCurve_initial,
    Matrix.one_kronecker_one]

theorem raising_intertwiner_upper (A B J : ℕ)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hW : totalRaiseComplex A B*W=W*spinRaiseComplex J) (c : ℂ) :
    (generalSpinMatrix A (Matrix.transvection (0 : Fin 2) 1 c) ⊗ₖ
      generalSpinMatrix B (Matrix.transvection (0 : Fin 2) 1 c))*W =
        W*generalSpinMatrix J (Matrix.transvection (0 : Fin 2) 1 c) := by
  have h := polynomialMatrix_intertwining (upperSpinCurve A ⊗ₖ upperSpinCurve B)
    (upperSpinCurve J) (totalRaiseComplex A B) (spinRaiseComplex J) W
    (upperSpinTensor_derivative A B) (upperSpinCurve_derivative J)
    (upperSpinTensor_initial A B) (upperSpinCurve_initial J) hW
  ext i j
  have he := congrArg (fun M => (M i j).eval c) h
  simpa [Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap,eval_finsetSum,eval_mul,upperSpinCurve_eval] using he

theorem lowering_intertwiner_lower (A B J : ℕ)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hW : (totalRaiseComplex A B)ᵀ*W=W*(spinRaiseComplex J)ᵀ) (c : ℂ) :
    (generalSpinMatrix A (Matrix.transvection (1 : Fin 2) 0 c) ⊗ₖ
      generalSpinMatrix B (Matrix.transvection (1 : Fin 2) 0 c))*W =
        W*generalSpinMatrix J (Matrix.transvection (1 : Fin 2) 0 c) := by
  have ht : spinRaiseComplex J*Wᵀ=Wᵀ*totalRaiseComplex A B := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using congrArg Matrix.transpose hW.symm
  have h := polynomialMatrix_intertwining (upperSpinCurve J)
    (upperSpinCurve A ⊗ₖ upperSpinCurve B) (spinRaiseComplex J) (totalRaiseComplex A B) Wᵀ
    (upperSpinCurve_derivative J) (upperSpinTensor_derivative A B)
    (upperSpinCurve_initial J) (upperSpinTensor_initial A B) ht
  have he : W*(generalSpinMatrix J (Matrix.transvection (0 : Fin 2) 1 c))ᵀ =
      (generalSpinMatrix A (Matrix.transvection (0 : Fin 2) 1 c) ⊗ₖ
      generalSpinMatrix B (Matrix.transvection (0 : Fin 2) 1 c))ᵀ*W := by
    have hh := congrArg Matrix.transpose h
    ext i j
    have hh' := congrArg (fun M => (M i j).eval c) hh
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.kronecker,Matrix.kroneckerMap,
      eval_finsetSum,eval_mul,upperSpinCurve_eval,mul_comm] using hh'
  have hf : (Matrix.transvection (0 : Fin 2) 1 c)ᵀ=Matrix.transvection 1 0 c := by
    ext i j
    simp [Matrix.transvection,Matrix.transpose_apply,Matrix.single,Matrix.one_apply,eq_comm,and_comm]
  change W*(generalSpinMatrix J (Matrix.transvection (0 : Fin 2) 1 c))ᵀ =
    ((generalSpinMatrix A (Matrix.transvection (0 : Fin 2) 1 c))ᵀ ⊗ₖ
     (generalSpinMatrix B (Matrix.transvection (0 : Fin 2) 1 c))ᵀ)*W at he
  rw [← generalSpinMatrix_transpose,← generalSpinMatrix_transpose,
    ← generalSpinMatrix_transpose,hf] at he
  exact he.symm

end Laughlin.Rotation

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

abbrev PairCoupledIndex (Q : ℕ) :=
  Σ r : OddPairLabel Q, Fin (genericCoupledWeight Q Q (oddPairDeficit r)+1)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

noncomputable def sphereHamiltonian (L Q : ℕ) : Matrix (Occupations L) (Occupations L) ℂ :=
  ∑ p ∈ Finset.range (2*L+1), (spherePairMatrix L Q p)ᴴ * spherePairMatrix L Q p

end Laughlin.Planar

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

theorem weight_support_diagonal_intertwining (A B z J : ℕ) (hz : 2*z+J=A+B)
    (W : Matrix (Fin (A+1) × Fin (B+1)) (Fin (J+1)) ℂ)
    (hs : ∀ i n, i.1.val+i.2.val ≠ z+n.val → W i n=0)
    (x y : ℂ) (hxy : x*y=1) :
    (generalSpinMatrix A (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) ⊗ₖ
      generalSpinMatrix B (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)))*W =
        W*generalSpinMatrix J (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) := by
  rw [generalSpinMatrix_diagonal,generalSpinMatrix_diagonal,generalSpinMatrix_diagonal,
    Matrix.diagonal_kronecker_diagonal]
  ext i n
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases hi : i.1.val+i.2.val=z+n.val
  · have he : A-i.1.val+(B-i.2.val)=z+(J-n.val) := by
      have h1 := i.1.isLt
      have h2 := i.2.isLt
      have hn := n.isLt
      omega
    have hf : (y^i.1.val*x^(A-i.1.val))*(y^i.2.val*x^(B-i.2.val)) = y^n.val*x^(J-n.val) := by
      calc
        _ = y^(i.1.val+i.2.val)*x^(A-i.1.val+(B-i.2.val)) := by simp only [pow_add]; ring
        _ = (x*y)^z*(y^n.val*x^(J-n.val)) := by rw [hi,he]; simp only [pow_add,mul_pow]; ring
        _ = _ := by rw [hxy,one_pow,one_mul]
    rw [hf]
    ring
  · rw [hs i n hi]
    simp

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix Kronecker

noncomputable def sourceThreeEnd (Q : ℕ) (i : PairOrbitalIndex Q) : Module.End ℂ (Space Q) :=
  annihilate i.2 * sourcePairEnd Q i.1.val

noncomputable def sourceThreeVector (Q : ℕ) (i : PairOrbitalIndex Q) : Space Q :=
  sourcePairVector Q i.1.val * create i.2 (1 : Space Q)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HighestFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

noncomputable def sourceThreeHighestEnd (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    Module.End ℂ (Space Q) :=
  ∑ p : Fin (z+1), (highestUnit (2*Q-2) Q z p.val : ℂ) •
    sourceThreeEnd Q (weightSliceIndex (2*Q-2) Q z (by omega) hz p)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

noncomputable def threeWedge (Q : ℕ) (u : Spin.PairOrbitalIndex Q → ℂ) : Space Q :=
  ∑ a, u a • threeBodyColumn Q a.1.val a.2

end Laughlin.Fock

end OAI
end


