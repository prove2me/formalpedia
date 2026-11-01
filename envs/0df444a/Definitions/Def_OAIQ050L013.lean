-- Prove2me | Definitions.Def_OAIQ050L013
-- name    : OAIQ050L013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:09:46.869574+00:00
-- url     : https://prove2.me/theorems/b9440b5a-5cb1-4392-9a4d-0e29b49441f7
-- title:
--   Definitions bundle OAIQ050L013 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 7 definitions and 10 theorems. The definitions and types are `OAI.Laughlin.Fock.threeBodyGramSlice`, `OAI.Laughlin.Fock.wedgeDelta`, `OAI.Laughlin.Rotation.generalSpinMatrix`, `OAI.Laughlin.Rotation.physicalPairInclusion`, `OAI.Laughlin.Rotation.sourceMixer`, `OAI.Laughlin.Rotation.sourceTorus`, `OAI.Laughlin.Spin.GenericCoupledIndex`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_Asymptotics_UpperSpinCurve`, `Laughlin_Asymptotics_UpperSpinDynamics`, `Laughlin_FourBody_LimitCARReadout`, `Laughlin_Operators_PhysicalPairRotation`, `Laughlin_Polynomial_PolynomialMatrixODE`, `Laughlin_Spin_Basis2`, `Laughlin_Spin_BinomialWeights`, `Laughlin_Spin_GeneralSpinAction`, `Laughlin_Spin_Mixing`, `Laughlin_Spin_Torus`, `Laughlin_Tensor_PolynomialRealization`, `Laughlin_Tensor_WeightProducts`, `Laughlin_ThreeBody_GramSlice`.
--
--   **Imports.** It imports the bundles `OAIQ050L005`, `OAIQ050L006`, `OAIQ050L007` and `OAIQ050L008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L017`, `OAIQ050L018` and `OAIQ050L019`; the statements `OAI_Laughlin_Fock_threeBodyGramSlice_first_row_pos`, `OAI.Laughlin.Fock.threeBodyGramSlice_first_row_pos_s50`, `OAI_Laughlin_Fock_threeBodyGram_highest_first_coordinate`, `OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50`, `OAI_Laughlin_Rotation_physicalPairInclusion_SU2` and `OAI.Laughlin.Rotation.physicalPairInclusion_SU2_s50`; the proofs of `OAI_Laughlin_Fock_fourPairTargetMatrix_Fock`, `OAI_Laughlin_Fock_retainedFourAllowance_bessel_bound`, `OAI_Laughlin_Fock_sourcePairEnd_rotation`, `OAI.Laughlin.Fock.sourcePairEnd_rotation_s50`, `OAI_Laughlin_Fock_threeBodyGramSlice_first_row_pos`, `OAI.Laughlin.Fock.threeBodyGramSlice_first_row_pos_s50`, `OAI_Laughlin_Fock_threeBodyGram_highest_first_coordinate`, `OAI.Laughlin.Fock.threeBodyGram_highest_first_coordinate_s50`, `OAI_Laughlin_Fock_weightedFourEnd_readout`, `OAI.Laughlin.Fock.weightedFourEnd_readout_s50`, `OAI_Laughlin_Rotation_source_spin_commutant_scalar` and `OAI.Laughlin.Rotation.source_spin_commutant_scalar_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L005
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007
import Definitions.Def_OAIQ050L008

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Tensor_WeightProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators

 theorem tensorWeight_product {R : Type*} [CommMonoid R] (Q : ℕ) (a : Fin Q → Fin 2) (x y : R) :
    (∏ i, if a i=1 then y else x) = y^(tensorWeight Q a)*x^(Q-tensorWeight Q a) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hc : (Finset.univ.filter (fun i => ¬ a i=1)).card=Q-tensorWeight Q a := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin Q => a i=1)
    simp only [Finset.card_univ,Fintype.card_fin] at h
    change (Finset.univ.filter (fun i => ¬ a i=1)).card=Q-(tensorBits Q a).card
    unfold tensorBits
    omega
  rw [hc]
  rfl

 theorem tensorMatrix_diagonal (Q : ℕ) (x y : ℂ) :
    tensorMatrix Q (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) =
      Matrix.diagonal (fun a => y^(tensorWeight Q a)*x^(Q-tensorWeight Q a)) := by
  classical
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [tensorMatrix,Matrix.diagonal_apply_eq]
    have he (i : Fin Q) : (if a i=0 then x else y)=(if a i=1 then y else x) := by
      have h : a i=0 ∨ a i=1 := by omega
      rcases h with h | h <;> simp [h]
    simp_rw [he]
    exact tensorWeight_product Q a x y
  · rw [Matrix.diagonal_apply_ne _ hab]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Torus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def sourceTorus (z : ℂ) (hz : ‖z‖=1) : SourceSU2 := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i=0 then z else star z)
  have hzz : z*(starRingEnd ℂ) z=1 := by simpa [hz] using Complex.mul_conj' z
  have hzz' : (starRingEnd ℂ) z*z=1 := by rw [mul_comm]; exact hzz
  refine ⟨A,?_⟩
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A,Matrix.mul_apply,Matrix.star_eq_conjTranspose,hzz,hzz']
  · simp [A,Matrix.det_diagonal,Fin.prod_univ_two,hzz]

 theorem symmetricTensor_diagonal_intertwining (Q : ℕ) (f : ℕ → ℂ) :
    Matrix.diagonal (fun a => f (tensorWeight Q a))*symmetricTensorInclusion Q =
      symmetricTensorInclusion Q*Matrix.diagonal (fun p : Fin (Q+1) => f p.val) := by
  ext a p
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,symmetricTensorInclusion,Matrix.map_apply,
    symmetricTensorInclusionReal]
  by_cases h : tensorWeight Q a=p.val
  · simp [h,mul_comm]
  · simp [h]

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

theorem tensorMatrix_polynomial {R : Type*} [CommRing R]
    (f : ℂ →+* R) (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : R) (b : Fin Q → Fin 2) :
    (∑ a, f (tensorMatrix Q A a b) *
      (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      (f (A 0 1)*u+f (A 1 1)*v)^(tensorWeight Q b) *
      (f (A 0 0)*u+f (A 1 0)*v)^(Q-tensorWeight Q b) := by
  have he (a : Fin Q → Fin 2) : f (tensorMatrix Q A a b) *
      (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a)) =
      ∏ k, f (A (a k) (b k)) * (if a k=1 then v else u) := by
    rw [Finset.prod_mul_distrib, tensorWeight_product]
    simp [tensorMatrix]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun k x => f (A x (b k)) * (if x=1 then v else u))]
  have he' (k : Fin Q) : (∑ x : Fin 2, f (A x (b k)) * (if x=1 then v else u)) =
      if b k=1 then f (A 0 1)*u+f (A 1 1)*v else f (A 0 0)*u+f (A 1 0)*v := by
    have h : b k=0 ∨ b k=1 := by omega
    rcases h with h | h <;> simp [h, Fin.sum_univ_two]
  simp_rw [he']
  exact tensorWeight_product Q b _ _

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

noncomputable def generalSpinMatrix (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ :=
  (symmetricTensorInclusion Q)ᴴ * tensorMatrix Q A * symmetricTensorInclusion Q

theorem generalSpinMatrix_transpose (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    generalSpinMatrix Q Aᵀ=(generalSpinMatrix Q A)ᵀ := by
  have hI : (symmetricTensorInclusion Q)ᴴ=(symmetricTensorInclusion Q)ᵀ := by
    ext a b
    simp [symmetricTensorInclusion,Matrix.conjTranspose_apply,Matrix.transpose_apply]
  have hT : tensorMatrix Q Aᵀ=(tensorMatrix Q A)ᵀ := rfl
  simp only [generalSpinMatrix,hI,hT,Matrix.transpose_mul,Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_BinomialWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators

theorem spinBinomialWeight_step (Q : ℕ) (p : Fin Q) :
    spinBinomialWeight Q p.succ * ((p.val : ℂ)+1) =
      spinBinomialWeight Q p.castSucc * (Spin.ladder Q p.val : ℂ) := by
  have hr : Real.sqrt (Q.choose (p.val+1) : ℝ)*((p.val : ℝ)+1) =
      Real.sqrt (Q.choose p.val : ℝ)*Spin.ladder Q p.val := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq Q p.val)
    push_cast at hc
    have he : (Real.sqrt (Q.choose (p.val+1) : ℝ)*((p.val : ℝ)+1))^2 =
        (Real.sqrt (Q.choose p.val : ℝ)*Spin.ladder Q p.val)^2 := by
      unfold Spin.ladder
      rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
      linear_combination ((p.val : ℝ)+1)*hc
    have h1 : 0 ≤ Real.sqrt (Q.choose (p.val+1) : ℝ)*((p.val : ℝ)+1) := by positivity
    have h2 : 0 ≤ Real.sqrt (Q.choose p.val : ℝ)*Spin.ladder Q p.val := by
      unfold Spin.ladder; positivity
    nlinarith only [he,h1,h2]
  simpa [spinBinomialWeight] using congrArg Complex.ofReal hr

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

theorem upperSpinCurve_derivative_succ (Q : ℕ) (p : Fin (Q+1)) (q : Fin Q) :
    (upperSpinCurve Q p q.succ).derivative =
      upperSpinCurve Q p q.castSucc * C (Spin.ladder Q q.val : ℂ) := by
  by_cases hp : p.val ≤ q.val
  · have he : q.val+1-p.val-1=q.val-p.val := by omega
    simp only [upperSpinCurve,Fin.val_succ,Fin.val_castSucc,derivative_monomial,
      monomial_mul_C,he]
    congr 1
    have hc := congrArg (fun n : ℕ => (n : ℂ)) (Nat.choose_mul_succ_eq q.val p.val)
    push_cast at hc
    have hw := spinBinomialWeight_step Q q
    field_simp [spinBinomialWeight_ne_zero Q p]
    linear_combination -(spinBinomialWeight Q q.succ)*hc +
      (q.val.choose p.val : ℂ)*hw
  · have hsmall : q.val < p.val := by omega
    by_cases hlarge : q.val+1 < p.val
    · simp [upperSpinCurve,Nat.choose_eq_zero_of_lt hsmall,Nat.choose_eq_zero_of_lt hlarge]
    · have he : p.val=q.val+1 := by omega
      simp [upperSpinCurve,he]

end Laughlin.Rotation

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

theorem polynomialMatrix_intertwining {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι (Polynomial ℂ)) (V : Matrix κ κ (Polynomial ℂ))
    (G : Matrix ι ι ℂ) (H : Matrix κ κ ℂ) (W : Matrix ι κ ℂ)
    (hU : polynomialMatrixDerivative U=U*G.map C)
    (hV : polynomialMatrixDerivative V=V*H.map C)
    (hU0 : polynomialMatrixCoeff U 0=1) (hV0 : polynomialMatrixCoeff V 0=1)
    (hW : G*W=W*H) : U*W.map C=W.map C*V := by
  have hWC : G.map C*W.map C=W.map C*H.map C := by
    simpa only [Matrix.map_mul] using congrArg (fun M => M.map C) hW
  have hd : polynomialMatrixDerivative (U*W.map C-W.map C*V) =
      (U*W.map C-W.map C*V)*H.map C := by
    rw [polynomialMatrixDerivative_sub,polynomialMatrixDerivative_mul,polynomialMatrixDerivative_mul,
      polynomialMatrixDerivative_constant,hU,hV,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
      Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
    rw [hWC]
  have h0 : polynomialMatrixCoeff (U*W.map C-W.map C*V) 0=0 := by
    rw [polynomialMatrixCoeff_sub,polynomialMatrixCoeff_mul_constant,
      polynomialMatrixCoeff_constant_mul,hU0,hV0,Matrix.one_mul,Matrix.mul_one,sub_self]
  exact sub_eq_zero.mp (polynomialMatrix_zero_of_derivative_right _ H hd h0)

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

theorem polynomialMatrixDerivative_kronecker {ι κ τ υ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) (Q : Matrix τ υ (Polynomial ℂ)) :
    polynomialMatrixDerivative (P ⊗ₖ Q)=
      polynomialMatrixDerivative P ⊗ₖ Q+P ⊗ₖ polynomialMatrixDerivative Q := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [polynomialMatrixDerivative,Matrix.kroneckerMap,derivative_mul]

theorem polynomialMatrixCoeff_kronecker_zero {ι κ τ υ : Type*}
    (P : Matrix ι κ (Polynomial ℂ)) (Q : Matrix τ υ (Polynomial ℂ)) :
    polynomialMatrixCoeff (P ⊗ₖ Q) 0=polynomialMatrixCoeff P 0 ⊗ₖ polynomialMatrixCoeff Q 0 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [polynomialMatrixCoeff,Matrix.kroneckerMap]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_LimitCARReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def wedgeDelta (Q : ℕ) (j k a b : Fin (Q+1)) : ℂ :=
  delta j a * delta k b - delta k a * delta j b

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_PhysicalPairRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix Kronecker

noncomputable def physicalPairInclusion (Q : ℕ) := (Spin.pairInclusion Q).map Complex.ofReal

end Laughlin.Rotation

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

noncomputable def threeBodyGramSlice (Q z : ℕ) (hz : z ≤ Q)
    (p q : Fin (z+1)) : ℝ :=
  (if p = q then 1 else 0) - 2*∑ t : Fin (Q+1),
    pairCoefficient Q p.val (sliceOrbital Q z hz q) t *
      pairCoefficient Q q.val (sliceOrbital Q z hz p) t

end Laughlin.Fock

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

abbrev GenericCoupledIndex (A B : ℕ) :=
  Σ z : Fin (min A B+1), Fin (genericCoupledWeight A B z.val+1)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Mixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def sourceMixer : SourceSU2 := by
  let c : ℝ := Real.sqrt (1/2)
  have hc : (c : ℂ)^2=(1/2 : ℂ) := by
    have hs : c^2=(1/2 : ℝ) := Real.sq_sqrt (by norm_num)
    have h := congrArg Complex.ofReal hs
    push_cast at h
    exact h
  refine ⟨!![(c : ℂ),-(c : ℂ);(c : ℂ),(c : ℂ)],?_⟩
  constructor
  · apply Matrix.mem_unitaryGroup_iff.mpr
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply] <;>
      linear_combination 2*hc
  · simp [Matrix.det_fin_two]
    linear_combination 2*hc

end Laughlin.Rotation

end OAI
end


