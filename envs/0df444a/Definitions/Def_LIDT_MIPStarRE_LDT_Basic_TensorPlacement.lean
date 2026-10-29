-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
-- name    : LIDT_MIPStarRE_LDT_Basic_TensorPlacement
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:51:34.064283+00:00
-- url     : https://prove2.me/theorems/d186017d-ab7b-405d-bdce-266469c79fce
-- title:
--   LIDT definitions: LDT / Basic / TensorPlacement
-- statement:
--   This bundle records algebraic identities for tensor placement, finite sums, weighted averages, and operator expectations. It also supplies positivity and sandwich-contraction bounds used in variance, polynomial-agreement, commutativity, and pasting estimates.
--
--   Principal definitions:
--   - `leftTensor_finset_sum`: Left placement commutes with a finite sum, $\sum_a(A_a\otimes I)=(\sum_aA_a)\otimes I$.
--   - `leftTensor_averageOperatorOverDistribution`: Left placement commutes with a weighted operator average.
--   - `ev_leftTensor_total_eq_sum_outcome`: The expectation of a left-placed submeasurement total equals the sum of the expectations of its left-placed outcomes.
--   - `rightTensor_finset_sum`: Right placement commutes with finite sums.
--   - `opTensor_averageOperatorOverDistribution_left`: Tensoring a fixed right operator commutes with averaging the left operator.
--   - `opTensor_averageOperatorOverDistribution_right`: Tensoring a fixed left operator commutes with averaging the right operator.
--   - `sandwichTensor_residual_sum_le_one`: A sum of positive sandwich terms formed from a submeasurement residual is bounded by the identity.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/TensorPlacement.lean#L23-L472

-- Generated from MIPStarRE/LDT/Basic/TensorPlacement.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Tensor-placement helper lemmas and sandwich tensor estimates

Tensor-sum commutation, positivity/boundedness preservation,
factoring lemmas, and sandwich-residual estimates used in
the main induction step and polynomial-agreement arguments.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Tensor-placement helper lemmas -/

/-- Left tensor placement commutes with finite sums. -/
theorem leftTensor_finset_sum {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₁) :
    Finset.sum s (fun a => leftTensor (ι₂ := ι₂) (f a)) =
      leftTensor (ι₂ := ι₂) (Finset.sum s f) := by
  classical
  simpa [leftTensor, opTensor] using
    (opTensor_sum_left_finset (s := s) (f := f)
      (B := (1 : MIPStarRE.Quantum.Op ι₂))).symm

/-- Left tensor placement commutes with operator averages. -/
theorem leftTensor_averageOperatorOverDistribution {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (𝒟 : Distribution α) (A : α → MIPStarRE.Quantum.Op ι₁) :
    leftTensor (ι₂ := ι₂) (averageOperatorOverDistribution 𝒟 A) =
      averageOperatorOverDistribution 𝒟 (fun a => leftTensor (ι₂ := ι₂) (A a)) := by
  unfold averageOperatorOverDistribution
  rw [← leftTensor_finset_sum (ι₂ := ι₂) 𝒟.support
    (fun a => 𝒟.weight a • A a)]
  refine Finset.sum_congr rfl ?_
  intro a _
  simpa [leftTensor, opTensor] using
    (opTensor_smul_left_error
      (ι₁ := ι₁) (ι₂ := ι₂) (𝒟.weight a) (A a) (1 : MIPStarRE.Quantum.Op ι₂))

/-- Expanding the left-tensor mass of a submeasurement on a bipartite state as
the sum of per-outcome left-tensor expectations.

This is a generic identity at the level of `ev ψ (leftTensor _)`: applying
`SubMeas.sum_eq_total`, pulling `leftTensor` through the finite sum via
`leftTensor_finset_sum`, and distributing `ev` through the sum via
`ev_finset_sum`. Using the definitional equalities
`subMeasMass ψ A.liftLeft = ev ψ A.liftLeft.total = ev ψ (leftTensor A.total)`,
this immediately yields the helper-stage opening
`subMeasMass ψ A.liftLeft = ∑ a, ev ψ (leftTensor (A.outcome a))` used in the
Section 9 / Section 12 calculations. -/
theorem ev_leftTensor_total_eq_sum_outcome {α : Type*} [Fintype α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A : SubMeas α ι) :
    ev ψ (leftTensor (ι₂ := ι) A.total) =
      ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
  rw [← A.sum_eq_total,
      ← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a : α => A.outcome a),
      ev_finset_sum]

/-- Evaluation of a left-placed operator average is the average of the
left-placed evaluations. -/
theorem ev_leftTensor_averageOperatorOverDistribution {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂)) (𝒟 : Distribution α)
    (A : α → MIPStarRE.Quantum.Op ι₁) :
    ev ψ (leftTensor (ι₂ := ι₂) (averageOperatorOverDistribution 𝒟 A)) =
      avgOver 𝒟 (fun a => ev ψ (leftTensor (ι₂ := ι₂) (A a))) := by
  rw [leftTensor_averageOperatorOverDistribution]
  exact ev_averageOperatorOverDistribution ψ 𝒟
    (fun a => leftTensor (ι₂ := ι₂) (A a))

/-- Right tensor placement commutes with finite sums. -/
theorem rightTensor_finset_sum {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₂) :
    Finset.sum s (fun a => rightTensor (ι₁ := ι₁) (f a)) =
      rightTensor (ι₁ := ι₁) (Finset.sum s f) := by
  classical
  simpa [rightTensor, opTensor] using
    (opTensor_sum_right_finset (A := (1 : MIPStarRE.Quantum.Op ι₁)) (s := s)
      (f := f)).symm





/-- Tensoring on the right commutes with operator averages in the left factor. -/
theorem opTensor_averageOperatorOverDistribution_left {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (𝒟 : Distribution α)
    (A : α → MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (averageOperatorOverDistribution 𝒟 A) B =
      averageOperatorOverDistribution 𝒟 (fun a => opTensor (A a) B) := by
  unfold averageOperatorOverDistribution
  rw [opTensor_sum_left_finset]
  refine Finset.sum_congr rfl ?_
  intro a _
  simpa using opTensor_smul_left_error (c := 𝒟.weight a) (A := A a) (B := B)

/-- Tensoring on the left commutes with operator averages in the right factor. -/
theorem opTensor_averageOperatorOverDistribution_right {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (𝒟 : Distribution α)
    (A : MIPStarRE.Quantum.Op ι₁) (B : α → MIPStarRE.Quantum.Op ι₂) :
    opTensor A (averageOperatorOverDistribution 𝒟 B) =
      averageOperatorOverDistribution 𝒟 (fun a => opTensor A (B a)) := by
  unfold averageOperatorOverDistribution
  rw [opTensor_sum_right_finset]
  refine Finset.sum_congr rfl ?_
  intro a _
  simpa using opTensor_smul_right_error (c := 𝒟.weight a) (A := A) (B := B a)

/-- Evaluation of an averaged left tensor factor is the average of the
corresponding tensor expectations. -/
theorem ev_opTensor_averageOperatorOverDistribution_left {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂)) (𝒟 : Distribution α)
    (A : α → MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    ev ψ (opTensor (averageOperatorOverDistribution 𝒟 A) B) =
      avgOver 𝒟 (fun a => ev ψ (opTensor (A a) B)) := by
  rw [opTensor_averageOperatorOverDistribution_left]
  exact ev_averageOperatorOverDistribution ψ 𝒟 (fun a => opTensor (A a) B)

/-- Evaluation of an averaged right tensor factor is the average of the
corresponding tensor expectations. -/
theorem ev_opTensor_averageOperatorOverDistribution_right {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂)) (𝒟 : Distribution α)
    (A : MIPStarRE.Quantum.Op ι₁) (B : α → MIPStarRE.Quantum.Op ι₂) :
    ev ψ (opTensor A (averageOperatorOverDistribution 𝒟 B)) =
      avgOver 𝒟 (fun a => ev ψ (opTensor A (B a))) := by
  rw [opTensor_averageOperatorOverDistribution_right]
  exact ev_averageOperatorOverDistribution ψ 𝒟 (fun a => opTensor A (B a))









/-- Left tensor placement preserves positivity. -/
theorem leftTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : 0 ≤ A) :
    0 ≤ leftTensor (ι₂ := ι₂) A := by
  simpa [leftTensor, opTensor] using
    (opTensor_nonneg
      (A := A) (B := (1 : MIPStarRE.Quantum.Op ι₂)) hA
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))

/-- Right tensor placement preserves positivity. -/
theorem rightTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : 0 ≤ A) :
    0 ≤ rightTensor (ι₁ := ι₁) A := by
  simpa [rightTensor, opTensor] using
    (opTensor_nonneg
      (A := (1 : MIPStarRE.Quantum.Op ι₁)) (B := A)
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₁) ≤ 1) hA)

/-- Left tensor placement preserves the operator bound `≤ 1`. -/
theorem leftTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : A ≤ 1) :
    leftTensor (ι₂ := ι₂) A ≤ 1 := by
  simpa [leftTensor, opTensor] using
    (opTensor_mono_left
      (A₁ := A) (A₂ := (1 : MIPStarRE.Quantum.Op ι₁))
      (B := (1 : MIPStarRE.Quantum.Op ι₂)) hA
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))



/-- Right tensor placement preserves the operator bound `≤ 1`. -/
theorem rightTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : A ≤ 1) :
    rightTensor (ι₁ := ι₁) A ≤ 1 := by
  simpa [rightTensor, leftTensor, opTensor] using
    (opTensor_le_leftTensor
      (A := (1 : MIPStarRE.Quantum.Op ι₁)) (B := A)
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₁) ≤ 1) hA)

namespace SubMeas

/-- A filtered diagonal tensor sum of two submeasurements is a contraction.

The estimate uses only positivity and the submeasurement total bound on the
left factor, together with the pointwise `≤ 1` bound on the right factor. -/
theorem opTensor_sum_filter_le_one {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (S T : SubMeas α ι) (P : α → Prop) [DecidablePred P] :
    ∑ x ∈ Finset.univ.filter P, opTensor (S.outcome x) (T.outcome x) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  calc
    ∑ x ∈ Finset.univ.filter P, opTensor (S.outcome x) (T.outcome x)
      ≤ ∑ x ∈ Finset.univ.filter P, leftTensor (ι₂ := ι) (S.outcome x) := by
          refine Finset.sum_le_sum ?_
          intro x _hx
          exact opTensor_le_leftTensor (S.outcome_pos x) (T.outcome_le_one x)
    _ ≤ ∑ x : α, leftTensor (ι₂ := ι) (S.outcome x) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
            (fun x _hmem _hnotmem => leftTensor_nonneg (S.outcome_pos x))
    _ = leftTensor (ι₂ := ι) S.total := by
          rw [← S.sum_eq_total]
          rw [leftTensor_finset_sum]
    _ ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact leftTensor_le_one S.total_le_one

end SubMeas

/-! ### Sandwich tensor estimates -/

/-- A single tensor summand with a sandwiched left register is nonnegative in
expectation.

The left register `Outer_o * Inner_i * Outer_o` is PSD by sandwich positivity,
and the right-register outcome is PSD, so their tensor product is PSD. -/
theorem sandwichTensorSummand_nonneg
    {α β γ ιA ιB : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (Outer : SubMeas β ιA) (Inner : SubMeas α ιA) (Right : SubMeas γ ιB)
    (o : β) (i : α) (r : γ) :
    0 ≤ ev ψ
      (leftTensor (ι₂ := ιB)
          (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
        rightTensor (ι₁ := ιA) (Right.outcome r)) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  exact ev_nonneg_of_psd ψ _ <|
    opTensor_nonneg
      (IsSelfAdjoint.conjugate_nonneg
        (Inner.outcome_pos i) (Outer.outcome_hermitian o))
      (Right.outcome_pos r)

/-- The residual tensor sum from a sandwiched left-register submeasurement and an
independent right-register submeasurement is at most one in a normalized state.

The operator under the sum factors as
`(∑ o, Outer_o * Inner.total * Outer_o) ⊗ Right.total`; the first factor is
bounded by `1` by the submeasurement axioms and sandwich monotonicity.  The
second factor is also bounded by `1`. -/
theorem sandwichTensor_residual_sum_le_one
    {α β γ ιA ιB : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hnorm : ψ.IsNormalized)
    (Outer : SubMeas β ιA) (Inner : SubMeas α ιA) (Right : SubMeas γ ιB) :
    (∑ ir : α × γ, ∑ o : β,
        ev ψ
          (leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2))) ≤ 1 := by
  let sandwichTotal : MIPStarRE.Quantum.Op ιA :=
    ∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o
  have hsandwichTotal_nonneg : 0 ≤ sandwichTotal := by
    exact Finset.sum_nonneg fun o _ =>
      IsSelfAdjoint.conjugate_nonneg
        (SubMeas.total_nonneg Inner) (Outer.outcome_hermitian o)
  have hsandwichTotal_le_one : sandwichTotal ≤ 1 := by
    calc
      sandwichTotal
        ≤ ∑ o : β, Outer.outcome o := by
            refine Finset.sum_le_sum ?_
            intro o _
            exact le_trans
              (IsSelfAdjoint.conjugate_le_conjugate
                Inner.total_le_one (Outer.outcome_hermitian o))
              (by
                simpa using
                  MIPStarRE.Quantum.sq_le_self
                    (Outer.outcome_pos o) (SubMeas.outcome_le_one Outer o))
      _ = Outer.total := Outer.sum_eq_total
      _ ≤ 1 := Outer.total_le_one
  have hop_sum :
      (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2)) =
        leftTensor (ι₂ := ιB) sandwichTotal * rightTensor (ι₁ := ιA) Right.total := by
    calc
      (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2))
        = ∑ i : α, ∑ r : γ, ∑ o : β,
            leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
              rightTensor (ι₁ := ιA) (Right.outcome r) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ i : α, ∑ o : β,
            leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
              rightTensor (ι₁ := ιA) Right.total := by
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (∑ r : γ, ∑ o : β,
                  leftTensor (ι₂ := ιB)
                      (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                    rightTensor (ι₁ := ιA) (Right.outcome r))
                = ∑ o : β, ∑ r : γ,
                    leftTensor (ι₂ := ιB)
                        (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                      rightTensor (ι₁ := ιA) (Right.outcome r) := by
                    rw [Finset.sum_comm]
              _ = ∑ o : β,
                    leftTensor (ι₂ := ιB)
                        (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                      rightTensor (ι₁ := ιA) Right.total := by
                    refine Finset.sum_congr rfl ?_
                    intro o _
                    rw [← Matrix.mul_sum]
                    rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ Right.outcome]
                    rw [Right.sum_eq_total]
      _ = (∑ i : α, ∑ o : β,
            leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome i * Outer.outcome o)) *
            rightTensor (ι₁ := ιA) Right.total := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.sum_mul]
      _ = leftTensor (ι₂ := ιB) sandwichTotal * rightTensor (ι₁ := ιA) Right.total := by
            congr 1
            calc
              ∑ i : α, ∑ o : β,
                  leftTensor (ι₂ := ιB)
                    (Outer.outcome o * Inner.outcome i * Outer.outcome o)
                = ∑ o : β, ∑ i : α,
                    leftTensor (ι₂ := ιB)
                      (Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    rw [Finset.sum_comm]
              _ = ∑ o : β,
                    leftTensor (ι₂ := ιB)
                      (∑ i : α,
                        Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    refine Finset.sum_congr rfl ?_
                    intro o _
                    rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ]
              _ = leftTensor (ι₂ := ιB)
                    (∑ o : β, ∑ i : α,
                      Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ]
              _ = leftTensor (ι₂ := ιB) sandwichTotal := by
                    congr 1
                    calc
                      ∑ o : β, ∑ i : α,
                          Outer.outcome o * Inner.outcome i * Outer.outcome o
                        = ∑ o : β,
                            Outer.outcome o * Inner.total * Outer.outcome o := by
                            refine Finset.sum_congr rfl ?_
                            intro o _
                            rw [← Matrix.sum_mul, ← Matrix.mul_sum, Inner.sum_eq_total]
                      _ = sandwichTotal := rfl
  calc
    (∑ ir : α × γ, ∑ o : β,
        ev ψ
          (leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2)))
      = ev ψ (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ιB)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ιA) (Right.outcome ir.2)) := by
          rw [ev_sum]
          refine Finset.sum_congr rfl ?_
          intro ir _
          rw [ev_sum]
    _ = ev ψ (leftTensor (ι₂ := ιB) sandwichTotal *
        rightTensor (ι₁ := ιA) Right.total) := by
          rw [hop_sum]
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
          apply ev_mono ψ _ _
          calc
            leftTensor (ι₂ := ιB) sandwichTotal * rightTensor (ι₁ := ιA) Right.total
              = opTensor sandwichTotal Right.total := by
                rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ιB) sandwichTotal :=
                opTensor_le_leftTensor hsandwichTotal_nonneg Right.total_le_one
            _ ≤ 1 := leftTensor_le_one (ι₂ := ιB) hsandwichTotal_le_one
    _ = 1 := ev_one_of_isNormalized ψ hnorm

end MIPStarRE.LDT

end

end LIDT


