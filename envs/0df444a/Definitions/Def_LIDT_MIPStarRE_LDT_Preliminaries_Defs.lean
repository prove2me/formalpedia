-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_Defs
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:34:43.14636+00:00
-- url     : https://prove2.me/theorems/17741725-977d-45eb-9fe9-27e8a00c60f1
-- title:
--   LIDT definitions: LDT / Preliminaries / Defs
-- statement:
--   This bundle defines the proposition-level records and operator families used by the preliminary consistency and completion arguments.
--
--   Principal definitions:
--   - `BipartiteSDDRel`: a bipartite state-dependent distance relation.
--   - `OpBounded01`: an operator-family boundedness record.
--   - `ConsAgreement`: a consistency-agreement record.
--   - `ConsSubMeasStmt`: a same-space consistency statement.
--   - `ConsSubMeasHeterogeneousStmt`: a heterogeneous consistency statement.
--   - `SwitchSandwichStmt`: the left and right switch-sandwich conditions.
--   - `CompTransferStmt`: a completeness-transfer statement.
--   - `completeAtOutcome`: completes a submeasurement at a selected outcome.
--   - `CompletingToMeasStmt`: records the completion-to-measurement construction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/Defs.lean#L40-L382

-- Generated from MIPStarRE/LDT/Preliminaries/Defs.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Preliminary definitions and statement structures

This file collects the lightweight statement and definition layer for the
preliminaries chapter of the LDT development. It records the paper's
consistency, sandwich, and completion statements in a form used by later files.

## Main definitions

- `BipartiteSDDRel`: the paper-style left/right state-dependent distance
  relation.
- `ConsAgreement`: the measurement reformulation of consistency.
- `ConsSubMeasStmt`, `SwitchSandwichStmt`, `CompTransferStmt`, and
  `CompletingToMeasStmt`: conclusion statements for the main preliminary
  propositions.
- `completeAtOutcome`: completion of a submeasurement at a distinguished
  outcome.

## References

- `references/ldt-paper/preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-! ## Consistency and distance statements -/

/-- Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`. -/
structure BipartiteSDDRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  leftRightSquaredDistanceBound :
    sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight B) ≤ δ

/-- Condition `0 ≤ B ≤ I` for the switch-sandwich argument. -/
structure OpBounded01 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : MIPStarRE.Quantum.Op ι) : Prop where
  nonnegative : 0 ≤ B
  boundedByIdentity : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - B

/-- Agreement probability from `prop:simeq-for-measurements`. -/
noncomputable def agreementProbability {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) : Error :=
  1 - bipartiteConsError ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)

/-- Conclusion statement for the measurement reformulation of consistency. -/
structure ConsAgreement {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error) : Prop where
  agreementLowerBound : agreementProbability ψ 𝒟 A B ≥ 1 - δ

/-- A diagonal sandwich family has total operator at most the identity. -/
 theorem diagonalSandwichFamily_total_le_one {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] (A : IdxSubMeas Question Outcome ιA)
    (B : IdxMeas Question Outcome ιB) (q : Question) :
    (∑ a : Outcome,
      leftTensor (ι₂ := ιB) ((A q).outcome a) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)) ≤ 1 := by
  calc
    ∑ a : Outcome,
        leftTensor (ι₂ := ιB) ((A q).outcome a) *
          rightTensor (ι₁ := ιA) ((B q).outcome a)
      ≤ ∑ a : Outcome, leftTensor (ι₂ := ιB) ((A q).outcome a) := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          rw [leftTensor_mul_rightTensor_eq_opTensor]
          exact opTensor_le_leftTensor
            ((A q).outcome_pos a) (Measurement.outcome_le_one (B q) a)
    _ = leftTensor (ι₂ := ιB) ((A q).total) := by
      rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ (fun a => (A q).outcome a)]
      rw [(A q).sum_eq_total]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ιB) (A q).total_le_one

/-- A total sandwich family has total operator at most the identity. -/
 theorem totalSandwichFamily_total_le_one {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] (A : IdxSubMeas Question Outcome ιA)
    (B : IdxMeas Question Outcome ιB) (q : Question) :
    (∑ a : Outcome,
      leftTensor (ι₂ := ιB) ((A q).total) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)) ≤ 1 := by
  calc
    ∑ a : Outcome,
        leftTensor (ι₂ := ιB) ((A q).total) *
          rightTensor (ι₁ := ιA) ((B q).outcome a)
      = leftTensor (ι₂ := ιB) ((A q).total) := by
          rw [← Finset.mul_sum]
          rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ (fun a => (B q).outcome a)]
          rw [(B q).sum_eq]
          simp [leftTensor, rightTensor]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ιB) (A q).total_le_one

/-- `A_a ⊗ B_a`, the diagonal bipartite family from `prop:cons-sub-meas`.

This same-space version is the specialization used by the existing
main-theorem path.  The paper-facing two-space version is
`heterogeneousDiagonalSandwichFamily`. -/
noncomputable def diagonalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome (ι × ι) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ι) ((A q).outcome a) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ι) ((A q).outcome a) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    outcome_pos := fun a => by
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg ((A q).outcome_pos a) ((B q).outcome_pos a)
    sum_eq_total := rfl
    total_le_one := by
      exact diagonalSandwichFamily_total_le_one A B q
  }

/-- `A ⊗ B_a`, the total bipartite family from `prop:cons-sub-meas`.

This same-space version is the specialization used by the existing
main-theorem path.  The paper-facing two-space version is
`heterogeneousTotalSandwichFamily`. -/
noncomputable def totalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome (ι × ι) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ι) ((A q).total) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ι) ((A q).total) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    outcome_pos := fun a => by
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg ((A q).total_nonneg) ((B q).outcome_pos a)
    sum_eq_total := rfl
    total_le_one := by
      exact totalSandwichFamily_total_le_one A B q
  }

/-- `A_a ⊗ B_a` for the two-space statement of `prop:cons-sub-meas`.

Here `A` acts on the left Hilbert space and `B` acts on the right Hilbert
space; the resulting family acts on the tensor-product state space
`ιA × ιB`. -/
noncomputable def heterogeneousDiagonalSandwichFamily {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxMeas Question Outcome ιB) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ιB) ((A q).outcome a) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ιB) ((A q).outcome a) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)
    outcome_pos := fun a => by
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg ((A q).outcome_pos a) ((B q).outcome_pos a)
    sum_eq_total := rfl
    total_le_one := by
      exact diagonalSandwichFamily_total_le_one A B q
  }

/-- `A ⊗ B_a` for the two-space statement of `prop:cons-sub-meas`.

The total operator `A^x = ∑_a A^x_a` remains on the left tensor factor, while
the measurement outcome `B^x_a` remains on the right tensor factor. -/
noncomputable def heterogeneousTotalSandwichFamily {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxMeas Question Outcome ιB) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ιB) ((A q).total) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ιB) ((A q).total) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)
    outcome_pos := fun a => by
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      exact _root_.LIDT.MIPStarRE.LDT.opTensor_nonneg ((A q).total_nonneg) ((B q).outcome_pos a)
    sum_eq_total := rfl
    total_le_one := by
      exact totalSandwichFamily_total_le_one A B q
  }

/-- Same-space output statement for `prop:cons-sub-meas`.

The paper-facing two-space output statement is
`ConsSubMeasHeterogeneousStmt`. -/
structure ConsSubMeasStmt {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) : Prop where
  diagonalControl :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (diagonalSandwichFamily A B) γ
  sandwichControl :
    SDDRel ψ 𝒟 (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ
  combinedControl :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (totalSandwichFamily A B) (4 * γ)

/-- Two-space output statement for `prop:cons-sub-meas`.

It records the two estimates
`A^x_a ⊗ I ≈_γ A^x_a ⊗ B^x_a` and
`A^x_a ⊗ B^x_a ≈_γ A^x ⊗ B^x_a`, and the resulting
`4γ` estimate from `A^x_a ⊗ I` to `A^x ⊗ B^x_a`. -/
structure ConsSubMeasHeterogeneousStmt {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxMeas Question Outcome ιB) (γ : Error) : Prop where
  /-- `A^x_a ⊗ I` is close to the diagonal family `A^x_a ⊗ B^x_a`. -/
  diagonalControl :
    SDDRel ψ 𝒟 (IdxSubMeas.placeLeft A) (heterogeneousDiagonalSandwichFamily A B) γ
  /-- The diagonal family `A^x_a ⊗ B^x_a` is close to `A^x ⊗ B^x_a`. -/
  sandwichControl :
    SDDRel ψ 𝒟
      (heterogeneousDiagonalSandwichFamily A B)
      (heterogeneousTotalSandwichFamily A B) γ
  /-- The two preceding estimates give `A^x_a ⊗ I ≈_{4γ} A^x ⊗ B^x_a`. -/
  combinedControl :
    SDDRel ψ 𝒟
      (IdxSubMeas.placeLeft A)
      (heterogeneousTotalSandwichFamily A B) (4 * γ)

/-! ## Sandwich expectations -/

/-- Averaged left term `E_x ∑_a ⟨ψ, (A_a B A_a ⊗ I) ψ⟩`. -/
noncomputable def leftSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) ((A q).outcome a) *
        leftTensor (ι₂ := ι) B *
        leftTensor (ι₂ := ι) ((A q).outcome a))

/-- Averaged middle term `E_x ∑_a ⟨ψ, (B ⊗ A_a) ψ⟩`. -/
noncomputable def middleSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) B *
        rightTensor (ι₁ := ι) ((A q).outcome a))

/-- Averaged right term `E_x ∑_a ⟨ψ, (B A_a ⊗ I) ψ⟩`. -/
noncomputable def rightSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) (B * (A q).outcome a))

/-- Conclusion statement for `prop:switch-sandwich`. -/
structure SwitchSandwichStmt {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (δ : Error) : Prop where
  leftSandwichTransfer :
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A B|
      ≤ 2 * Real.sqrt δ
  rightSandwichTransfer :
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B|
      ≤ Real.sqrt δ

/-- Conclusion statement for `prop:completeness-transfer-projective-P`. -/
structure CompTransferStmt {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) : Prop where
  completenessTransfer :
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε

/-! ## Completion -/

/-- The completed outcomes sum to the identity. -/
 theorem completeAtOutcome_sum_eq_one {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (B : SubMeas Outcome ι) (a0 : Outcome) :
    (∑ a : Outcome,
      if a = a0 then B.outcome a + (1 - B.total) else B.outcome a) = 1 := by
  have hsingle :
      (∑ x : Outcome, if x = a0 then 1 - B.total else 0) = 1 - B.total := by
    simp
  have hrewrite :
      (∑ a : Outcome, if a = a0 then B.outcome a + (1 - B.total) else B.outcome a) =
        ∑ a : Outcome, (B.outcome a + if a = a0 then 1 - B.total else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a = a0 <;> simp [h]
  rw [hrewrite, Finset.sum_add_distrib, B.sum_eq_total, hsingle]
  simp

/-- Canonical completion of `B` by adjoining the residual `I - Σ_a B_a`
to the distinguished outcome `a0`. -/
noncomputable def completeAtOutcome {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (B : SubMeas Outcome ι) (a0 : Outcome) : Measurement Outcome ι := by
  classical
  let residual := 1 - B.total
  exact {
    toSubMeas := {
      outcome := fun a =>
        if h : a = a0 then
          B.outcome a + residual
        else
          B.outcome a
      total := 1
      outcome_pos := fun a => by
        by_cases h : a = a0
        · simpa [h, residual] using
            add_nonneg (B.outcome_pos a0) (sub_nonneg.mpr B.total_le_one)
        · simp [h, B.outcome_pos a]
      sum_eq_total := by
        exact completeAtOutcome_sum_eq_one B a0
      total_le_one := le_rfl
    }
    total_eq_one := rfl
  }

/-- Analytic conclusion for `prop:completing-to-measurement` once a witness
`C` has been fixed.

The theorem `completingToMeasurement` separately records that the chosen witness
is the canonical completion `completeAtOutcome B a0`, so this structure stores
only the closeness statement from the paper. -/
structure CompletingToMeasStmt {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (C : Measurement Outcome ι) (a0 : Outcome) (δ ζ : Error) : Prop where
  closenessAfterCompletion :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily C.toSubMeas.liftLeft)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ)

end MIPStarRE.LDT.Preliminaries

end

end LIDT


