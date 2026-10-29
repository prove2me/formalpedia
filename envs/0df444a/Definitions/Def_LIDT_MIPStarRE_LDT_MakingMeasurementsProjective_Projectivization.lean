-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:54:42.722437+00:00
-- url     : https://prove2.me/theorems/703f9041-328c-4834-961f-98bc4cf78518
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / Projectivization
-- statement:
--   This bundle supplies the operator inequalities used to turn submeasurements into projective submeasurements. It combines tensor-placement identities, Cauchy-Schwarz estimates, diagonal positivity, overlap bounds, and the zero projective family used in degenerate cases.
--
--   Principal definitions:
--   - `leftTensor_outcome_mul_conjTranspose_eq`: the left-tensor product of an outcome with its adjoint equals the tensor of the outcome square for Hermitian effects.
--   - `rightTensor_outcome_conjTranspose_mul_eq`: the corresponding right-tensor identity.
--   - `abs_sum_ev_opTensor_le_sqrt_mul_sqrt`: a Cauchy-Schwarz bound for a finite sum of tensor-product outcome expectations.
--   - `sum_ev_leftTensor_outcome_sq_nonneg`: nonnegativity of the left diagonal-mass sum.
--   - `sum_ev_rightTensor_outcome_sq_nonneg`: nonnegativity of the right diagonal-mass sum.
--   - `sum_ev_opTensor_outcome_le_totalMass`: the outcome-overlap sum is bounded by the total state mass.
--   - `totalMass_sub_two_defect_le_diagA`: a lower bound on the left diagonal mass in terms of overlap and bipartite consistency defect.
--   - `zeroProjSubMeas`: the zero outcome family as a projective submeasurement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean#L33-L598

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Rounding To Projectors Core

Internal lemmas for the orthogonalization and rounding-to-projectors chain.

This file extracts the consistency-to-almost-projective and spectral/rounding
steps so that `QXPLayer.lean` can depend on them without importing the full
Section 5 theorem file.

## References

- `references/ldt-paper/orthonormalization.tex`
- `blueprint/src/chapter/ch04_projective.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Orthonormalization helper lemmas -/

/-- `leftTensor (A_a) * (leftTensor (A_a))ᴴ = leftTensor (A_a * A_a)` for Hermitian outcomes. -/
private lemma leftTensor_outcome_mul_conjTranspose_eq
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas Outcome ιA) (a : Outcome) :
    leftTensor (ι₂ := ιB) (A.outcome a) *
        (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
      leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a) := by
  rw [leftTensor_conjTranspose, A.outcome_hermitian, leftTensor_mul_leftTensor]

/-- The right-tensor analogue of
`leftTensor_outcome_mul_conjTranspose_eq`. -/
private lemma rightTensor_outcome_conjTranspose_mul_eq
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (B : SubMeas Outcome ιB) (a : Outcome) :
    (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ *
        rightTensor (ι₁ := ιA) (B.outcome a) =
      rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a) := by
  rw [rightTensor_conjTranspose, B.outcome_hermitian, rightTensor_mul_rightTensor]

/-- Cauchy–Schwarz bound for the sum `∑_a ⟨ψ | A_a ⊗ B_a | ψ⟩`, expressed in
terms of the left/right diagonal masses. -/
 lemma abs_sum_ev_opTensor_le_sqrt_mul_sqrt
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) :
    |∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))| ≤
      Real.sqrt
          (∑ a : Outcome,
            ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))) := by
  have hX := fun a : Outcome =>
    leftTensor_outcome_mul_conjTranspose_eq (ιB := ιB) A a
  have hY := fun a : Outcome =>
    rightTensor_outcome_conjTranspose_mul_eq (ιA := ιA) B a
  simpa [leftTensor_mul_rightTensor_eq_opTensor, hX, hY,
      -leftTensor_conjTranspose, -rightTensor_conjTranspose] using
    MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt ψ
      (fun a => leftTensor (ι₂ := ιB) (A.outcome a))
      (fun a => rightTensor (ι₁ := ιA) (B.outcome a))

/-- The `diagA` sum (in terms of `leftTensor (A_a * A_a)`) is nonnegative. -/
 lemma sum_ev_leftTensor_outcome_sq_nonneg
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA) :
    0 ≤ ∑ a : Outcome,
          ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) := by
  refine Finset.sum_nonneg fun a _ => ?_
  have h := ev_adjoint_self_nonneg ψ (leftTensor (ι₂ := ιB) (A.outcome a))
  rwa [leftTensor_conjTranspose, A.outcome_hermitian, leftTensor_mul_leftTensor] at h

/-- The `diagB` sum (in terms of `rightTensor (B_a * B_a)`) is nonnegative. -/
 lemma sum_ev_rightTensor_outcome_sq_nonneg
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (B : SubMeas Outcome ιB) :
    0 ≤ ∑ a : Outcome,
          ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a)) := by
  refine Finset.sum_nonneg fun a _ => ?_
  rw [← rightTensor_outcome_conjTranspose_mul_eq (ιA := ιA) B a]
  exact ev_adjoint_self_nonneg ψ (rightTensor (ι₁ := ιA) (B.outcome a))

/-- Bound the overlap sum `∑_a ⟨ψ | A_a ⊗ B_a | ψ⟩` by the total mass
`⟨ψ | 1 | ψ⟩` using `B.outcome a ≤ 1` and `A`'s completeness. -/
 lemma sum_ev_opTensor_outcome_le_totalMass
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) ≤
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
  have hleft_one :
      ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
        ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    simpa using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            opTensor_le_leftTensor (ι₂ := ιB)
              (A.outcome_pos a) (Measurement.outcome_le_one B a)
    _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
          rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
          rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
          simp [A.sum_eq_total]
    _ = ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
          rw [A.total_eq_one]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := hleft_one

/-- Lower bound for the `diagA` sum in terms of the overlap and the bipartite
consistency defect, obtained from the Cauchy–Schwarz squared bound. -/
 lemma totalMass_sub_two_defect_le_diagA
    {diagA diagB totalMass defect overlap : Error}
    (hdiagA_nonneg : 0 ≤ diagA)
    (hdefect_nonneg : 0 ≤ defect)
    (hdefect_eq : defect = totalMass - overlap)
    (hoverlap_sq : overlap ^ 2 ≤ diagA * diagB)
    (hdiagB_le : diagB ≤ totalMass) :
    totalMass - 2 * defect ≤ diagA := by
  by_cases hsmall : totalMass ≤ defect
  · linarith
  · have hmass_pos : 0 < totalMass := by
      have hdefect_lt : defect < totalMass := lt_of_not_ge hsmall
      linarith
    have hoverlap_eq : overlap = totalMass - defect := by linarith [hdefect_eq]
    have hsquare : (totalMass - defect) ^ 2 ≤ diagA * totalMass := by
      nlinarith [hoverlap_eq, hoverlap_sq, hdiagB_le, hdiagA_nonneg]
    nlinarith [hsquare, hmass_pos]

/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`. The Cauchy–Schwarz chain and tensor
hermitian identities have been factored out above, so the main proof is now a
straightforward combination of those helpers.
-/
private lemma qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qSSCDefect ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) ≤
      2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
  classical
  let diagA : Error :=
    ∑ a : Outcome,
      ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))
  let diagB : Error :=
    ∑ a : Outcome,
      ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let defect : Error := qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas
  have hdefect_nonneg : 0 ≤ defect :=
    qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas
  have hdiagA_nonneg : 0 ≤ diagA :=
    sum_ev_leftTensor_outcome_sq_nonneg (ιB := ιB) ψ A.toSubMeas
  have hdiagB_nonneg : 0 ≤ diagB :=
    sum_ev_rightTensor_outcome_sq_nonneg (ιA := ιA) ψ B.toSubMeas
  have hleft_one :
      ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
        totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hright_one :
      ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) = totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (rightTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hleftPlaced_outcome :
      ∀ a : Outcome,
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a =
          leftTensor (ι₂ := ιB) (A.outcome a) := by
    intro a
    rfl
  have hleftPlaced_total :
      (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total =
        leftTensor (ι₂ := ιB) A.total :=
    rfl
  have hrightPlaced_outcome :
      ∀ a : Outcome,
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a =
          rightTensor (ι₁ := ιA) (B.outcome a) := by
    intro a
    rfl
  have hrightPlaced_total :
      (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).total =
        rightTensor (ι₁ := ιA) B.total :=
    rfl
  have hdiagA_le : diagA ≤ totalMass := by
    calc
      diagA ≤ ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
        simpa [diagA, hleftPlaced_outcome, hleftPlaced_total, leftTensor_mul_leftTensor,
          A.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      _ = totalMass := hleft_one
  have hdiagB_le : diagB ≤ totalMass := by
    calc
      diagB ≤ ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
        simpa [diagB, hrightPlaced_outcome, hrightPlaced_total,
          rightTensor_mul_rightTensor, B.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      _ = totalMass := hright_one
  have hoverlap_le : overlap ≤ totalMass :=
    sum_ev_opTensor_outcome_le_totalMass (ψ := ψ) A B
  have habs : |overlap| ≤ Real.sqrt diagA * Real.sqrt diagB :=
    abs_sum_ev_opTensor_le_sqrt_mul_sqrt (ψ := ψ) A.toSubMeas B.toSubMeas
  have hoverlap_upper : overlap ≤ Real.sqrt diagA * Real.sqrt diagB :=
    (abs_le.mp habs).2
  have hoverlap_sq : overlap ^ 2 ≤ diagA * diagB := by
    have hsq :
        overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := by
      have hoverlap_nonneg : 0 ≤ overlap :=
        Finset.sum_nonneg fun a _ =>
          ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)
      nlinarith [hoverlap_nonneg, hoverlap_upper,
        Real.sqrt_nonneg diagA, Real.sqrt_nonneg diagB]
    calc
      overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := hsq
      _ = diagA * diagB := by
            ring_nf
            rw [Real.sq_sqrt hdiagA_nonneg, Real.sq_sqrt hdiagB_nonneg]
  have hdefect_eq : defect = totalMass - overlap := by
    have hoverlap_le_totalOverlap :
        overlap ≤ ev ψ (opTensor A.total B.total) := by
      simpa [totalMass, A.total_eq_one, B.total_eq_one, opTensor] using hoverlap_le
    dsimp [defect]
    unfold qBipartiteConsDefect
    rw [show qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas = overlap by rfl]
    rw [show (let totalOverlap := ev ψ (opTensor A.total B.total);
          max 0 (totalOverlap - overlap)) =
        max 0 (ev ψ (opTensor A.total B.total) - overlap) by rfl]
    rw [max_eq_right (sub_nonneg.mpr hoverlap_le_totalOverlap)]
    simp [totalMass, A.total_eq_one, B.total_eq_one, opTensor]
  have hdiagA_lower : totalMass - 2 * defect ≤ diagA :=
    totalMass_sub_two_defect_le_diagA
      hdiagA_nonneg hdefect_nonneg hdefect_eq hoverlap_sq hdiagB_le
  have hinner : totalMass - diagA ≤ 2 * defect := by linarith
  have htarget_nonneg : 0 ≤ 2 * defect := by linarith
  have hmax : max 0 (totalMass - diagA) ≤ 2 * defect :=
    max_le_iff.mpr ⟨htarget_nonneg, hinner⟩
  have hmax' : max 0 (ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) - diagA) ≤
      2 * defect := by
    simpa [hleft_one] using hmax
  simpa [qSSCDefect, diagA, hleftPlaced_outcome, hleftPlaced_total,
    leftTensor_mul_leftTensor, A.total_eq_one] using hmax'



 lemma sourceAlmostProjective_of_ssc {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (η : Error)
    (hssc : qSSCDefect ψ A.toSubMeas ≤ η) :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ η := by
  classical
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hsource_eq :
      ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a) =
        ev ψ A.toSubMeas.total - diagA := by
    calc
      ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a)
          = ∑ a : Outcome,
              (ev ψ (A.outcome a) - ev ψ (A.outcome a * A.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact ev_sub ψ (A.outcome a) (A.outcome a * A.outcome a)
      _ = (∑ a : Outcome, ev ψ (A.outcome a)) -
            ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) := by
            rw [Finset.sum_sub_distrib]
      _ = ev ψ A.toSubMeas.total - diagA := by
            rw [← ev_sum ψ A.outcome, A.toSubMeas.sum_eq_total]
  have hssc' : max 0 (ev ψ A.toSubMeas.total - diagA) ≤ η := by
    simpa [qSSCDefect, diagA] using hssc
  calc
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)
      = ev ψ A.toSubMeas.total - diagA := hsource_eq
    _ ≤ max 0 (ev ψ A.toSubMeas.total - diagA) := le_max_right 0 _
    _ ≤ η := hssc'

/-- The source idempotence defect of a measurement is nonnegative. -/
lemma sourceAlmostProjective_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) :
    0 ≤ ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
  refine Finset.sum_nonneg ?_
  intro a _
  exact ev_nonneg_of_psd ψ _ <|
    sub_nonneg.mpr <|
      MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)

/-- Consistency implies almost-projective: if `A` is `ζ`-consistent
with `B`, then `A` is `2ζ`-almost-projective. -/
lemma consistencyToAlmostProjective {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      AlmostProjMeasStatement ψ
        (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ) := by
  intro hCons
  classical
  let A_lifted : Measurement Outcome (ιA × ιB) :=
    leftLiftedMeasurement (ιB := ιB) A
  have hCons' :
      qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hCons.offDiagonalBound
  have hζ_nonneg : 0 ≤ ζ := by
    exact le_trans (qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas) hCons'
  have hsscBound :
      qSSCDefect ψ A_lifted.toSubMeas ≤ consistencyToAlmostProjectiveError ζ := by
    calc
      qSSCDefect ψ A_lifted.toSubMeas
        ≤ 2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
            simpa [A_lifted, leftLiftedMeasurement, leftPlacedSubMeas] using
              qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect
                (ψ := ψ) A B
      _ ≤ 2 * ζ := by
            exact mul_le_mul_of_nonneg_left hCons' (by norm_num)
      _ = consistencyToAlmostProjectiveError ζ := by
            simp [consistencyToAlmostProjectiveError]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    rw [MIPStarRE.LDT.Preliminaries.constFamily_ssc_unit]
    exact hsscBound
  · constructor
    calc
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily A_lifted.toSubMeas)
          (constSubMeasFamily A_lifted.toSubMeas)
        = 0 := sddError_self ψ (uniformDistribution Unit) _
      _ ≤ 2 * consistencyToAlmostProjectiveError ζ := by
            dsimp [consistencyToAlmostProjectiveError]
            nlinarith [hζ_nonneg]
  · exact sourceAlmostProjective_of_ssc ψ A_lifted _ hsscBound



/-- The zero family is a projective submeasurement. This supplies trivial
large-error branches where the target error bound is already at least the
universal `qSDD ≤ 1` estimate. -/
def zeroProjSubMeas {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :
    ProjSubMeas Outcome ι where
  toSubMeas :=
    { outcome := fun _ => 0
      total := 0
      outcome_pos := fun _ => le_rfl
      sum_eq_total := Fintype.sum_eq_zero _ fun _ => rfl
      total_le_one := zero_le_one }
  proj := fun _ => by simp

/-- The zero projective submeasurement is within unit `qSDD` of any lifted
submeasurement on a normalized state. -/
lemma qSDD_leftPlaced_zeroProjSubMeas_le_one {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ιA) :
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) A)
      (leftPlacedSubMeas (ιB := ιB)
        (zeroProjSubMeas (Outcome := Outcome) (ι := ιA)).toSubMeas) ≤ 1 := by
  have hq :
      qSDD ψ (leftPlacedSubMeas (ιB := ιB) A)
          (leftPlacedSubMeas (ιB := ιB)
            (zeroProjSubMeas (Outcome := Outcome) (ι := ιA)).toSubMeas) =
        ∑ a : Outcome,
          ev ψ (((leftPlacedSubMeas (ιB := ιB) A).outcome a) *
            ((leftPlacedSubMeas (ιB := ιB) A).outcome a)) := by
    unfold qSDD qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    let Z : MIPStarRE.Quantum.Op (ιA × ιB) := (leftPlacedSubMeas (ιB := ιB) A).outcome a
    have hzero :
        (leftPlacedSubMeas (ιB := ιB)
          (zeroProjSubMeas (Outcome := Outcome) (ι := ιA)).toSubMeas).outcome a = 0 := by
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [zeroProjSubMeas, leftPlacedSubMeas, leftTensor, h₁, h₂]
    calc
      ev ψ
          ((Z -
              (leftPlacedSubMeas (ιB := ιB)
                (zeroProjSubMeas (Outcome := Outcome) (ι := ιA)).toSubMeas).outcome a)ᴴ *
            (Z - (leftPlacedSubMeas (ιB := ιB)
              (zeroProjSubMeas (Outcome := Outcome) (ι := ιA)).toSubMeas).outcome a))
        = ev ψ (Zᴴ * Z) := by
            rw [hzero]
            simp
      _ = ev ψ (Z * Z) := by
            rw [SubMeas.outcome_hermitian (leftPlacedSubMeas (ιB := ιB) A) a]
      _ = ev ψ (((leftPlacedSubMeas (ιB := ιB) A).outcome a) *
            ((leftPlacedSubMeas (ιB := ιB) A).outcome a)) := by
            rfl
  rw [hq]
  simpa using
    MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ
      (leftPlacedSubMeas (ιB := ιB) A)



end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


