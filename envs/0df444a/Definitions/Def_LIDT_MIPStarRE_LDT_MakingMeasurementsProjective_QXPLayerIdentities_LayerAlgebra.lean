-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:27:36.005983+00:00
-- url     : https://prove2.me/theorems/93b9cf98-7e10-4c60-807c-e87e3574e971
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayerIdentities / LayerAlgebra
-- statement:
--   This bundle records the algebra of the Q/X/XHat/P layer used to repair submeasurements. It rewrites Q and X expressions, proves Hermitian and positivity properties, defines the squared difference and canonical projective submeasurement, and packages the total-domination invariant.
--
--   Principal definitions:
--   - `qaRestated`: restates the operator Q_a in the layer notation.
--   - `xExpressionToQExpression`: converts an X-layer expression into its Q-layer form.
--   - `x_mul_xHat_adjoint_isHermitian`: proves that X times XHat adjoint is Hermitian.
--   - `x_mul_xHat_adjoint_sq`: identifies its square with X times X adjoint.
--   - `x_mul_xHat_adjoint_nonneg`: proves positivity of the same operator.
--   - `squaredDifference`: defines the layer's squared-difference operator.
--   - `qxpProjSubMeas`: constructs the canonical projective submeasurement.
--   - `QXPLayerTotalDomination`: records domination of the total operator in the repair.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/LayerAlgebra.lean#L32-L718

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/LayerAlgebra.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Q/X/XHat/P algebraic identities

Algebraic identities for the `Q/X/XHat/P` layer, including the
restatements of `Q_a`, `P_a`, the mixed product, and projectivity of `P`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section



/-- **`Q_a` restated** (`lem:qa-restated`).

Rewrites the paper's operator `Q_a` in terms of `X_a`, `X`, and `T_a`. -/
lemma qaRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Qa data.qLayer a = (Xa data a)ᴴ * Xa data a ∧
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x ∧
      Qa data.qLayer a = (Xa data a)ᴴ * data.x := by
  have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
    simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
  constructor
  · calc
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
      _ = (Xa data a)ᴴ * Xa data a := by
        symm
        calc
          (Xa data a)ᴴ * Xa data a =
              data.xᴴ * Ta data.qLayer a * (Ta data.qLayer a * data.x) := by
                simp [Xa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
            _ = data.xᴴ * Ta data.qLayer a * data.x := by
                  simpa [Ta, Matrix.mul_assoc] using
                    congrArg (fun M => data.xᴴ * (M * data.x)) (data.qLayer.t.proj a)
  · constructor
    · exact data.qa_eq a
    · calc
        Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
        _ = (Xa data a)ᴴ * data.x := by
          simp [Xa, Matrix.conjTranspose_mul, hTa]

















/-- **`X`-expression to `Q`-expression** (`lem:X-expression-to-Q-expression`).

Converts the quadratic error term in `X X† - I` to the corresponding
`Q_a Q Q_a - Q_a` expression. -/
lemma xExpressionToQExpression {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
  have hQaSq : Qa data.qLayer a * Qa data.qLayer a = Qa data.qLayer a := by
    exact (data.qa_projective a).isIdempotentElem.eq
  have hQaXa : (Xa data a)ᴴ * Xa data a = Qa data.qLayer a := by
    exact (qaRestated data a).1.symm
  have hQaLeft : (Xa data a)ᴴ * data.x = Qa data.qLayer a := by
    exact (qaRestated data a).2.2.symm
  have hQaRight : data.xᴴ * Xa data a = Qa data.qLayer a := by
    simpa [Qa, Xa, Matrix.mul_assoc] using (data.qa_eq a).symm
  calc
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      ((Xa data a)ᴴ * ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1))) *
        Xa data a := by
          rw [Matrix.mul_assoc]
    _ = ((Xa data a)ᴴ *
          (data.x * data.xᴴ * (data.x * data.xᴴ) + (-2 • (data.x * data.xᴴ) + 1))) *
        Xa data a := by
          congr 1
          noncomm_ring
    _ =
        (Xa data a)ᴴ * data.x * (data.xᴴ * data.x * (data.xᴴ * Xa data a)) +
          (-2 • ((Xa data a)ᴴ * data.x * (data.xᴴ * Xa data a)) +
            (Xa data a)ᴴ * Xa data a) := by
          rw [Matrix.mul_assoc]
          rw [Matrix.add_mul, Matrix.add_mul]
          rw [Matrix.mul_add, Matrix.mul_add]
          have hneg :
              (Xa data a)ᴴ * ((-(data.x * data.xᴴ) + -(data.x * data.xᴴ)) * Xa data a) =
                -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) +
                  -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) := by
            rw [Matrix.add_mul]
            rw [Matrix.mul_add]
            simp [Matrix.mul_assoc]
          simp [Matrix.mul_assoc, two_smul, hneg]
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      simp only [Matrix.mul_assoc, hQaXa, hQaLeft, hQaRight, data.x_gram_right, hQaSq,
        Int.reduceNeg, neg_smul, zsmul_eq_mul, Int.cast_ofNat]
      noncomm_ring
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      noncomm_ring









private lemma xHat_mixed_adjoint {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHatᴴ * data.x = CFC.sqrt (QTotal data.qLayer) := by
  calc
    data.xHatᴴ * data.x = (data.xᴴ * data.xHat)ᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = (CFC.sqrt (QTotal data.qLayer))ᴴ := by rw [data.xHat_mixed]
    _ = CFC.sqrt (QTotal data.qLayer) := by
      simpa using
        (Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg (QTotal data.qLayer))).isHermitian.eq



/-- The operator `X Xhat†` is Hermitian in a QXP layer. -/
lemma x_mul_xHat_adjoint_isHermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ)ᴴ = data.x * data.xHatᴴ := by
  calc
    (data.x * data.xHatᴴ)ᴴ = data.xHat * data.xᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
      calc
        data.xHat * data.xᴴ = data.xHat * (data.xᴴ * (data.xHat * data.xHatᴴ)) := by
          rw [data.xHat_coisometry]
          simp
        _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          simp [Matrix.mul_assoc]
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [data.xHat_mixed, ← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]

/-- The square of `X Xhat†` is `X X†` in a QXP layer. -/
lemma x_mul_xHat_adjoint_sq {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ) = data.x * data.xᴴ := by
  calc
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ)
        = data.x * (data.xHatᴴ * data.x) * data.xHatᴴ := by
            simp [Matrix.mul_assoc]
    _ = data.x * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          rw [xHat_mixed_adjoint data, data.xHat_mixed]
    _ = data.x * data.xᴴ := by
          simp [Matrix.mul_assoc, data.xHat_coisometry]

/-- The operator `X Xhat†` is positive semidefinite in a QXP layer. -/
lemma x_mul_xHat_adjoint_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    0 ≤ data.x * data.xHatᴴ := by
  have hsqrt_nonneg : 0 ≤ CFC.sqrt (QTotal data.qLayer) :=
    CFC.sqrt_nonneg (QTotal data.qLayer)
  calc
    0 ≤ data.xHat * CFC.sqrt (QTotal data.qLayer) * data.xHatᴴ := by
      exact
        (Matrix.PosSemidef.mul_mul_conjTranspose_same
          (Matrix.nonneg_iff_posSemidef.mp hsqrt_nonneg)
          data.xHat).nonneg
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]



/-- **Squared difference** (`lem:squared-difference`).

Bounds the defect between `X` and `XHat` by the squared defect of `X X†`
from the auxiliary identity. -/
lemma squaredDifference {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ ≤
      (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by
  let Y : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier := data.x * data.xHatᴴ
  have hY_sub :
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := by
    have hYh : Yᴴ = Y := by
      simpa [Y] using x_mul_xHat_adjoint_isHermitian data
    have hYadj : data.xHat * data.xᴴ = Y := by
      simpa [Y, Matrix.conjTranspose_mul] using hYh
    have hYsq : data.x * data.xᴴ = Y * Y := by
      simpa [Y] using (x_mul_xHat_adjoint_sq data).symm
    calc
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ
          = (data.x - data.xHat) * (data.xᴴ - data.xHatᴴ) := by
              simp
      _ = data.x * (data.xᴴ - data.xHatᴴ) - data.xHat * (data.xᴴ - data.xHatᴴ) := by
            conv_lhs => rw [Matrix.sub_mul]
      _ = (data.x * data.xᴴ - data.x * data.xHatᴴ) -
            (data.xHat * data.xᴴ - data.xHat * data.xHatᴴ) := by
              conv_lhs => rw [Matrix.mul_sub, Matrix.mul_sub]
      _ = data.x * data.xᴴ - data.x * data.xHatᴴ - data.xHat * data.xᴴ +
            data.xHat * data.xHatᴴ := by
              abel
      _ = data.x * data.xᴴ - Y - Y + 1 := by
            simp [Y, hYadj, data.xHat_coisometry]
      _ = Y * Y - Y - Y + 1 := by rw [hYsq]
      _ = (Y - 1) * (Y - 1) := by
            noncomm_ring
  have hY_nonneg : 0 ≤ Y := by
    simpa [Y] using x_mul_xHat_adjoint_nonneg data
  have hYsq :
      Y * Y = data.x * data.xᴴ := by
    simpa [Y] using x_mul_xHat_adjoint_sq data
  have hY_herm : Yᴴ = Y := by
    simpa [Y] using x_mul_xHat_adjoint_isHermitian data
  have hYm1_herm : (Y - 1)ᴴ = Y - 1 := by
    simp [hY_herm]
  have hYp1_nonneg : 0 ≤ Y + 1 := add_nonneg hY_nonneg zero_le_one
  have hYp1_comm : Commute (Y + 1) Y := by
    change (Y + 1) * Y = Y * (Y + 1)
    simp [mul_add, add_mul]
  have hYp1_mul_nonneg : 0 ≤ (Y + 1) * Y := by
    exact Commute.mul_nonneg hYp1_nonneg hY_nonneg hYp1_comm
  have h_one_le_sq :
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) ≤ (Y + 1) * (Y + 1) := by
    have hYp1_le_sq : Y + 1 ≤ (Y + 1) * (Y + 1) := by
      apply sub_nonneg.mp
      calc
        (Y + 1) * (Y + 1) - (Y + 1) = (Y + 1) * ((Y + 1) - 1) := by
          rw [mul_sub]
          simp
        _ = (Y + 1) * Y := by simp
        _ ≥ 0 := hYp1_mul_nonneg
    exact le_trans (by simpa using add_le_add_right hY_nonneg 1) hYp1_le_sq
  have h_main :
      (Y - 1) * (Y - 1) ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := by
    simpa [Matrix.mul_assoc] using
      IsSelfAdjoint.conjugate_le_conjugate h_one_le_sq hYm1_herm
  have h_comm_pm : Commute (Y - 1) (Y + 1) := by
    change (Y - 1) * (Y + 1) = (Y + 1) * (Y - 1)
    simp [sub_eq_add_neg, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
  calc
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := hY_sub
    _ ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := h_main
    _ = ((Y - 1) * (Y + 1)) * ((Y - 1) * (Y + 1)) := by
          rw [← Matrix.mul_assoc, h_comm_pm.eq, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (Y * Y - 1) * (Y * Y - 1) := by
          congr 1 <;> noncomm_ring
    _ = (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by simp [hYsq]

/-- The sum of the QXP `P`-operators is the Gram operator `XHat† XHat`.

This is the total-mass identity for the canonical projective submeasurement
produced from the Q/X/XHat/P layer. -/
lemma sum_pa_eq_xHat_adjoint_mul_xHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (∑ a, Pa data a) = data.xHatᴴ * data.xHat := by
  classical
  have hsum_aux (s : Finset Outcome) :
      Finset.sum s (fun a => Pa data a) =
        data.xHatᴴ * (Finset.sum s fun a => Ta data.qLayer a) * data.xHat := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
        simp [Pa, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
  calc
    (∑ a, Pa data a) = data.xHatᴴ * (∑ a, Ta data.qLayer a) * data.xHat := by
      simpa using hsum_aux Finset.univ
    _ = data.xHatᴴ * data.xHat := by
      simpa [Ta] using
        congrArg (fun M => data.xHatᴴ * M * data.xHat) data.qLayer.t.sum_eq

/-- **Projectivity of `P`** (`lem:P-projectivity`).

The family `P_a` built from `XHat` and `T_a` is a projective
submeasurement. -/
lemma pProjectivity {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ P : ProjSubMeas Outcome ι,
      ∀ a : Outcome, P.outcome a = Pa data a := by
  classical
  refine ⟨{
    outcome := Pa data
    total := ∑ a, Pa data a
    outcome_pos := ?_
    sum_eq_total := rfl
    total_le_one := ?_
    proj := ?_
  }, ?_⟩
  · intro a
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (data.qLayer.t.toMeasurement.outcome_pos a))
        data.xHat).nonneg
  · let X : MIPStarRE.Quantum.Op ι := data.xHatᴴ * data.xHat
    have hX_sq : X * X = X := by
      dsimp [X]
      calc
        (data.xHatᴴ * data.xHat) * (data.xHatᴴ * data.xHat)
            = data.xHatᴴ * (data.xHat * data.xHatᴴ) * data.xHat := by
                simp [Matrix.mul_assoc]
        _ = data.xHatᴴ * data.xHat := by
              simp [data.xHat_coisometry]
    have hX_herm : Xᴴ = X := by
      dsimp [X]
      simp [Matrix.conjTranspose_mul]
    have hX_proj : MIPStarRE.Quantum.IsProj X :=
      { isIdempotentElem := hX_sq
        isSelfAdjoint := hX_herm }
    have h_one_sub_X_nonneg : 0 ≤ 1 - X := by
      exact hX_proj.one_sub_nonneg
    have hsum :
        (∑ a, Pa data a) = X := by
      simpa [X] using sum_pa_eq_xHat_adjoint_mul_xHat data
    rw [hsum]
    exact sub_nonneg.mp h_one_sub_X_nonneg
  · intro a
    calc
      Pa data a * Pa data a
          = data.xHatᴴ * Ta data.qLayer a * (data.xHat * data.xHatᴴ) *
              Ta data.qLayer a * data.xHat := by
                simp [Pa, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * Ta data.qLayer a * data.xHat := by
            simp [data.xHat_coisometry, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * data.xHat := by
            simp [Ta, data.qLayer.t.proj a, Matrix.mul_assoc]
      _ = Pa data a := rfl
  · intro a
    rfl

/-- The canonical projective submeasurement obtained from the Q/X/XHat/P
layer. Its outcomes are the paper's operators `P_a`. -/
noncomputable def qxpProjSubMeas {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ProjSubMeas Outcome ι :=
  Classical.choose (pProjectivity data)

@[simp] lemma qxpProjSubMeas_outcome {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (qxpProjSubMeas data).outcome a = Pa data a :=
  Classical.choose_spec (pProjectivity data) a









/-- Total-domination invariant for the QXP repair.

This proposition is the construction-level operator comparison required by the
paper-tight monotone-total route: the canonical projective family obtained from
the QXP layer has total operator bounded by the source submeasurement total.
It is deliberately stronger than state-dependent-distance closeness and should
be proved from the concrete repair, not inferred from the orthonormalization
error estimate alone. -/
structure QXPLayerTotalDomination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι) : Prop where
  /-- The projective QXP total is bounded by the source submeasurement total. -/
  total_le : (qxpProjSubMeas data).toSubMeas.total ≤ A.total

namespace QXPLayerTotalDomination





end QXPLayerTotalDomination

end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


