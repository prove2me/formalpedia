-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
-- name    : LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:36:05.260353+00:00
-- url     : https://prove2.me/theorems/5d4e26ea-f0b5-4a25-8d60-1415f4def559
-- title:
--   LIDT definitions: LDT / Test / StrategyPolynomialFamilies
-- statement:
--   This bundle defines packaged polynomial measurement families and their strategy properties. It supports constructing a family from slice measurements, averaging over slice heights, evaluating at a next-dimensional point, and recording completeness, point consistency, strong self-consistency, and boundedness inputs.
--
--   Principal definitions:
--   - `IdxPolyFamily`: a slice-indexed polynomial family with witness and domination data.
--   - `ofSliceMeas`: constructs a family from available slice measurements.
--   - `averagedSubMeas`: averages the slice family over heights.
--   - `evaluatedAtNextPoint`: evaluates the family at a point in the next dimension.
--   - `Complete`: completeness of the packaged family.
--   - `ConsistentWithPoints`: consistency with point measurements.
--   - `StronglySelfConsistent`: strong self-consistency of the family.
--   - `SliceBoundednessInput`: the boundedness input required by the paper's induction step.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean#L20-L284

-- Generated from MIPStarRE/LDT/Test/StrategyPolynomialFamilies.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
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
# Polynomial-family interfaces for the low individual degree test

Packaged slice-indexed polynomial-family interfaces extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Polynomial-family interfaces -/

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets.

The `witness` and `dominationTarget` fields store the per-slice PSD operator
`Z^x` and per-slice, per-polynomial operator `E_u A^{u,x}_{g(u)}` appearing in
the paper's boundedness hypothesis (`references/ldt-paper/commutativity-G.tex`,
item `data-processed-boundedness`). We store these operators explicitly rather
than hiding them behind ambient defaults, so each constructor must choose an
honest witness/target pair.

Callers without access to an ambient strategy can use `ofSliceMeas`, which takes
`Z^x := ∑_g G^x_g` and `dominationTarget x g := G^x_g`. Callers with access to a
symmetric strategy should prefer the constructor `ofSymStrat`,
which derives both fields from the strategy itself. -/
structure IdxPolyFamily (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  meas : IdxProjSubMeas (Fq params) (Polynomial params) ι
  witness : Fq params → MIPStarRE.Quantum.Op ι
  dominationTarget : Fq params → Polynomial params → MIPStarRE.Quantum.Op ι

-- NOTE: no global `Inhabited` instance for `IdxPolyFamily`; without an actual
-- slice family, any default would be a degenerate zero-family placeholder.

namespace IdxPolyFamily

/-- Honest local constructor when only the slice family `x ↦ G^x` is available.

This uses the slice total `∑_g G^x_g` as the witness operator and the concrete
outcome `G^x_g` as the domination target. -/
def ofSliceMeas {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    IdxPolyFamily params ι where
  meas := meas
  witness := fun x => (meas x).toSubMeas.total
  dominationTarget := fun x g => (meas x).toSubMeas.outcome g

@[simp] lemma ofSliceMeas_meas {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    (ofSliceMeas meas).meas = meas := rfl

@[simp] lemma ofSliceMeas_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) :
    (ofSliceMeas meas).witness x = (meas x).toSubMeas.total := rfl

@[simp] lemma ofSliceMeas_dominationTarget {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    (ofSliceMeas meas).dominationTarget x g = (meas x).toSubMeas.outcome g := rfl

/-- The averaged submeasurement `G = E_x G^x`: average the slice
measurements over the uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def averagedSubMeas {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    SubMeas (Polynomial params) ι :=
  averageIdxSubMeas (uniformDistribution (Fq params))
    (fun x => (family.meas x).toSubMeas)
    (uniformDistribution_weight_sum_le_one (Fq params))

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluatedAtNextPoint {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeas)

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in source-style
boundedness assumptions. -/
noncomputable def averagedPointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) (h : Polynomial params) :
    MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}` from the paper's
boundedness hypothesis. -/
noncomputable def averagedSlicePointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

/-- Slice-wise averaged total operator `E_u \sum_a A^{u,x}_a`.

For a genuine symmetric strategy this simplifies to `1`, but keeping the
strategy-shaped formula explicit records where the witness comes from. -/
noncomputable def averagedSliceTotalOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι) (x : Fq params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total)

@[simp] theorem averagedSliceTotalOperator_eq_one {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    averagedSliceTotalOperator strategy x = 1 := by
  unfold averagedSliceTotalOperator averageOperatorOverDistribution
  calc
    ∑ u ∈ (uniformDistribution (Point params)).support,
        (uniformDistribution (Point params)).weight u •
          (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total
      = ∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u • (1 : MIPStarRE.Quantum.Op ι) := by
            apply Finset.sum_congr rfl
            intro u _
            have htotal :
                (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total =
                  (1 : MIPStarRE.Quantum.Op ι) := by
              simpa using (strategy.pointMeasurement (appendPoint params u x)).total_eq_one
            rw [htotal]
    _ = (∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u) • (1 : MIPStarRE.Quantum.Op ι) := by
          rw [Finset.sum_smul]
    _ = 1 := by
          rw [uniformDistribution_weight_sum_eq_one (Point params), one_smul]

/-- Paper-facing constructor: bundle a slice submeasurement with a symmetric
strategy so that both the domination target and the witness are derived from the
strategy itself.

Concretely, `dominationTarget x g` is the averaged slice-point evaluation
operator `E_u A^{u,x}_{g(u)}` from `references/ldt-paper/commutativity-G.tex`,
and `witness x` is the corresponding averaged slice-total operator
`E_u \sum_a A^{u,x}_a`. Since point measurements are genuine measurements, this
witness simplifies to `1`, but its stored definition keeps the provenance
explicit. -/
noncomputable def ofSymStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    IdxPolyFamily params ι where
  meas := meas
  witness := averagedSliceTotalOperator strategy
  dominationTarget := fun x g => averagedSlicePointEvaluationOperator strategy x g

@[simp] lemma ofSymStrat_meas {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    (ofSymStrat strategy meas).meas = meas := rfl

theorem ofSymStrat_witness_eq_averagedSliceTotalOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) :
    (ofSymStrat strategy meas).witness x = averagedSliceTotalOperator strategy x := rfl

@[simp] lemma ofSymStrat_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) :
    (ofSymStrat strategy meas).witness x = 1 := by
  simp [ofSymStrat_witness_eq_averagedSliceTotalOperator]

@[simp] lemma ofSymStrat_dominationTarget {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    (ofSymStrat strategy meas).dominationTarget x g =
      averagedSlicePointEvaluationOperator strategy x g := rfl

structure Complete {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeas.liftLeft (1 - kappa)

structure ConsistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (strategy : SymStrat params.next ι) (zeta : Error) : Prop where
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta



structure StronglySelfConsistent {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceSelfConsistency :
    SDDRel ψ (uniformDistribution (Fq params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

/-- Paper-faithful boundedness input for slice-indexed polynomial families.

This structure encodes the boundedness item in
`references/ldt-paper/commutativity-G.tex` and `references/ldt-paper/ld-pasting.tex`.
It consists of positive witnesses `Z^x`, the averaged residual bound
`E_x <psi| (I - G^x) tensor Z^x |psi> <= zeta`, and the domination condition
`Z^x >= E_u A^{u,x}_{g(u)}`.

The domination condition is stated directly against the averaged point operator
from the strategy.  It is not mediated through `family.dominationTarget`, so this
public input does not contain an additional identification bridge. -/
structure SliceBoundednessInput {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  /-- Positivity of the slice witnesses `Z^x`. -/
  sliceOpPSD : ∀ x, 0 ≤ family.witness x
  /-- Averaged residual bound `E_x <psi| (I - G^x) tensor Z^x |psi> <= zeta`. -/
  sliceBoundedness :
    avgOver (uniformDistribution (Fq params))
      (fun x =>
        ev strategy.state <|
          leftTensor (ι₂ := ι) (1 - (family.meas x).toSubMeas.total) *
            rightTensor (ι₁ := ι) (family.witness x)) ≤ zeta
  /-- Paper domination condition `E_u A^{u,x}_{g(u)} <= Z^x`. -/
  sliceDominatesAveragedPoint :
    ∀ x : Fq params, ∀ g : Polynomial params,
      averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x

namespace SliceBoundednessInput

/-- The boundedness residual obtained from a concrete slice family `G`.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`
(`\label{thm:self-improvement-in-induction-section}`), especially the boundedness
field of the slice-wise self-improvement output.

This is the induction-oriented `Z^x ⊗ (I - G^x)` term after replacing the
abstract slice family by the concrete `G`, written in the paper's
`(I - G^x) ⊗ Z^x` orientation. -/
noncomputable def storedResidual {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (_hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ev strategy.state
    (leftTensor (ι₂ := ι) (1 - (G x).total) *
      rightTensor (ι₁ := ι) (family.witness x))





end SliceBoundednessInput

end IdxPolyFamily

end MIPStarRE.LDT

end

end LIDT


