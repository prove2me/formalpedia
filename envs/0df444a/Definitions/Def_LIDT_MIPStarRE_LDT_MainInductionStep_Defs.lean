-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Defs
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:36:15.95899+00:00
-- url     : https://prove2.me/theorems/17b49ab1-752b-4002-99e5-bba4593ed667
-- title:
--   LIDT definitions: LDT / MainInductionStep / Defs
-- statement:
--   This bundle defines the data and error quantities for restricted slice strategies in the main induction step. It lifts axis answers, packages complete point and line measurements, defines restricted diagonal families, and records failure and goodness predicates used by the successor construction.
--
--   Principal definitions:
--   - `liftAxisAnswer`: lifts an axis-line answer from a restricted slice to the ambient space.
--   - `RestrictedSymStrat`: packages the restricted slice strategy and its projective diagonal answer measurement.
--   - `axisParallelPointAnswerFamily`: the sampled point-answer family for the axis-parallel test.
--   - `axisParallelLineAnswerFamily`: the sampled axis-line answer family at the base point.
--   - `restrictedDiagonalPointAnswerFamily`: the point-answer family for a restricted diagonal test.
--   - `restrictedDiagonalLineAnswerFamily`: the restricted diagonal-line family at the base point.
--   - `axisParallelFailureProbability`: the failure surrogate for the axis-parallel test.
--   - `IsGood`: the goodness data required of a restricted strategy.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Defs.lean#L25-L533

-- Generated from MIPStarRE/LDT/MainInductionStep/Defs.lean by skeleton subtraction.
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
# Section 6 — Definitions

This file contains restriction/lifting maps, section-local error terms,
averaging operators, and tensor-placement bookkeeping for the induction step.

## References

- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lift an axis-line answer from the restricted slice back to the ambient space. -/
def liftAxisAnswer (params : Parameters) [FieldModel params.q] (x : Fq params) :
    AxisLinePolynomial params → AxisLinePolynomial params.next :=
  fun f => AxisLinePolynomial.appendAtHeight params f x

/-- Restricted slice data keeps the point and axis-parallel measurements
complete, and packages a genuine projective measurement on the slice's diagonal
answer space.

The paper's outcome-level formula would send a slice polynomial `f` to the
ambient outcome `append_x(f)`. With the current ambient diagonal answer
encoding, that map is not total on all ambient outcomes, so here we preserve the
verifier-visible base-point readout used in Chapter 10 instead: first
postprocess the ambient slice-preserving diagonal measurement to its value at
`zeroCoord` in `F_q`, then re-embed that `F_q`-valued projective measurement
into the honest slice answer space `DiagonalLinePolynomial params` using
canonical representatives.

This yields a complete projective measurement on the `(m,q,d)` diagonal answer
space whose base-point evaluation agrees with the ambient slice-preserving
branch, eliminating the earlier lossy submeasurement while remaining faithful
to the restricted diagonal test actually formalized here. -/
structure RestrictedSymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The bipartite state carried by the restricted strategy. -/
  state : QuantumState (ι × ι)
  /-- The restricted strategy reuses the ambient state's normalization witness. -/
  isNormalized : state.IsNormalized
  /-- The restricted point measurement. -/
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  /-- The restricted axis-parallel line measurement, packaged with transport covariance. -/
  axisParallelMeasurement : MIPStarRE.LDT.AxisParallelCovariantMeasurement params ι
  /-- The restricted diagonal-line measurement on the honest slice answer space. -/
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

namespace RestrictedSymStrat

/-- Sampled point answers in the axis-parallel lines test.
Point player receives `u` (base point) and answers at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  MIPStarRE.LDT.axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u` (parameter `zeroCoord`). -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  MIPStarRE.LDT.axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

/-- Sampled point answers in the `j`-restricted diagonal test.
Point player receives `u` and answers at `u`. -/
noncomputable def restrictedDiagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  MIPStarRE.LDT.diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point (parameter `zeroCoord`). -/
noncomputable def restrictedDiagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  MIPStarRE.LDT.diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

/-- Failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Failure surrogate for the diagonal lines test.
Averages over restriction index `j`, then the
`j`-restricted diagonal test. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (restrictedDiagonalPointAnswerFamily strategy j)
        (restrictedDiagonalLineAnswerFamily strategy j)

/-- Goodness data for a restricted strategy. -/
structure IsGood {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι)
    (eps delta gamma : Error) : Prop where
  /-- The restricted axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest :
    strategy.axisParallelFailureProbability ≤ eps
  /-- The restricted self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest :
    strategy.selfConsistencyFailureProbability ≤ delta
  /-- The restricted diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest :
    strategy.diagonalFailureProbability ≤ gamma

end RestrictedSymStrat

/-- Equivalence between slice and ambient axis-line polynomials at a fixed height `x`:
`liftAxisAnswer` sends a slice polynomial to its ambient lift, with
`AxisLinePolynomial.restrictAtHeight` as inverse. -/
def axisLinePolynomialEquiv (params : Parameters) [FieldModel params.q] (x : Fq params) :
    AxisLinePolynomial params ≃ AxisLinePolynomial params.next where
  toFun := liftAxisAnswer params x
  invFun := fun f => AxisLinePolynomial.restrictAtHeight params f x
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- Restrict an axis-parallel line measurement to the slice at height `x`. -/
noncomputable def restrictAxisParallelMeasurement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι :=
  fun ℓ =>
    let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
    let restrictedTotal : MIPStarRE.Quantum.Op ι :=
      ∑ f : AxisLinePolynomial params,
        lifted.toSubMeas.outcome (liftAxisAnswer params x f)
    have hrestrictedTotal :
        restrictedTotal = 1 := by
      calc
        restrictedTotal
          = ∑ g : AxisLinePolynomial params.next, lifted.toSubMeas.outcome g := by
              simpa [restrictedTotal] using
                (Fintype.sum_equiv (axisLinePolynomialEquiv params x)
                  (fun f => lifted.toSubMeas.outcome (liftAxisAnswer params x f))
                  (fun g => lifted.toSubMeas.outcome g)
                  (by intro f; rfl))
        _ = 1 := by
            rw [lifted.toSubMeas.sum_eq_total, lifted.total_eq_one]
    { toMeasurement := {
        toSubMeas := {
          outcome := fun f =>
            lifted.toSubMeas.outcome (liftAxisAnswer params x f)
          total := 1
          outcome_pos := fun f => lifted.outcome_pos (liftAxisAnswer params x f)
          sum_eq_total := hrestrictedTotal
          total_le_one := le_rfl
        }
        total_eq_one := rfl }
      proj := fun f => lifted.proj (liftAxisAnswer params x f) }

private theorem restrictAxisParallelMeasurement_transportInvariant
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    MIPStarRE.LDT.AxisParallelMeasurementTransportInvariant params
      (restrictAxisParallelMeasurement params strategy x) := by
  intro ℓ t
  have htransport :=
    MIPStarRE.LDT.AxisParallelCovariantMeasurement.transportInvariant
      strategy.axisParallelMeasurement
      (AxisParallelLine.appendAtHeight params ℓ x) t
  apply ProjMeas.ext
  intro a
  calc
    (restrictAxisParallelMeasurement params strategy x
        (AxisParallelLine.rebaseAt ℓ t)).outcome a
      = (strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params (AxisParallelLine.rebaseAt ℓ t) x)).outcome
          (liftAxisAnswer params x a) := by
            rfl
    _ = (strategy.axisParallelMeasurement
          (AxisParallelLine.rebaseAt (AxisParallelLine.appendAtHeight params ℓ x) t)).outcome
          (liftAxisAnswer params x a) := by
            simp
    _ = (AxisParallelLine.transportMeasurement (params := params.next)
          (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)) t).outcome
          (liftAxisAnswer params x a) := by
            simp [htransport]
    _ = (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).outcome
          (((AxisLinePolynomial.reparamAtEquiv (params := params.next) t).symm)
            (liftAxisAnswer params x a)) := by
            simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
              Measurement.transport, SubMeas.transport]
    _ = (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).outcome
          (liftAxisAnswer params x
            (((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm) a)) := by
            simp [liftAxisAnswer]
    _ = (restrictAxisParallelMeasurement params strategy x ℓ).outcome
          (((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm) a) := by
            rfl
    _ = (AxisParallelLine.transportMeasurement (params := params)
          (restrictAxisParallelMeasurement params strategy x ℓ) t).outcome a := by
            simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
              Measurement.transport, SubMeas.transport]

/-- Canonical honest slice answer with prescribed value at the base point.

We use the constant polynomial because the restricted diagonal branch only reads
line answers at `zeroCoord`. -/
noncomputable def diagonalValueRepresentative (params : Parameters)
    [FieldModel params.q] (a : Fq params) :
    DiagonalLinePolynomial params where
  poly := _root_.Polynomial.C (decodeScalar a)
  degreeBounded := (_root_.Polynomial.natDegree_C (decodeScalar a)).trans_le (Nat.zero_le _)

/-- Restrict a diagonal-line measurement to the slice at height `x`.

This is not literally the paper's outcome reindexing
`f ↦ DiagonalLinePolynomial.appendAtHeight params f x`; that map only covers the
degree-`params.m * params.d` ambient outcomes. Instead we preserve the only
statistic used by the restricted diagonal test formalized here, namely the
base-point answer at `zeroCoord`.

Concretely we:
1. restrict the ambient line question to the slice-preserving line,
2. postprocess the ambient projective measurement to its `zeroCoord` value in
   `F_q`, and
3. re-embed that `F_q`-valued projective measurement into the honest slice
   answer space via `diagonalValueRepresentative`.

This produces a complete projective measurement on
`DiagonalLinePolynomial params` whose induced base-point answer distribution is
exactly the same as the ambient slice-preserving diagonal measurement. -/
noncomputable def restrictDiagonalMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι :=
  fun ℓ =>
    ProjMeas.postprocess
      (ProjMeas.postprocess
        (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord))
      (diagonalValueRepresentative params)

/-- Restrict a diagonal-line measurement to the slice at height `x`, using the
paper-level function-answer alphabet.

Unlike `restrictDiagonalMeasurement`, this keeps the whole line answer function
rather than only the value at `zeroCoord`.  The map is total because
`DiagonalLineAnswer` has no degree-bound subtype proof to preserve. -/
noncomputable def restrictDiagonalAnswerMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι :=
  fun ℓ =>
    ProjMeas.postprocess
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
      (fun f : DiagonalLinePolynomial params.next =>
        DiagonalLineAnswer.restrictAtHeight params f.toAnswer x)

/-- Transport covariance for the function-valued restricted diagonal-line
measurement. -/
private theorem restrictDiagonalAnswerMeasurement_transportInvariant (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    DiagonalAnswerMeasurementTransportInvariant params
      (restrictDiagonalAnswerMeasurement params strategy x) := by
  intro ℓ t
  apply ProjMeas.ext
  intro a
  have htransport :=
    MIPStarRE.LDT.DiagonalCovariantMeasurement.transportInvariant
      strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x) t
  let A := (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas
  let ePoly := DiagonalLinePolynomial.reparamAtEquiv (params := params.next) t
  let eAns := DiagonalLineAnswer.reparamAtEquiv (params := params) t
  let f : DiagonalLinePolynomial params.next → DiagonalLineAnswer params :=
    fun g => DiagonalLineAnswer.restrictAtHeight params g.toAnswer x
  have hcomm : ∀ g, f (ePoly g) = eAns (f g) := by
    intro g
    funext s
    dsimp [f, ePoly, eAns, DiagonalLinePolynomial.reparamAtEquiv,
      DiagonalLineAnswer.reparamAtEquiv, DiagonalLinePolynomial.toAnswer,
      DiagonalLineAnswer.restrictAtHeight, DiagonalLineAnswer.reparamAt]
    exact DiagonalLinePolynomial.reparamAt_apply g t s
  have hpost : postprocess (SubMeas.transport ePoly A) f =
      SubMeas.transport eAns (postprocess A f) :=
    SubMeas.postprocess_transport_equiv ePoly eAns A f f hcomm
  exact congrArg (fun M : SubMeas (DiagonalLineAnswer params) ι => M.outcome a) <| by
    simpa [restrictDiagonalAnswerMeasurement, DiagonalLine.transportMeasurement,
      ProjMeas.transport, Measurement.transport, A, ePoly, eAns, f,
      DiagonalLine.appendAtHeight_rebaseAt, htransport] using hpost

/-- The `x`-restricted strategy with function-valued diagonal-line
answers.

This matches the slice-restriction interface in `inductive_step.tex`, lines
436--455. It is
kept parallel to the current `xRestrictedStrategy`, whose diagonal field uses the
legacy degree-bounded answer alphabet and therefore only preserves the sampled
base-point readout. -/
noncomputable def xRestrictedAnswerSymStrat (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) : AnswerSymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    { toIdxProjMeas := restrictAxisParallelMeasurement params strategy x
      transportInvariant := by
        exact restrictAxisParallelMeasurement_transportInvariant params strategy x }
  diagonalMeasurement :=
    { toIdxProjMeas := restrictDiagonalAnswerMeasurement params strategy x
      transportInvariant := by
        exact restrictDiagonalAnswerMeasurement_transportInvariant params strategy x }

/-- The function-answer restricted strategy reuses the ambient bipartite state. -/
@[simp] theorem xRestrictedAnswerSymStrat_state (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).state = strategy.state :=
  rfl

/-- The function-answer restricted strategy reindexes point questions by appending
the slice height. -/
@[simp] theorem xRestrictedAnswerSymStrat_pointMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) (u : Point params) :
    (xRestrictedAnswerSymStrat params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- The function-answer restricted strategy reuses the parent normalization witness. -/
@[simp] theorem xRestrictedAnswerSymStrat_isNormalized (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).isNormalized = strategy.isNormalized :=
  rfl

/-- The function-answer restricted diagonal measurement is the answer-valued
restriction of the ambient diagonal measurement. -/
@[simp] theorem xRestrictedAnswerSymStrat_diagonalMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) (ℓ : DiagonalLine params) :
    (xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement ℓ =
      restrictDiagonalAnswerMeasurement params strategy x ℓ :=
  rfl

/-- Evaluating the answer-valued restricted diagonal measurement at the base point
recovers the ambient slice-preserving diagonal readout. -/
@[simp] theorem restrictDiagonalAnswerMeasurement_postprocess_zero (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord) := by
  simp [restrictDiagonalAnswerMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp, DiagonalLinePolynomial.toAnswer,
    DiagonalLineAnswer.restrictAtHeight]
  rfl

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
noncomputable def xRestrictedStrategy (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) : RestrictedSymStrat params ι where
  state := strategy.state
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    { toIdxProjMeas := restrictAxisParallelMeasurement params strategy x
      transportInvariant := by
        exact restrictAxisParallelMeasurement_transportInvariant params strategy x }
  diagonalMeasurement := restrictDiagonalMeasurement params strategy x

/-- Restricting a strategy does not change its bipartite state. -/
@[simp] theorem xRestrictedStrategy_state (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedStrategy params strategy x).state = strategy.state :=
  rfl

/-- Restricting a strategy reuses the parent strategy's normalization witness. -/
@[simp] theorem xRestrictedStrategy_isNormalized (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedStrategy params strategy x).isNormalized = strategy.isNormalized :=
  rfl

/-- Restricting a strategy reindexes point questions by appending the slice height. -/
@[simp] theorem xRestrictedStrategy_pointMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) (u : Point params) :
    (xRestrictedStrategy params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Restricting an axis-parallel measurement reindexes outcomes by slice extension. -/
@[simp] theorem restrictAxisParallelMeasurement_outcome (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas.outcome f =
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas.outcome
        (liftAxisAnswer params x f) :=
  rfl

/-- Postprocessing the restricted diagonal measurement at the base point recovers
exactly the ambient slice-preserving diagonal answer distribution at the base
point. -/
@[simp] theorem restrictDiagonalMeasurement_postprocess_zero (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord) := by
  classical
  let evalNext : DiagonalLinePolynomial params.next → Fq params := fun f => f zeroCoord
  let evalSlice : DiagonalLinePolynomial params → Fq params := fun f => f zeroCoord
  simp only [restrictDiagonalMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp]
  simp [diagonalValueRepresentative, DiagonalLinePolynomial.toFun, evalLinePolynomialModel]

/-- The intermediate `ν` from `thm:main-induction`. -/
noncomputable def mainInductionNu (params : Parameters) (k : ℕ)
    (eps delta gamma : Error) : Error :=
  1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
    (Real.rpow eps (1 / (1024 : Error)) +
      Real.rpow delta (1 / (1024 : Error)) +
      Real.rpow gamma (1 / (1024 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)))

/-- The explicit `σ` of `thm:main-induction`. -/
noncomputable def mainInductionError (params : Parameters) (k : ℕ)
    (eps delta gamma : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (mainInductionNu params k eps delta gamma +
      Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- The section-local self-improvement error. -/
noncomputable def selfImprovementInInductionError (params : Parameters)
    (eps delta _gamma : Error) : Error :=
  3000 * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The intermediate `ν` from the section-local pasting theorem. -/
noncomputable def ldPastingInInductionNu (params : Parameters) (k : ℕ)
    (eps delta gamma zeta : Error) : Error :=
  100 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The section-local pasting consistency error. -/
noncomputable def ldPastingInInductionError (params : Parameters) (k : ℕ)
    (eps delta gamma kappa zeta : Error) : Error :=
  kappa * (1 + 1 / (100 * (params.m : Error))) +
    2 * ldPastingInInductionNu params k eps delta gamma zeta +
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- Tensor-failure expectation on a bipartite space.

Computes `⟨ψ| (Z ⊗ I)(I ⊗ (I - Σ H_a)) |ψ⟩` where `Z` acts on the left register
and `H` acts on the right register. -/
noncomputable def tensorFailureExpectation {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (Z : MIPStarRE.Quantum.Op ιA) (H : SubMeas Outcome ιB) :
    Error :=
  ev ψ <|
    leftTensor (ι₂ := ιB) Z *
      rightTensor (ι₁ := ιA) (1 - H.total)

/-- Probability that a sampled test line in `F_q^{m+1}` is not parallel to the new axis. -/
noncomputable def sliceTransverseDirectionWeight (params : Parameters) : Error :=
  (params.m : Error) / (((params.m + 1 : ℕ) : Error))

/-- Reciprocal loss incurred when conditioning away the new axis direction.

In `lem:restricted-probabilities`, the axis-parallel and diagonal branches use
this same conditioning step, so both averaged slice bounds carry the paper's
common factor `((m + 1) / m)`. -/
noncomputable def sliceConditioningLoss (params : Parameters) : Error :=
  (((params.m + 1 : ℕ) : Error) / (params.m : Error))

end MIPStarRE.LDT.MainInductionStep

end

end LIDT


