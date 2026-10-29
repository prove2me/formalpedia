-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
-- name    : LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:47:41.588932+00:00
-- url     : https://prove2.me/theorems/a52d17ad-8ee8-468d-8609-ea78f7c6f2e4
-- title:
--   LIDT definitions: LDT / CommutativityPoints / AnswerTheorems
-- statement:
--   This bundle defines the answer-valued point and line operator families used in commutativity-point comparisons. The definitions preserve the ordered and reversed product conventions needed by later estimates.
--
--   Principal definitions:
--   - `answerSampledPointMeasurement`: the point measurement sampled from an answer-valued strategy.
--   - `answerSampledDiagonalLineEvaluation`: the diagonal-line evaluation family.
--   - `answerPointMeasurementProductLeft`: the left ordered point product.
--   - `answerPointMeasurementProductRight`: the reversed point product.
--   - `answerPointMeasurementProductAlongSharedLine`: the shared-line point product.
--   - `answerPointMeasurementProductAlongSharedLineReversed`: its reversed ordering.
--   - `answerPointDiagonalLineMixedProductLeft`: the left mixed point and diagonal-line product.
--   - `answerDiagonalLineProductOrdered`: the ordered diagonal-line product.
--   - `answerDiagonalLineProductReversed`: the reversed diagonal-line product.
--   - `answerPointDiagonalLineMixedProductRight`: the right mixed product.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean#L26-L142

-- Generated from MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
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

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.CommutativityPoints
end MIPStarRE.LDT.CommutativityPoints

/-!
# Section 10 commutativity points: answer-valued diagonal measurements
This file proves the commutativity-at-points theorem using the answer-valued
diagonal-line verifier relation.  The conclusion concerns only the point
measurements, hence it can later be transferred to the ordinary carrier used by
self-improvement, but the proof does not use the carrier's inert diagonal
measurement.
## References
- `references/ldt-paper/commutativity-points.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

/-- The point measurement, reindexed by a sampled diagonal line and a parameter
on it, for an answer-valued strategy. -/
def answerSampledPointMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate an answer-valued diagonal-line measurement at the sampled
parameter. -/
noncomputable def answerSampledDiagonalLineEvaluation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` for an answer-valued
strategy. -/
noncomputable def answerPointMeasurementProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` for an answer-valued
strategy. -/
noncomputable def answerPointMeasurementProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily Au Av

 noncomputable def answerPointMeasurementProductAlongSharedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    answerPointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

 noncomputable def answerPointMeasurementProductAlongSharedLineReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    answerPointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

 noncomputable def answerPointDiagonalLineMixedProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas Au Lv

 noncomputable def answerDiagonalLineProductOrdered
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      reversedProductOpFamily Lu Lv

 noncomputable def answerDiagonalLineProductReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      orderedProductOpFamily Lu Lv

 noncomputable def answerPointDiagonalLineMixedProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    postprocess (tensorProductSubMeas Av Lu) Prod.swap



















end MIPStarRE.LDT.CommutativityPoints

end

end LIDT


