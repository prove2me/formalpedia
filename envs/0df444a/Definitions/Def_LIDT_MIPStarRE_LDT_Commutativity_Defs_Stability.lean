-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
-- name    : LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:40:53.059696+00:00
-- url     : https://prove2.me/theorems/c32798e6-af42-4589-830a-bc494364872f
-- title:
--   LIDT definitions: LDT / Commutativity / Defs / Stability
-- statement:
--   This bundle defines the two postprocessed products used in the stability version of the commutativity argument. One evaluates the ordered full-slice product at sampled points, while the other evaluates the reversed product in the corresponding right-register arrangement.
--
--   Principal definitions:
--   - `evaluatedFromFullSliceProductLeft`: evaluates the ordered full-slice product at sampled points.
--   - `evaluatedFromFullSliceProductRight`: evaluates the reversed full-slice product at sampled points.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Defs/Stability.lean#L45-L63

-- Generated from MIPStarRE/LDT/Commutativity/Defs/Stability.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
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

/-!
# Section 11 commutativity: stability definitions

Reindexing and postprocessing infrastructure used in the full-slice and
stability reductions, including the weighted reindex of raw operator families.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]


/-- Postprocess the full-slice ordered product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)


















end MIPStarRE.LDT.Commutativity

end

end LIDT


