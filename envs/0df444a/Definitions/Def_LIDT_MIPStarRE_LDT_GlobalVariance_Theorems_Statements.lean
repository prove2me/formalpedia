-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:46:59.385059+00:00
-- url     : https://prove2.me/theorems/c2b971f9-8b25-4b90-974b-21766dd9b967
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / Statements
-- statement:
--   This bundle packages the proposition-shaped conclusions used by the global-variance argument. Each structure stores the family comparisons and deviation bounds needed by its stage.
--
--   Principal definitions:
--   - `GeneralizeBStatement`: the generalize-B comparison package.
--   - `LocalVarianceOfPointsStatement`: the local-variance comparison package.
--   - `GlobalVarianceOfPointsStatement`: the global-variance and local-to-global package.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/Statements.lean#L18-L104

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/Statements.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
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

namespace LIDT

/-! ## Statement structures -/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

/-- Paper origin: `references/ldt-paper/expansion.tex:273-291`
(`\label{lem:generalize-b}`).

Conclusion statement for `lem:generalize-b`.
`ψbi` is the bipartite state on `d * d` (passed as `strategy.state`
by callers). -/
structure GeneralizeBStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Prop where
  /-- The aggregated left and right `generalize-b` families are close in `SDDRel`. -/
  aggregateFamilyComparison :
    SDDRel ψbi
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)
  /-- Each fixed polynomial satisfies the claimed deviation bound. -/
  pointwiseNormBound :
    ∀ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params
  /-- The polynomial average of the deviations satisfies the same bound. -/
  averagedNormBound :
    generalizeBDeviation params strategy ψbi G ≤ generalizeBError params

/-- Paper origin: `references/ldt-paper/expansion.tex:292-324`
(`\label{lem:local-variance-of-points}`).

Conclusion statement for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  /-- The aggregated edge families are close in `SDDRel`. -/
  aggregateEdgeComparison :
    SDDRel ψbi
      (rerandomizeCoord params)
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)
  /-- Each fixed polynomial satisfies the edgewise squared-difference bound. -/
  pointwiseEdgeNormBound :
    ∀ g : Polynomial params,
      localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        localVarianceOfPointsError params eps delta
  /-- Each fixed polynomial satisfies the local-variance bound. -/
  pointwiseLocalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
        localVarianceOfPointsError params eps delta
  /-- The polynomial average of the local variances satisfies the same bound. -/
  averagedLocalVarianceBound :
    pointConditionedLocalVariance params strategy G ≤
      localVarianceOfPointsError params eps delta

/-- Paper origin: `references/ldt-paper/expansion.tex:325-353`
(`\label{lem:global-variance-of-points}`).

Conclusion statement for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) (eps delta : Error) : Prop where
  /-- The aggregated global families are close in `SDDRel`. -/
  aggregateGlobalComparison :
    SDDRel ψbi
      (independentPointPair params)
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)
  /-- Each fixed polynomial satisfies the global squared-difference bound. -/
  pointwiseGlobalNormBound :
    ∀ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy ψbi G g ≤
        globalVarianceOfPointsError params eps delta
  /-- Each fixed polynomial satisfies the local-to-global transfer estimate. -/
  pointwiseExpansionTransfer :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        (params.m : Error) *
          pointConditionedLocalVarianceAtPolynomial params strategy G g
  /-- Each fixed polynomial satisfies the claimed global-variance bound. -/
  pointwiseGlobalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        globalVarianceOfPointsError params eps delta
  /-- The polynomial average of the global variances satisfies the same bound. -/
  averagedGlobalVarianceBound :
    pointConditionedGlobalVariance params strategy G ≤
      globalVarianceOfPointsError params eps delta

end

end MIPStarRE.LDT.GlobalVariance

end LIDT


