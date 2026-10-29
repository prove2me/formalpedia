-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
-- name    : LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:46:13.487413+00:00
-- url     : https://prove2.me/theorems/0a2cc57f-c8b6-49bc-bd07-e2311ad5f6bb
-- title:
--   LIDT definitions: LDT / Commutativity / Scaffold / Core
-- statement:
--   This bundle records the error envelopes and proposition-shaped interfaces for polynomial commutativity. It links evaluated-slice and full-slice operator families by state-dependent operator distance and packages the Hermitian-square normalization condition.
--
--   Principal definitions:
--   - `commDataProcessedGError`: The processed evaluated-slice error $48m(\sqrt\gamma+\sqrt\zeta)$.
--   - `comMainError`: The full commutativity error $30m(\gamma^{1/4}+\zeta^{1/4}+(d/q)^{1/4})$.
--   - `CommDataProcessedGConclusion`: The SDD operator relation for the processed evaluated-slice products.
--   - `ComMainConclusion`: The SDD operator relation for the full-slice products.
--   - `NormalizationConditionStatement`: Equality of the two square operators together with their upper bound by the identity.
--   - `normalizationConditionAdjointSquareOperator` and `normalizationConditionSquareOperator`: The two Hermitian-square operators in that normalization statement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Scaffold/Core.lean#L28-L90

-- Generated from MIPStarRE/LDT/Commutativity/Scaffold/Core.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
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
# Section 11 commutativity: core operator estimates

Core operator-ordering notation and elementary comparison lemmas shared across
the Section 11 commutativity argument.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Displayed error term for `lem:comm-data-processed-g`. -/
noncomputable def commDataProcessedGError (params : Parameters) (gamma zeta : Error) : Error :=
  48 * (params.m : Error) *
    (Real.rpow gamma (1 / (2 : Error)) + Real.rpow zeta (1 / (2 : Error)))

/-- Displayed error term for `thm:com-main`. -/
noncomputable def comMainError (params : Parameters) (gamma zeta : Error) : Error :=
  30 * (params.m : Error) *
    (Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)))

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:16-47`
(`\label{lem:comm-data-processed-g}`).

Displayed conclusion of the commutativity-of-`G`-after-evaluation lemma.  The
strategy state is bipartite.  Alice-side measurements are lifted to the left
tensor factor, while Bob-side postprocessed point measurements are lifted to the
right tensor factor. -/
abbrev CommDataProcessedGConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop :=
  SDDOpRel strategy.state
    (uniformDistribution (EvaluatedSliceQuestion params))
    (evaluatedSliceProductLeft params strategy family)
    (evaluatedSliceProductRight params strategy family)
    (commDataProcessedGError params gamma zeta)

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:228-257`
(`\label{thm:com-main}`).

Displayed conclusion of the commutativity-of-`G` theorem. -/
abbrev ComMainConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) : Prop :=
  SDDOpRel strategy.state
    (uniformDistribution (FullSliceQuestion params))
    (fullSliceProductLeft params strategy family)
    (fullSliceProductRight params strategy family)
    (comMainError params gamma zeta)

/-- Paper origin: `references/ldt-paper/commutativity-G.tex:309-338`
(`\label{lem:normalization-condition}`); records the Hermitian-square /
identity-bound expansion used inside the proof of the commutativity theorem
`\label{thm:com-main}` (`references/ldt-paper/commutativity-G.tex:228-378`).

Conclusion statement for `lem:normalization-condition`. -/
structure NormalizationConditionStatement {OutcomeA OutcomeB : Type*}
    [Fintype OutcomeA] [Fintype OutcomeB]
    (P : SubMeas OutcomeA ι)
    (Q : ProjSubMeas OutcomeB ι) : Prop where
  /-- The two square operators formed from `∑_b Q_b P_a Q_b` agree. -/
  sandwichedHermitianSquare :
    normalizationConditionAdjointSquareOperator P Q =
      normalizationConditionSquareOperator P Q
  /-- The square operator formed from the sandwiched family is bounded by the
  identity operator. -/
  sandwichedBoundedByIdentity :
    normalizationConditionSquareOperator P Q ≤ normalizationConditionIdentityBound P Q


end MIPStarRE.LDT.Commutativity

end

end LIDT


