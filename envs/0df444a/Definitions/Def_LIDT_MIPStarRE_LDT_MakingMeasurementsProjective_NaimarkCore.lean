-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:56:36.352203+00:00
-- url     : https://prove2.me/theorems/bb87d574-2836-45ce-b717-084b3f102894
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / NaimarkCore
-- statement:
--   This bundle defines the matrix ingredients of a one-measurement Naimark dilation. It represents the missing mass, auxiliary transition, partial-isometry column, input projector, and outcome projectors that embed a submeasurement into a projective measurement.
--
--   Principal definitions:
--   - `oneMeasNaimarkRemainder`: the identity minus the total submeasurement operator.
--   - `oneMeasNaimarkAuxTransition`: the auxiliary matrix unit for the dilation.
--   - `oneMeasNaimarkColumn`: the partial-isometry column implementing the dilation map.
--   - `oneMeasNaimarkInputProj`: the projector onto the auxiliary input-none sector.
--   - `oneMeasNaimarkOutcomeProj`: the projector for a specified outcome sector.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkCore.lean#L131-L162

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkCore.lean by skeleton subtraction.
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

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Naimark core

Core projector and compression lemmas for the one-measurement Naimark
dilation construction.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-! ### One-measurement Naimark (Lemma 5.2) -/











/-- The slack operator `I - ∑_a M_a` for one-measurement Naimark dilation. -/
noncomputable def oneMeasNaimarkRemainder {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) : MIPStarRE.Quantum.Op d :=
  1 - ∑ a, M.effect a

/-- The auxiliary matrix unit used in the one-measurement Naimark construction. -/
def oneMeasNaimarkAuxTransition {α : Type*} [DecidableEq α] (oa ob : Option α) :
    MIPStarRE.Quantum.Op (Option α) :=
  Matrix.single oa ob 1

/-- The partial-isometry column implementing the one-measurement Naimark map. -/
noncomputable def oneMeasNaimarkColumn {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : MIPStarRE.Quantum.Submeasurement α d) :
    MIPStarRE.Quantum.Op (d × Option α) := fun x y =>
  match x.2, y.2 with
  | some a, none => CFC.sqrt (M.effect a) x.1 y.1
  | none, none => CFC.sqrt (oneMeasNaimarkRemainder M) x.1 y.1
  | _, _ => 0

/-- The projector onto the input `none` slice of the auxiliary register. -/
def oneMeasNaimarkInputProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] :
    MIPStarRE.Quantum.Op (d × Option α) :=
  Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (oneMeasNaimarkAuxTransition none none)

/-- The auxiliary-basis projector for a given Naimark outcome slice. -/
def oneMeasNaimarkOutcomeProj {α : Type*} [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d] (oa : Option α) :
    MIPStarRE.Quantum.Op (d × Option α) :=
  Matrix.kronecker (1 : MIPStarRE.Quantum.Op d) (oneMeasNaimarkAuxTransition oa oa)












end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


