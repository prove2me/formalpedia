-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkOneMeas
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkOneMeas
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:57:26.77999+00:00
-- url     : https://prove2.me/theorems/a9696ac5-5ff3-44dd-b039-d1486672146a
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / NaimarkOneMeas
-- statement:
--   This bundle turns one-measurement Naimark dilation data into projective submeasurements. It provides both the completed option-indexed dilation and its restriction back to the original outcome type for use in later measurement assembly.
--
--   Principal definitions:
--   - The option-indexed conversion produces the completed projective submeasurement on the enlarged outcome type.
--   - The restricted conversion returns the corresponding projective submeasurement on the original outcomes.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkOneMeas.lean#L477-L510

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/NaimarkOneMeas.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — one-measurement Naimark

Unitary-extension machinery and the one-measurement Naimark lemma.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT
open MIPStarRE.Quantum



-- This is independent of Naimark and could be moved to `LDT/Preliminaries`.






/-! ### Projective submeasurement on the original outcomes -/

/-- The completed one-measurement Naimark dilation as a projective
submeasurement on the `Option α` outcome type.

This is the direct submeasurement interface for the lifted projectors supplied
by `OneMeasNaimarkData`.  The subsequent restriction to the original outcomes
uses `restrictSomeProjSubMeas`. -/
noncomputable def OneMeasNaimarkData.toProjSubMeasOption {α : Type*}
    [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData α d) :
    ProjSubMeas (Option α) (d × Option α) where
  toSubMeas := {
    outcome := data.liftedEffect
    total := ∑ oa, data.liftedEffect oa
    outcome_pos := data.lifted_pos
    sum_eq_total := rfl
    total_le_one := data.lifted_sum_le_one
  }
  proj := fun oa => (data.lifted_isProj oa).isIdempotentElem.eq

/-- Restrict the completed one-measurement Naimark dilation to the original
outcomes.

The one-measurement construction gives a complete projective measurement on
`Option α`; the extra outcome `none` carries the residual mass
`1 - ∑ₐ Mₐ`.  Restricting to the `some a` outcomes gives the projective
submeasurement on the original outcome type used by the tensor-product Naimark
statement. -/
noncomputable def OneMeasNaimarkData.toProjSubMeas {α : Type*}
    [Fintype α] [DecidableEq α]
    {d : Type*} [Fintype d] [DecidableEq d]
    (data : OneMeasNaimarkData α d) :
    ProjSubMeas α (d × Option α) :=
  restrictSomeProjSubMeas data.toProjSubMeasOption


end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


