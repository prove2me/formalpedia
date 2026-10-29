-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_Completion
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:42:40.593878+00:00
-- url     : https://prove2.me/theorems/957c8a36-c978-4a17-a81a-c890b1096257
-- title:
--   LIDT definitions: LDT / Preliminaries / Completion
-- statement:
--   This bundle defines completion of a projective submeasurement at a distinguished outcome. It preserves projectivity and supplies conversions of the completed object to a complete measurement and to an ordinary submeasurement.
--
--   Principal definitions:
--   - `completeAtOutcomeProj`: completes a projective submeasurement while preserving projectivity.
--   - `completeAtOutcomeProj_toMeasurement`: views the completed projective object as a measurement.
--   - `completeAtOutcomeProj_toSubMeas`: views it as an ordinary submeasurement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/Completion.lean#L21-L71

-- Generated from MIPStarRE/LDT/Preliminaries/Completion.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
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

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Preliminary completion lemmas

Structural completion helpers that stay close to `completeAtOutcome` while
keeping only the light projectivity dependencies from
`SwitchSandwichPrep/Core.lean`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Completing a projective submeasurement at a distinguished outcome preserves
projectivity. The residual effect `1 - P.total` is a projection orthogonal to
`P.outcome a0`, so the completed effect remains idempotent. -/
noncomputable def completeAtOutcomeProj {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas Outcome ι) (a0 : Outcome) : ProjMeas Outcome ι := by
  classical
  refine
    { toMeasurement := completeAtOutcome P.toSubMeas a0
      proj := ?_ }
  intro a
  by_cases ha : a = a0
  · subst a
    let T : MIPStarRE.Quantum.Op ι := P.total
    let Pa : MIPStarRE.Quantum.Op ι := P.outcome a0
    let R : MIPStarRE.Quantum.Op ι := 1 - T
    have hTT : T * T = T := by
      simpa [T] using projSubMeas_total_proj P
    have hPaT : Pa * T = Pa := by
      simpa [Pa, T] using projSubMeas_outcome_mul_total_eq_outcome P a0
    have hPa_star : IsStarProjection Pa :=
      isStarProjection_iff'.2 ⟨by simpa [Pa] using P.proj a0,
        (Matrix.nonneg_iff_posSemidef.mp (P.outcome_pos a0)).isHermitian.eq⟩
    have hT_star : IsStarProjection T :=
      isStarProjection_iff'.2 ⟨hTT,
        (Matrix.nonneg_iff_posSemidef.mp P.total_nonneg).isHermitian.eq⟩
    have hR_star : IsStarProjection R := by
      simpa [R] using hT_star.one_sub
    have hPaR : Pa * R = 0 := by
      calc
        Pa * R = Pa * (1 - T) := by rfl
        _ = Pa - Pa * T := by rw [mul_sub, mul_one]
        _ = 0 := by simp [hPaT]
    have hproj :
        (P.outcome a0 + (1 - P.total)) * (P.outcome a0 + (1 - P.total)) =
          P.outcome a0 + (1 - P.total) := by
      simpa [Pa, R] using (hPa_star.add hR_star hPaR).isIdempotentElem.eq
    simpa [completeAtOutcome] using hproj
  · simpa [completeAtOutcome, ha] using P.proj a

@[simp] theorem completeAtOutcomeProj_toMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas Outcome ι) (a0 : Outcome) :
    (completeAtOutcomeProj P a0).toMeasurement = completeAtOutcome P.toSubMeas a0 :=
  rfl

@[simp] theorem completeAtOutcomeProj_toSubMeas {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas Outcome ι) (a0 : Outcome) :
    (completeAtOutcomeProj P a0).toSubMeas = (completeAtOutcome P.toSubMeas a0).toSubMeas :=
  rfl

end MIPStarRE.LDT.Preliminaries

end

end LIDT


