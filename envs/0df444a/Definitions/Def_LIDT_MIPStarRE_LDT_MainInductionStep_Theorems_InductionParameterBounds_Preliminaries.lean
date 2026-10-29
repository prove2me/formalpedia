-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:43:01.76807+00:00
-- url     : https://prove2.me/theorems/71efc89d-ef08-464d-b187-38962d3fbb86
-- title:
--   LIDT definitions: LDT / MainInductionStep / Theorems / InductionParameterBounds / Preliminaries
-- statement:
--   This bundle contains elementary parameter inequalities used before applying the main induction estimates. The results turn root bounds into unit bounds and control the field-dimension ratio under the induction parameter assumptions.
--
--   Principal definitions:
--   - `le_one_of_rpow_le_one`: a nonnegative base is at most one when its specified real power is at most one under the available exponent conditions.
--   - `dq_ratio_le_one`: the ratio `d / q` is at most one from the parameter inequality `d <= q`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean#L61-L80

-- Generated from MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# Section 6 — Induction Parameter Bound Preliminaries

This file is one leaf of `InductionParameterBounds`. It contains the elementary
point-line reduction for the base case, the real-variable comparison lemmas used
by the small-parameter estimates, and the bound `d/q ≤ 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





lemma le_one_of_rpow_le_one {x c : Error}
    (hc_pos : 0 < c) (h : Real.rpow x c ≤ 1) :
    x ≤ 1 := by
  by_contra hx_gt
  have hx_gt' : 1 < x := lt_of_not_ge hx_gt
  have : 1 < Real.rpow x c := Real.one_lt_rpow hx_gt' hc_pos
  linarith

/-- Internal helper: `d/q ≤ 1` under the assumption `params.d ≤ params.q`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma dq_ratio_le_one
    (params : Parameters)
    (hdq_le_q : params.d ≤ params.q) :
    ((params.d : Error) / (params.q : Error)) ≤ 1 := by
  have hq_pos : (0 : Error) < (params.q : Error) := by
    exact_mod_cast params.hq
  have hdq_real : (params.d : Error) ≤ (params.q : Error) := by
    exact_mod_cast hdq_le_q
  exact (div_le_iff₀ hq_pos).2 (by simpa using hdq_real)



end MIPStarRE.LDT.MainInductionStep

end

end LIDT


