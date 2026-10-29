-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_SelfImprovement
-- name    : LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_SelfImprovement
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:45:11.764713+00:00
-- url     : https://prove2.me/theorems/5fbe6e0d-7293-476a-af13-dc9081526cf4
-- title:
--   LIDT definitions: LDT / MainInductionStep / Theorems / InductionParameterBounds / SelfImprovement
-- statement:
--   This bundle derives unit-interval consequences from a self-improvement error bounded by one. The estimates control the axis and self-consistency components used by the induction step.
--
--   Principal definitions:
--   - `eps_le_one_of_selfImprovementInInductionError_le_one`: bounds the axis-parallel error by one.
--   - `delta_le_one_of_selfImprovementInInductionError_le_one`: bounds the self-consistency error by one.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/SelfImprovement.lean#L28-L133

-- Generated from MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/SelfImprovement.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_Preliminaries
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
# Section 6 — Self-Improvement Error Bounds

This file is one leaf of `InductionParameterBounds`. It contains the scalar
consequences of the non-vacuous hypothesis
`selfImprovementInInductionError ≤ 1`, namely the bounds `eps ≤ 1` and
`delta ≤ 1` used before applying self-improvement inside the induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
    (params : Parameters) {eps delta gamma x : Error}
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1)
    (hscaled_le :
      3000 * (params.next.m : Error) * Real.rpow x (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma) :
    x ≤ 1 := by
  have hcoef_ge_one : (1 : Error) ≤ 3000 * (params.next.m : Error) := by
    have hm_one : (1 : Error) ≤ (params.next.m : Error) := by
      exact_mod_cast params.next.hm
    nlinarith
  have hroot_le_one : Real.rpow x (1 / (32 : Error)) ≤ 1 := by
    by_contra hroot
    have hroot_gt : 1 < Real.rpow x (1 / (32 : Error)) := lt_of_not_ge hroot
    have : 1 < 3000 * (params.next.m : Error) * Real.rpow x (1 / (32 : Error)) := by
      nlinarith [hcoef_ge_one]
    linarith [hscaled_le, hzeta_le]
  exact le_one_of_rpow_le_one (by positivity) hroot_le_one

private lemma selfImprovementInInduction_scaled_component_le
    (params : Parameters) {x y z : Error}
    (hrest_nonneg : 0 ≤ y + z) :
    3000 * (params.next.m : Error) * x ≤
      3000 * (params.next.m : Error) * (x + y + z) := by
  have hsummono : x ≤ x + y + z := by
    nlinarith [hrest_nonneg]
  have hcoef_nonneg : 0 ≤ 3000 * (params.next.m : Error) := by
    positivity
  exact mul_le_mul_of_nonneg_left hsummono hcoef_nonneg

/-- Internal helper: under `selfImprovementInInductionError ≤ 1`, the axis-parallel error `eps ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma eps_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    eps ≤ 1 := by
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow delta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    have hdelta_root_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
      Real.rpow_nonneg hdelta_nonneg (1 / (32 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
    nlinarith
  have heps_scaled_le :
      3000 * (params.next.m : Error) * Real.rpow eps (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma := by
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm] using
      (selfImprovementInInduction_scaled_component_le (params := params)
        (x := Real.rpow eps (1 / (32 : Error)))
        (y := Real.rpow delta (1 / (32 : Error)))
        (z := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
        hrest_nonneg)
  exact
    le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
      params hzeta_le heps_scaled_le

/-- Internal helper: under `selfImprovementInInductionError ≤ 1`,
the self-consistency error `delta ≤ 1`.

Exposed for cross-module use in `AvgSliceErrors` and `PastingAssembly`. -/
lemma delta_le_one_of_selfImprovementInInductionError_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    {eps delta gamma : Error}
    (hgood : strategy.IsGood eps delta gamma)
    (hzeta_le : selfImprovementInInductionError params.next eps delta gamma ≤ 1) :
    delta ≤ 1 := by
  have hdelta_nonneg := delta_nonneg_of_isGood params.next strategy hgood
  have heps_nonneg := eps_nonneg_of_isGood params.next strategy hgood
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hrest_nonneg :
      0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
    have heps_root_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
      Real.rpow_nonneg heps_nonneg (1 / (32 : Error))
    have hratio_root_nonneg :
        0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) :=
      Real.rpow_nonneg hratio_nonneg (1 / (32 : Error))
    nlinarith
  have hdelta_scaled_le :
      3000 * (params.next.m : Error) * Real.rpow delta (1 / (32 : Error)) ≤
        selfImprovementInInductionError params.next eps delta gamma := by
    simpa [selfImprovementInInductionError, Parameters.next, mul_assoc, mul_left_comm,
        mul_comm, add_assoc, add_left_comm, add_comm] using
      (selfImprovementInInduction_scaled_component_le (params := params)
        (x := Real.rpow delta (1 / (32 : Error)))
        (y := Real.rpow eps (1 / (32 : Error)))
        (z := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))
        hrest_nonneg)
  exact
    le_one_of_selfImprovementInInductionError_le_one_of_scaled_bound
      params hzeta_le hdelta_scaled_le

end MIPStarRE.LDT.MainInductionStep

end

end LIDT


