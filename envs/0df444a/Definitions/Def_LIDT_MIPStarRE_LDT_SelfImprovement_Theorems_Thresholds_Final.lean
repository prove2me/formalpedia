-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:06:05.966644+00:00
-- url     : https://prove2.me/theorems/b59f9dc1-72f7-40bd-9c8d-7009a3e44e25
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Thresholds / Final
-- statement:
--   This bundle defines the final self-improvement power sum and expresses the helper, final, orthonormalization, and data-processing errors through it.
--
--   Principal definitions:
--   - `finalStagePowerSum`: the final sum of fractional-power contributions.
--   - `finalStagePowerSum_nonneg`: proves nonnegativity of the power sum.
--   - `finalStagePowerSum_le_of_exponent_ge`: gives its exponent monotonicity bound.
--   - `sqrt_finalStagePowerSum_le`: bounds its square root by a later power sum.
--   - `selfImprovementHelperError_eq_finalStagePowerSum`: identifies the helper error.
--   - `selfImprovementError_eq_finalStagePowerSum`: identifies the final error.
--   - `selfImprovementOrthogonalizationError_eq`: identifies the orthonormalization error.
--   - `selfImprovementDataProcessingError_eq`: identifies the data-processing error.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean#L33-L663

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 9 — final-stage numerical threshold absorptions

This module contains the final-stage arithmetic comparisons which absorb the natural
projective-output error terms into the literal `selfImprovementError` threshold.
The estimates formalize the exponent-monotonicity bookkeeping in
`references/ldt-paper/self_improvement.tex`, lines 803--810, and are used by the
final-field construction theorems in the self-improvement theorem.

The helper-stage estimates, including the square-root bound on the global-variance
error, are in `Thresholds.Helper`.
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective

/-! ## Final-stage threshold: `30 ζ̂ ≤ ζ`

For `ε, δ, d/q ∈ [0, 1]`, the helper-stage error is dominated by
`selfImprovementError / 30`. This is the exponent-monotonicity step in the
paper's chained absorption (`self_improvement.tex`, lines 803--810): for
unit-interval `x` and `0 ≤ z ≤ y`, `x^y ≤ x^z`. -/

/-- The three-term power sum used in the final-stage self-improvement threshold
bookkeeping.

For exponent `p`, this is the Lean counterpart of
`ε^p + δ^p + (d/q)^p`. Keeping this expression named makes the nested
absorptions in `self_improvement.tex`, lines 772--810, insensitive to future
constant adjustments. -/
noncomputable def finalStagePowerSum (params : Parameters)
    (eps delta p : Error) : Error :=
  Real.rpow eps p + Real.rpow delta p +
    Real.rpow ((params.d : Error) / (params.q : Error)) p

/-- The final-stage power sum is nonnegative when its base parameters are
nonnegative.

This is the positivity fact used when multiplying coefficient comparisons by
`ε^p + δ^p + (d/q)^p`. -/
theorem finalStagePowerSum_nonneg
    (params : Parameters) (eps delta p : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    0 ≤ finalStagePowerSum params eps delta p := by
  unfold finalStagePowerSum
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _))
    (Real.rpow_nonneg hdq_nonneg _)

/-- Exponent monotonicity for the final-stage power sum on the unit interval.

If `ε`, `δ`, and `d/q` all lie in `[0, 1]`, then increasing the exponent
decreases each term of the power sum. This is the formal arithmetic step behind
the final threshold comparison in `self_improvement.tex`, lines 803--810. -/
theorem finalStagePowerSum_le_of_exponent_ge
    (params : Parameters) (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1)
    {pLarge pSmall : Error} (hpSmall_nonneg : 0 ≤ pSmall)
    (hpSmall_le_pLarge : pSmall ≤ pLarge) :
    finalStagePowerSum params eps delta pLarge ≤
      finalStagePowerSum params eps delta pSmall := by
  unfold finalStagePowerSum
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact Real.rpow_le_rpow_of_exponent_ge' heps heps_le_one hpSmall_nonneg
      hpSmall_le_pLarge
  · exact Real.rpow_le_rpow_of_exponent_ge' hdelta hdelta_le_one hpSmall_nonneg
      hpSmall_le_pLarge
  · exact Real.rpow_le_rpow_of_exponent_ge' hdq_nonneg hdq_le_one hpSmall_nonneg
      hpSmall_le_pLarge

private theorem sqrt_rpow_eq_rpow_half {x p : Error} (hx : 0 ≤ x) :
    Real.sqrt (Real.rpow x p) = Real.rpow x (p / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow x p) (1 / (2 : Error)) = Real.rpow x (p * (1 / 2)) := by
      exact (Real.rpow_mul hx p (1 / (2 : Error))).symm
    _ = Real.rpow x (p / 2) := by ring_nf

/-- The square root of a final-stage power sum is bounded by the power sum with
half the exponent.

The proof is the elementary estimate
`sqrt (x + y + z) ≤ sqrt x + sqrt y + sqrt z`, applied to the three powers
`ε^p`, `δ^p`, and `(d/q)^p`. -/
theorem sqrt_finalStagePowerSum_le
    (params : Parameters) (eps delta p : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (finalStagePowerSum params eps delta p) ≤
      finalStagePowerSum params eps delta (p / 2) := by
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  unfold finalStagePowerSum
  calc
    Real.sqrt (Real.rpow eps p + Real.rpow delta p +
        Real.rpow ((params.d : Error) / (params.q : Error)) p)
        ≤ Real.sqrt (Real.rpow eps p) + Real.sqrt (Real.rpow delta p) +
          Real.sqrt (Real.rpow ((params.d : Error) / (params.q : Error)) p) :=
      sqrt_add3_le_add3_sqrt (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _)
        (Real.rpow_nonneg hdq_nonneg _)
    _ = Real.rpow eps (p / 2) + Real.rpow delta (p / 2) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (p / 2) := by
      rw [sqrt_rpow_eq_rpow_half heps, sqrt_rpow_eq_rpow_half hdelta,
        sqrt_rpow_eq_rpow_half hdq_nonneg]

/-- The helper-stage threshold as the final-stage power sum with exponent
`1/2`.

This is definitionally equal to `selfImprovementHelperError`; the named lemma is
used to avoid unfolding the error definition inside later absorptions. -/
theorem selfImprovementHelperError_eq_finalStagePowerSum
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementHelperError params eps delta =
      100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (2 : Error)) := by
  rfl

/-- The final self-improvement threshold as the final-stage power sum with
exponent `1/32`.

This records the literal error parameter appearing in the formal statement of
the self-improvement theorem. -/
theorem selfImprovementError_eq_finalStagePowerSum
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementError params eps delta =
      3000 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  rfl

private theorem sqrt_selfImprovementHelperError_le_ten_m_powerSum_quarter
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementHelperError params eps delta) ≤
      10 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (4 : Error)) := by
  have h100m_nn : (0 : Error) ≤ 100 * (params.m : Error) := by positivity
  have hsqrt100m := sqrt_100m_le_10m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (2 : Error)) heps hdelta
  have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
  rw [selfImprovementHelperError_eq_finalStagePowerSum]
  calc
    Real.sqrt (100 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (2 : Error)))
        = Real.sqrt (100 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error))) := by
          rw [Real.sqrt_mul h100m_nn]
    _ ≤ (10 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (4 : Error)) := by
          calc
            Real.sqrt (100 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error)))
                ≤ (10 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt100m (Real.sqrt_nonneg _)
            _ ≤ (10 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (4 : Error)) := by
                  rw [show (1 / (4 : Error)) = (1 / (2 : Error)) / 2 by norm_num]
                  exact mul_le_mul_of_nonneg_left hsqrt_sum h10m_nn

/-- The orthogonalization threshold written as an iterated square root of the
helper threshold.

The paper writes the corresponding quantity as
`100 * \widehat{\zeta}^{1/4}`. This lemma gives the equivalent square-root
form used by the estimates which follow orthonormalization. -/
theorem selfImprovementOrthogonalizationError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementOrthogonalizationError params eps delta =
      100 * Real.sqrt (Real.sqrt (selfImprovementHelperError params eps delta)) := by
  unfold selfImprovementOrthogonalizationError orthonormalizationError
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  congr 1
  calc
    Real.rpow (selfImprovementHelperError params eps delta) (1 / (4 : Error)) =
        Real.rpow (selfImprovementHelperError params eps delta)
          ((1 / (2 : Error)) * (1 / 2)) := by
      congr 1
      ring
    _ = Real.rpow
          (Real.rpow (selfImprovementHelperError params eps delta) (1 / (2 : Error)))
          (1 / (2 : Error)) := by
      exact Real.rpow_mul (selfImprovementHelperError_nonneg params eps delta)
        (1 / (2 : Error)) (1 / (2 : Error))

private theorem selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    selfImprovementOrthogonalizationError params eps delta ≤
      400 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (8 : Error)) := by
  have hsqrt_helper :=
    sqrt_selfImprovementHelperError_le_ten_m_powerSum_quarter params eps delta heps hdelta
  have hsqrt_mS :
      Real.sqrt (10 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (4 : Error))) ≤
        4 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (8 : Error)) := by
    have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
    have hsqrt10m := sqrt_10m_le_4m params
    have hsqrt_sum :=
      sqrt_finalStagePowerSum_le params eps delta (1 / (4 : Error)) heps hdelta
    have h4m_nn : (0 : Error) ≤ 4 * (params.m : Error) := by positivity
    calc
      Real.sqrt (10 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (4 : Error)))
          = Real.sqrt (10 * (params.m : Error)) *
            Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error))) := by
            rw [Real.sqrt_mul h10m_nn]
      _ ≤ (4 * (params.m : Error)) *
            finalStagePowerSum params eps delta (1 / (8 : Error)) := by
            calc
              Real.sqrt (10 * (params.m : Error)) *
                  Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error)))
                  ≤ (4 * (params.m : Error)) *
                      Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error))) :=
                    mul_le_mul_of_nonneg_right hsqrt10m (Real.sqrt_nonneg _)
              _ ≤ (4 * (params.m : Error)) *
                    finalStagePowerSum params eps delta (1 / (8 : Error)) := by
                    rw [show (1 / (8 : Error)) = (1 / (4 : Error)) / 2 by norm_num]
                    exact mul_le_mul_of_nonneg_left hsqrt_sum h4m_nn
  rw [selfImprovementOrthogonalizationError_eq]
  calc
    100 * Real.sqrt (Real.sqrt (selfImprovementHelperError params eps delta))
        ≤ 100 * Real.sqrt
            (10 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (4 : Error))) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsqrt_helper) (by norm_num)
    _ ≤ 100 * (4 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (8 : Error))) :=
        mul_le_mul_of_nonneg_left hsqrt_mS (by norm_num)
    _ = 400 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (8 : Error)) := by ring

private theorem sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
      20 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
  have horth :=
    selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
      params eps delta heps hdelta
  have h400m_nn : (0 : Error) ≤ 400 * (params.m : Error) := by positivity
  have hsqrt400m := sqrt_400m_le_20m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (8 : Error)) heps hdelta
  have h20m_nn : (0 : Error) ≤ 20 * (params.m : Error) := by positivity
  calc
    Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ Real.sqrt (400 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (8 : Error))) :=
          Real.sqrt_le_sqrt horth
    _ = Real.sqrt (400 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error))) := by
          rw [Real.sqrt_mul h400m_nn]
    _ ≤ (20 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (16 : Error)) := by
          calc
            Real.sqrt (400 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error)))
                ≤ (20 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt400m (Real.sqrt_nonneg _)
            _ ≤ (20 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (16 : Error)) := by
                  rw [show (1 / (16 : Error)) = (1 / (8 : Error)) / 2 by norm_num]
                  exact mul_le_mul_of_nonneg_left hsqrt_sum h20m_nn

/-- The data-processing threshold written with an ordinary square root.

This is the displayed expression used after projecting the helper output:
`8\widehat{\zeta} + 8\sqrt{\widehat{\zeta}_{\mathrm{ortho}}}`. -/
theorem selfImprovementDataProcessingError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementDataProcessingError params eps delta =
      8 * selfImprovementHelperError params eps delta +
        8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
  unfold selfImprovementDataProcessingError
  simp [Real.sqrt_eq_rpow, Real.rpow_eq_pow]





private theorem selfImprovementDataProcessingError_le_nine_sixty_m_powerSum_sixteenth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    selfImprovementDataProcessingError params eps delta ≤
      960 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (16 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hsqrt_orth :=
    sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
      params eps delta heps hdelta
  rw [selfImprovementDataProcessingError_eq]
  calc
    8 * selfImprovementHelperError params eps delta +
        8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ 8 * (100 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) +
          8 * (20 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) := by
          gcongr
    _ = 960 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (16 : Error)) := by ring

private theorem sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      31 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  have hdata :=
    selfImprovementDataProcessingError_le_nine_sixty_m_powerSum_sixteenth
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  have h960m_nn : (0 : Error) ≤ 960 * (params.m : Error) := by positivity
  have hsqrt960m := sqrt_960m_le_31m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (16 : Error)) heps hdelta
  have h31m_nn : (0 : Error) ≤ 31 * (params.m : Error) := by positivity
  calc
    Real.sqrt (selfImprovementDataProcessingError params eps delta)
        ≤ Real.sqrt (960 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) :=
          Real.sqrt_le_sqrt hdata
    _ = Real.sqrt (960 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error))) := by
          rw [Real.sqrt_mul h960m_nn]
    _ ≤ (31 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
          calc
            Real.sqrt (960 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error)))
                ≤ (31 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt960m (Real.sqrt_nonneg _)
            _ ≤ (31 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (32 : Error)) := by
                  rw [show (1 / (32 : Error)) = (1 / (16 : Error)) / 2 by norm_num]
                  exact mul_le_mul_of_nonneg_left hsqrt_sum h31m_nn

private theorem final_fields_projective_residual_error_le_131_times_finalStagePowerSum
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      131 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hdata_sqrt :
      Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        31 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    exact sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  nlinarith

/-- Final projective-residual threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective residual construction is
`ζ̂ + √ζ̂_dataprocess`. Under the standard unit-interval hypotheses for
`ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the literal
`selfImprovementError` threshold used by `SelfImprovementConclusion`.  Lean
records the third unit-interval hypothesis as `d ≤ q`, equivalently `d/q ≤ 1`
because `q` is positive. -/
theorem final_fields_projective_residual_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hhelper := final_fields_projective_residual_error_le_131_times_finalStagePowerSum params
    eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
  have hsum32_nn :
      0 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_nonneg params eps delta (1 / (32 : Error)) heps hdelta
  have hcoef :
      131 * (params.m : Error) ≤ 3000 * (params.m : Error) := by
    nlinarith [m_cast_nonneg params]
  calc
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        131 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := hhelper
    _ ≤ 3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) :=
        mul_le_mul_of_nonneg_right hcoef hsum32_nn
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]

/-- Final point-consistency threshold absorption from a total-difference bound.

The fallback submeasurement-total route contributes the natural error

`2 * ζ̂ + √ζ̂_dataprocess + 2 * √ζ̂_ortho`.

Under the standard unit-interval hypotheses for `ε`, `δ`, and `d/q`, this is
still absorbed by the literal `selfImprovementError` threshold. -/
theorem final_fields_point_consistency_total_difference_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    2 * selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hsqrt_orth_mono :
      finalStagePowerSum params eps delta (1 / (16 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hdata_sqrt :
      Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        31 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  have hsqrt_orth :
      Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
        20 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    have hsqrt16 :=
      sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
        params eps delta heps hdelta
    exact hsqrt16.trans
      (mul_le_mul_of_nonneg_left hsqrt_orth_mono (by positivity))
  have hm_nonneg : 0 ≤ (params.m : Error) := m_cast_nonneg params
  have hsum32_nonneg :
      0 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_nonneg params eps delta (1 / (32 : Error)) heps hdelta
  have hnatural :
      2 * selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) +
          2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
        3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    nlinarith
  calc
    2 * selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ 3000 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := hnatural
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]


/-- Final completeness threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective completeness transport is
`2ζ̂ + 2 sqrt ζ̂_ortho`. Under the standard unit-interval hypotheses for
`ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the literal
`selfImprovementError` threshold used by `SelfImprovementFinalFields`.  Lean
records the third unit-interval hypothesis as `d ≤ q`, equivalently `d/q ≤ 1`
because `q` is positive. -/
theorem final_fields_completeness_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    2 * selfImprovementHelperError params eps delta +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hsqrt_orth_mono :
      finalStagePowerSum params eps delta (1 / (16 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hsqrt_orth :
      Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
        20 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    have hsqrt16 :=
      sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
        params eps delta heps hdelta
    exact hsqrt16.trans
      (mul_le_mul_of_nonneg_left hsqrt_orth_mono (by positivity))
  have hm_nonneg : 0 ≤ (params.m : Error) := m_cast_nonneg params
  have hsum32_nonneg :
      0 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_nonneg params eps delta (1 / (32 : Error)) heps hdelta
  have hnatural :
      2 * selfImprovementHelperError params eps delta +
          2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
        3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    nlinarith
  calc
    2 * selfImprovementHelperError params eps delta +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ 3000 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := hnatural
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]

/-- Final self-closeness threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective self-closeness transport is
`3 * (ζ̂_ortho + 2ζ̂ + ζ̂_ortho)`. Under the standard unit-interval hypotheses
for `ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the
literal `selfImprovementError` threshold used by `SelfImprovementFinalFields`.
Lean records the third unit-interval hypothesis as `d ≤ q`, equivalently
`d/q ≤ 1` because `q` is positive.
-/
theorem final_fields_self_closeness_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    3 * (selfImprovementOrthogonalizationError params eps delta +
        2 * selfImprovementHelperError params eps delta +
        selfImprovementOrthogonalizationError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
  have horth_mono :
      finalStagePowerSum params eps delta (1 / (8 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have horth :
      selfImprovementOrthogonalizationError params eps delta ≤
        400 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    have horth8 :=
      selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
        params eps delta heps hdelta
    exact horth8.trans
      (mul_le_mul_of_nonneg_left horth_mono (by positivity))
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hnatural :
      3 * (selfImprovementOrthogonalizationError params eps delta +
          2 * selfImprovementHelperError params eps delta +
          selfImprovementOrthogonalizationError params eps delta) ≤
        3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    nlinarith
  calc
    3 * (selfImprovementOrthogonalizationError params eps delta +
        2 * selfImprovementHelperError params eps delta +
        selfImprovementOrthogonalizationError params eps delta)
        ≤ 3000 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := hnatural
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


