-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:04:03.152531+00:00
-- url     : https://prove2.me/theorems/2b7e7976-5a20-4c1b-80fa-7d3873a16934
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Thresholds / Helper
-- statement:
--   This bundle supplies the elementary threshold inequalities used to absorb self-improvement errors. It records positivity of the discrete parameters and the dimension ratio, then bounds the square roots that appear in the helper estimates by linear expressions in the degree parameter.
--
--   Principal definitions:
--   - `one_le_m_cast`: the parameter `m` is at least one after casting to the error scalar field.
--   - `m_cast_nonneg`: nonnegativity of the cast parameter `m`.
--   - `d_q_ratio_nonneg`: nonnegativity of the cast ratio `d / q`.
--   - `d_q_ratio_le_one_of_d_le_q`: the ratio `d / q` is at most one when `d <= q`.
--   - `sqrt_100m_le_10m`: the square root of `100m` is at most `10m` for `m >= 1`.
--   - `sqrt_10m_le_4m`: the square root of `10m` is at most `4m` for `m >= 1`.
--   - `sqrt_400m_le_20m`: the square root of `400m` is at most `20m` for `m >= 1`.
--   - `sqrt_960m_le_31m`: the square root of `960m` is at most `31m` for `m >= 1`.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Helper.lean#L45-L515

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Helper.lean by skeleton subtraction.
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
# Section 9 — helper-stage numerical threshold absorptions

Reusable arithmetic threshold lemmas that compare the *natural* paper sums of
errors emitted by the helper-stage self-improvement constructions against the
literal `selfImprovementHelperError` threshold used by the final-field
statements (`SelfImprovementFinalFields` in `Statements.lean`).

The helper-stage absorptions formalize the displayed paper inequalities:

* `references/ldt-paper/self_improvement.tex`, lines 438--443 — point
  consistency: `4 √ζ_var ≤ ζ̂`.
* `references/ldt-paper/self_improvement.tex`, lines 595--603 — strong
  self-consistency: `11 √ζ_var + √(2δ) + md/q ≤ ζ̂`.
* `references/ldt-paper/self_improvement.tex`, lines 403--414 — completeness:
  `3 √δ ≤ ζ̂`.
* `references/ldt-paper/self_improvement.tex`, lines 614--624 — boundedness:
  `3 √δ + 4 √ζ_var ≤ ζ̂`.

The final-stage comparisons with `selfImprovementError` are collected in
`Thresholds.Final`.

Blueprint mirrors:

* `blueprint/src/chapter/ch07_self_improvement.tex`, lines 161--168 (point
  consistency) and 256--279 (strong self-consistency / boundedness).
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective

/-! ## Parameter convenience facts -/

/-- The parameter `m` is at least one, viewed in the error scalar field. -/
theorem one_le_m_cast (params : Parameters) :
    (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm

/-- The parameter `m`, viewed in the error scalar field, is nonnegative. -/
theorem m_cast_nonneg (params : Parameters) :
    (0 : Error) ≤ (params.m : Error) := by positivity

/-- The ratio `d/q`, viewed in the error scalar field, is nonnegative. -/
theorem d_q_ratio_nonneg (params : Parameters) :
    (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
  div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt params.q_cast_pos)

/-- If `d ≤ q`, then the ratio `d/q` is at most one. -/
theorem d_q_ratio_le_one_of_d_le_q
    (params : Parameters)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    ((params.d : Error) / (params.q : Error)) ≤ 1 :=
  (div_le_one params.q_cast_pos).mpr hd_le_q

/-- For `m ≥ 1`, `√(100m) ≤ 10m`. -/
theorem sqrt_100m_le_10m (params : Parameters) :
    Real.sqrt (100 * (params.m : Error)) ≤ 10 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h10m_nn).mpr ?_
  nlinarith [hmpos, hm1]

/-- For `m ≥ 1`, `√(10m) ≤ 4m`. -/
theorem sqrt_10m_le_4m (params : Parameters) :
    Real.sqrt (10 * (params.m : Error)) ≤ 4 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h4m_nn : (0 : Error) ≤ 4 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h4m_nn).mpr ?_
  nlinarith [hmpos, hm1]

/-- For `m ≥ 1`, `√(400m) ≤ 20m`. -/
theorem sqrt_400m_le_20m (params : Parameters) :
    Real.sqrt (400 * (params.m : Error)) ≤ 20 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h20m_nn : (0 : Error) ≤ 20 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h20m_nn).mpr ?_
  nlinarith [hmpos, hm1]

/-- For `m ≥ 1`, `√(960m) ≤ 31m`. -/
theorem sqrt_960m_le_31m (params : Parameters) :
    Real.sqrt (960 * (params.m : Error)) ≤ 31 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h31m_nn : (0 : Error) ≤ 31 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h31m_nn).mpr ?_
  nlinarith [hmpos, hm1]

/-! ## Subroutine: square-root bound on `globalVarianceOfPointsError`

The paper's central arithmetic step (`self_improvement.tex`, line 441) is

`√(24 m (ε + δ + md/q)) ≤ 20 m (ε^{1/2} + δ^{1/2} + (d/q)^{1/2})`.

We separate the constant `5` from the multipliers `4`/`11`/`3` used downstream
and prove a single reusable bound. -/

/-- Expansion of the variance error into the three residuals appearing in the
self-improvement paper.

The final summand is written as `m * (d / q)`, rather than `(m * d) / q`, so
that square-root estimates may split the last product directly. -/
theorem selfImprovementVarianceError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementVarianceError params eps delta =
      24 * (params.m : Error) *
        (eps + delta +
          ((params.m : Error) * ((params.d : Error) / (params.q : Error)))) := by
  unfold selfImprovementVarianceError globalVarianceOfPointsError generalizeBError
  rw [mul_div_assoc]

/-- Paper-faithful square-root bound on the variance error
(`self_improvement.tex`, lines 440--442). -/
theorem sqrt_selfImprovementVarianceError_le
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      5 * (params.m : Error) *
        (Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error))) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  rw [selfImprovementVarianceError_eq]
  have h24m_nn : (0 : Error) ≤ 24 * (params.m : Error) := by positivity
  have hmdq_nn :
      (0 : Error) ≤ (params.m : Error) * ((params.d : Error) / (params.q : Error)) :=
    mul_nonneg hmpos hdq_nonneg
  -- Step 1: √(24m * X) = √(24m) * √X.
  rw [Real.sqrt_mul h24m_nn]
  -- Step 2: √(eps + delta + m*(d/q)) ≤ √eps + √delta + √(m*(d/q)).
  have hstep2 :
      Real.sqrt (eps + delta +
          ((params.m : Error) * ((params.d : Error) / (params.q : Error)))) ≤
        Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.m : Error) *
            ((params.d : Error) / (params.q : Error))) :=
    sqrt_add3_le_add3_sqrt heps hdelta hmdq_nn
  have hsplit_mdq :
      Real.sqrt ((params.m : Error) * ((params.d : Error) / (params.q : Error))) =
        Real.sqrt (params.m : Error) *
          Real.sqrt ((params.d : Error) / (params.q : Error)) :=
    Real.sqrt_mul hmpos _
  -- √(24m) ≤ 5m.
  have hsqrt24m_le : Real.sqrt (24 * (params.m : Error)) ≤ 5 * (params.m : Error) :=
    by
      have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
      have h5m_nn : (0 : Error) ≤ 5 * (params.m : Error) := by positivity
      refine (Real.sqrt_le_left h5m_nn).mpr ?_
      nlinarith [hmpos, hm1]
  -- √(24m) * √m = √(24 m²) ≤ 5m.
  have hsplit_24m_m :
      Real.sqrt (24 * (params.m : Error)) * Real.sqrt (params.m : Error) =
        Real.sqrt (24 * ((params.m : Error) ^ (2 : ℕ))) := by
    rw [← Real.sqrt_mul h24m_nn]
    congr 1; ring
  have hsqrt24m_m_le :
      Real.sqrt (24 * (params.m : Error)) * Real.sqrt (params.m : Error) ≤
        5 * (params.m : Error) := by
    rw [hsplit_24m_m]
    have h5m_nn : (0 : Error) ≤ 5 * (params.m : Error) := by positivity
    refine (Real.sqrt_le_left h5m_nn).mpr ?_
    nlinarith [sq_nonneg ((params.m : Error)), hmpos]
  have hsqrt24m_nn : (0 : Error) ≤ Real.sqrt (24 * (params.m : Error)) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt (24 * (params.m : Error)) *
        Real.sqrt (eps + delta +
          ((params.m : Error) * ((params.d : Error) / (params.q : Error))))
        ≤ Real.sqrt (24 * (params.m : Error)) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.m : Error) *
                ((params.d : Error) / (params.q : Error)))) :=
          mul_le_mul_of_nonneg_left hstep2 hsqrt24m_nn
    _ = Real.sqrt (24 * (params.m : Error)) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt (params.m : Error) *
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by
          rw [hsplit_mdq]
    _ = Real.sqrt (24 * (params.m : Error)) * Real.sqrt eps +
          Real.sqrt (24 * (params.m : Error)) * Real.sqrt delta +
          (Real.sqrt (24 * (params.m : Error)) * Real.sqrt (params.m : Error)) *
            Real.sqrt ((params.d : Error) / (params.q : Error)) := by ring
    _ ≤ 5 * (params.m : Error) * Real.sqrt eps +
          5 * (params.m : Error) * Real.sqrt delta +
          5 * (params.m : Error) *
            Real.sqrt ((params.d : Error) / (params.q : Error)) := by
          have h1 :
              Real.sqrt (24 * (params.m : Error)) * Real.sqrt eps ≤
                5 * (params.m : Error) * Real.sqrt eps :=
            mul_le_mul_of_nonneg_right hsqrt24m_le (Real.sqrt_nonneg _)
          have h2 :
              Real.sqrt (24 * (params.m : Error)) * Real.sqrt delta ≤
                5 * (params.m : Error) * Real.sqrt delta :=
            mul_le_mul_of_nonneg_right hsqrt24m_le (Real.sqrt_nonneg _)
          have h3 :
              (Real.sqrt (24 * (params.m : Error)) *
                  Real.sqrt (params.m : Error)) *
                  Real.sqrt ((params.d : Error) / (params.q : Error)) ≤
                5 * (params.m : Error) *
                  Real.sqrt ((params.d : Error) / (params.q : Error)) :=
            mul_le_mul_of_nonneg_right hsqrt24m_m_le (Real.sqrt_nonneg _)
          linarith
    _ = 5 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring

/-- Expansion of the helper-stage self-improvement error into the square-root
sum used in the paper.

This form is often the convenient one for the helper-stage absorptions: it
identifies `selfImprovementHelperError` with
`100 m (√ε + √δ + √(d/q))`, rather than requiring each proof to unfold the
definition and convert the three `rpow` terms separately. -/
theorem selfImprovementHelperError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementHelperError params eps delta =
      100 * (params.m : Error) *
        (Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error))) := by
  simp [selfImprovementHelperError, Real.sqrt_eq_rpow, Real.rpow_eq_pow]

/-- The helper-stage threshold is nonnegative.

This is the basic positivity fact reused by the helper-stage absorption wrappers
and by the final-stage comparison with `selfImprovementError`. -/
theorem selfImprovementHelperError_nonneg
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error) :
    0 ≤ selfImprovementHelperError params eps delta := by
  rw [selfImprovementHelperError_eq]
  positivity

/-- Helper-stage point-consistency absorption (`self_improvement.tex`,
lines 438--443).

`4 √ζ_variance ≤ ζ̂`. -/
theorem helper_point_consistency_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    4 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      selfImprovementHelperError params eps delta := by
  have hsqrtbound :=
    sqrt_selfImprovementVarianceError_le params eps delta heps hdelta
  have hmnonneg : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hsum_nonneg :
      (0 : Error) ≤ Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by positivity
  rw [selfImprovementHelperError_eq]
  calc
    4 * Real.sqrt (selfImprovementVarianceError params eps delta)
        ≤ 4 * (5 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error)))) :=
          mul_le_mul_of_nonneg_left hsqrtbound (by norm_num)
    _ = 20 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
    _ ≤ 100 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
          have hcoef : (20 : Error) * (params.m : Error) ≤ 100 * (params.m : Error) := by
            nlinarith [hmnonneg]
          exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg

/-- Helper-stage strong-self-consistency absorption (`self_improvement.tex`,
lines 595--603).

`11 √ζ_variance + √(2δ) + md/q ≤ ζ̂`.  The hypothesis `hd_le_q`
records the small-error branch `d/q ≤ 1` used in the paper, since `q > 0`. -/
theorem helper_strong_self_consistency_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) +
        ((params.m : Error) * (params.d : Error) / (params.q : Error)) ≤
      selfImprovementHelperError params eps delta := by
  have hmnonneg : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
  have hsqrtbound :=
    sqrt_selfImprovementVarianceError_le params eps delta heps hdelta
  -- `√(2δ) ≤ 2 √δ`, since `√2 ≤ 2`.
  have hsqrt2_le_2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.mul_self_sqrt (by norm_num : (0 : Error) ≤ 2),
      Real.sqrt_nonneg (2 : Error)]
  have hsqrt2delta_le :
      Real.sqrt (2 * delta) ≤ 2 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : Error) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrt2_le_2 (Real.sqrt_nonneg _)
  -- `m * d / q = m * (d / q) ≤ m * √(d/q)` since `d/q ∈ [0, 1]`.
  have hdq_le_sqrt_dq :
      ((params.d : Error) / (params.q : Error)) ≤
        Real.sqrt ((params.d : Error) / (params.q : Error)) := by
    have hsqrtnn :
        (0 : Error) ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
      Real.sqrt_nonneg _
    have hsqrt_self :
        Real.sqrt ((params.d : Error) / (params.q : Error)) *
          Real.sqrt ((params.d : Error) / (params.q : Error)) =
          (params.d : Error) / (params.q : Error) :=
      Real.mul_self_sqrt hdq_nonneg
    have hsqrt_le_one :
        Real.sqrt ((params.d : Error) / (params.q : Error)) ≤ 1 :=
      Real.sqrt_le_one.mpr hdq_le_one
    nlinarith [hsqrtnn, hsqrt_self, hsqrt_le_one, hdq_nonneg]
  have hmd_q_eq :
      (params.m : Error) * (params.d : Error) / (params.q : Error) =
        (params.m : Error) * ((params.d : Error) / (params.q : Error)) :=
    mul_div_assoc _ _ _
  have hmd_q_le_msqrt :
      (params.m : Error) * (params.d : Error) / (params.q : Error) ≤
        (params.m : Error) *
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by
    rw [hmd_q_eq]
    exact mul_le_mul_of_nonneg_left hdq_le_sqrt_dq hmnonneg
  -- Components of the sum-of-roots `s`.
  have hsum_nonneg :
      (0 : Error) ≤ Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by positivity
  have hsqrt_eps_nn : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have hsqrt_delta_nn : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrt_dq_nn : 0 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
    Real.sqrt_nonneg _
  have hsqrt_delta_le_sum : Real.sqrt delta ≤
      Real.sqrt eps + Real.sqrt delta +
        Real.sqrt ((params.d : Error) / (params.q : Error)) := by linarith
  have hsqrt_dq_le_sum :
      Real.sqrt ((params.d : Error) / (params.q : Error)) ≤
        Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by linarith
  -- 11 √varE ≤ 55 m * sum.
  have h11 :
      11 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
        55 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    calc
      11 * Real.sqrt (selfImprovementVarianceError params eps delta)
          ≤ 11 * (5 * (params.m : Error) *
              (Real.sqrt eps + Real.sqrt delta +
                Real.sqrt ((params.d : Error) / (params.q : Error)))) :=
            mul_le_mul_of_nonneg_left hsqrtbound (by norm_num)
      _ = 55 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
  -- √(2δ) ≤ 2m * sum.
  have h2sqrt :
      Real.sqrt (2 * delta) ≤ 2 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    have h2coef : (2 : Error) ≤ 2 * (params.m : Error) := by nlinarith [hm1]
    have h2m_nn : (0 : Error) ≤ 2 * (params.m : Error) := by nlinarith [hmnonneg]
    calc
      Real.sqrt (2 * delta)
          ≤ 2 * Real.sqrt delta := hsqrt2delta_le
      _ ≤ 2 * (params.m : Error) * Real.sqrt delta :=
          mul_le_mul_of_nonneg_right h2coef hsqrt_delta_nn
      _ ≤ 2 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) :=
          mul_le_mul_of_nonneg_left hsqrt_delta_le_sum h2m_nn
  -- m * d / q ≤ m * sum.
  have hmd_q_le_msum :
      (params.m : Error) * (params.d : Error) / (params.q : Error) ≤
        (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    calc
      (params.m : Error) * (params.d : Error) / (params.q : Error)
          ≤ (params.m : Error) *
              Real.sqrt ((params.d : Error) / (params.q : Error)) := hmd_q_le_msqrt
      _ ≤ (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) :=
          mul_le_mul_of_nonneg_left hsqrt_dq_le_sum hmnonneg
  rw [selfImprovementHelperError_eq]
  calc
    11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) +
        ((params.m : Error) * (params.d : Error) / (params.q : Error))
        ≤ 55 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) +
          2 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) +
          (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by
        linarith
    _ = 58 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
    _ ≤ 100 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
        have hcoef : (58 : Error) * (params.m : Error) ≤ 100 * (params.m : Error) := by
          nlinarith [hmnonneg]
        exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg

/-- Helper-stage boundedness absorption (`self_improvement.tex`, lines
614--624).

`3 √δ + 4 √ζ_variance ≤ ζ̂`. -/
theorem helper_boundedness_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    3 * Real.sqrt delta + 4 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      selfImprovementHelperError params eps delta := by
  have hmnonneg : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have hsqrtbound :=
    sqrt_selfImprovementVarianceError_le params eps delta heps hdelta
  have hsqrt_eps_nn : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have hsqrt_delta_nn : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrt_dq_nn : 0 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
    Real.sqrt_nonneg _
  have hsum_nonneg :
      (0 : Error) ≤ Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by positivity
  have hsqrt_delta_le_sum :
      Real.sqrt delta ≤
        Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by linarith
  -- 3 √δ ≤ 3m * sum.
  have h3sqrt_delta :
      3 * Real.sqrt delta ≤ 3 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    have h3coef : (3 : Error) ≤ 3 * (params.m : Error) := by nlinarith [hm1]
    have h3m_nn : (0 : Error) ≤ 3 * (params.m : Error) := by nlinarith [hmnonneg]
    calc
      3 * Real.sqrt delta
          ≤ 3 * (params.m : Error) * Real.sqrt delta :=
            mul_le_mul_of_nonneg_right h3coef hsqrt_delta_nn
      _ ≤ 3 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) :=
            mul_le_mul_of_nonneg_left hsqrt_delta_le_sum h3m_nn
  -- 4 √varE ≤ 20 m * sum.
  have h4sqrt :
      4 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
        20 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    calc
      4 * Real.sqrt (selfImprovementVarianceError params eps delta)
          ≤ 4 * (5 * (params.m : Error) *
              (Real.sqrt eps + Real.sqrt delta +
                Real.sqrt ((params.d : Error) / (params.q : Error)))) :=
            mul_le_mul_of_nonneg_left hsqrtbound (by norm_num)
      _ = 20 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
  rw [selfImprovementHelperError_eq]
  calc
    3 * Real.sqrt delta + 4 * Real.sqrt (selfImprovementVarianceError params eps delta)
        ≤ 3 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) +
          20 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by linarith
    _ = 23 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
    _ ≤ 100 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
        have hcoef : (23 : Error) * (params.m : Error) ≤ 100 * (params.m : Error) := by
          nlinarith [hmnonneg]
        exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg

/-- Helper-stage completeness absorption (`self_improvement.tex`, lines
403--414).

The loss `3 √δ` from the Cauchy--Schwarz comparison is bounded by the helper
threshold `ζ̂`. -/
theorem helper_completeness_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    3 * Real.sqrt delta ≤ selfImprovementHelperError params eps delta := by
  have hvariance_nonneg :
      0 ≤ 4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    positivity
  calc
    3 * Real.sqrt delta
        ≤ 3 * Real.sqrt delta +
            4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
          linarith
    _ ≤ selfImprovementHelperError params eps delta :=
          helper_boundedness_error_le_selfImprovementHelperError params eps delta
            heps hdelta


end MIPStarRE.LDT.SelfImprovement

end

end LIDT


