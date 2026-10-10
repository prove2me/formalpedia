-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleContinuousValuation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:26:46.66565+00:00
-- url     : https://prove2.me/submissions/cc1d114f-bd17-44bf-9709-63fb6fa1d890

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_cm1ThieleReserve
import Definitions.Def_actuarial_cm1ThieleRHS
import Definitions.Def_actuarial_cm1ForceBenefitPV
import Definitions.Def_actuarial_cm1ForcePremiumPV
import Theorems.Thm_ActuarialValuation_cm1ThieleReserve_terminal
import Theorems.Thm_ActuarialValuation_cm1ThieleReserve_issue_value
import Theorems.Thm_ActuarialValuation_cm1ThieleReserve_nonneg
import Theorems.Thm_ActuarialValuation_cm1ForceTermFactor_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P T : ℝ) (hk : 0 < δ+μ)
    (hT : 0 ≤ T) (hnet : P ≤ μ*B) :
    (cm1ThieleReserve δ μ B P T T = 0) ∧
    (cm1ThieleReserve δ μ B P T 0 =
      cm1ForceBenefitPV δ μ B T - cm1ForcePremiumPV δ μ P T) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ T →
      0 ≤ cm1ThieleReserve δ μ B P T t ∧
      deriv (cm1ThieleReserve δ μ B P T) t =
        cm1ThieleRHS δ μ B P (cm1ThieleReserve δ μ B P T t)) := by
  constructor
  · exact cm1ThieleReserve_terminal δ μ B P T
  constructor
  · exact cm1ThieleReserve_issue_value δ μ B P T
  intro t ht0 htT
  constructor
  · exact cm1ThieleReserve_nonneg δ μ B P T t hk htT hnet
  · have hk0 : δ + μ ≠ 0 := ne_of_gt hk
    have hderiv :
        deriv (cm1ThieleReserve δ μ B P T) t =
          -cm1ForceNetOutgo μ B P * Real.exp (-(δ+μ)*(T-t)) := by
      change deriv (fun s : ℝ => cm1ForceNetOutgo μ B P *
        cm1ForceTermFactor δ μ T s) t =
          -cm1ForceNetOutgo μ B P * Real.exp (-(δ+μ)*(T-t))
      rw [deriv_const_mul_field (cm1ForceNetOutgo μ B P),
          cm1ForceTermFactor_deriv δ μ T t hk0]
      ring
    rw [hderiv]
    dsimp [cm1ThieleRHS, cm1ThieleReserve, cm1ForceNetOutgo,
      cm1ForceTermFactor]
    field_simp [hk0]
    ring
