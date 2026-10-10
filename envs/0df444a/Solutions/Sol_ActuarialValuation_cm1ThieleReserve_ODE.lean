-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleReserve_ODE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:25:54.690359+00:00
-- url     : https://prove2.me/submissions/4927d0af-176f-4f2b-9fd0-9551833511cb

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_cm1ThieleReserve
import Definitions.Def_actuarial_cm1ThieleRHS
import Theorems.Thm_ActuarialValuation_cm1ForceTermFactor_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P T t : ℝ) (hk : δ+μ ≠ 0) :
    deriv (cm1ThieleReserve δ μ B P T) t =
      cm1ThieleRHS δ μ B P (cm1ThieleReserve δ μ B P T t) := by
  have hderiv :
      deriv (cm1ThieleReserve δ μ B P T) t =
        -cm1ForceNetOutgo μ B P * Real.exp (-(δ+μ)*(T-t)) := by
    change deriv (fun s : ℝ => cm1ForceNetOutgo μ B P *
      cm1ForceTermFactor δ μ T s) t =
        -cm1ForceNetOutgo μ B P * Real.exp (-(δ+μ)*(T-t))
    rw [deriv_const_mul_field (cm1ForceNetOutgo μ B P),
        cm1ForceTermFactor_deriv δ μ T t hk]
    ring
  rw [hderiv]
  dsimp [cm1ThieleRHS, cm1ThieleReserve, cm1ForceNetOutgo,
    cm1ForceTermFactor]
  field_simp [hk]
  ring
