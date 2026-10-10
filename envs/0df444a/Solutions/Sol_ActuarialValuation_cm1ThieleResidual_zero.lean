-- Prove2me | solution 1 for ActuarialValuation.cm1ThieleResidual_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:27:39.521168+00:00
-- url     : https://prove2.me/submissions/ccc5ff96-630f-4078-9803-0c30209a9f6b

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_actuarial_cm1ThieleResidual
import Definitions.Def_actuarial_cm1ThieleReserve
import Definitions.Def_actuarial_cm1ThieleRHS
import Theorems.Thm_ActuarialValuation_cm1ForceTermFactor_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (δ μ B P T t : ℝ) (hk : δ+μ ≠ 0) :
    cm1ThieleResidual δ μ B P T t = 0 := by
  have hderiv :
      deriv (cm1ThieleReserve δ μ B P T) t =
        -cm1ForceNetOutgo μ B P * Real.exp (-(δ+μ)*(T-t)) := by
    change deriv (fun s : ℝ => cm1ForceNetOutgo μ B P *
      cm1ForceTermFactor δ μ T s) t =
        -cm1ForceNetOutgo μ B P * Real.exp (-(δ+μ)*(T-t))
    rw [deriv_const_mul_field (cm1ForceNetOutgo μ B P),
        cm1ForceTermFactor_deriv δ μ T t hk]
    ring
  unfold cm1ThieleResidual
  rw [hderiv]
  dsimp [cm1ThieleRHS, cm1ThieleReserve, cm1ForceNetOutgo,
    cm1ForceTermFactor]
  field_simp [hk]
  ring
