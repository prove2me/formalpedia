-- Prove2me | Definitions.Def_levy_foundations_weakExpBCF
-- name    : levy_foundations_weakExpBCF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:18:32.681558+00:00
-- url     : https://prove2.me/theorems/01cefe5b-b4cb-40ed-bb9e-89267cee27f4
-- title:
--   Bounded continuous complex exponential Fourier character
-- statement:
--   Bounded continuous complex exponential Fourier character.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/WeakConvergence.lean#L61

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.IntegralCharFun

open MeasureTheory Complex BoundedContinuousFunction
namespace LevyFoundations
/-- Complex exponential character as a bounded continuous function. -/
noncomputable def weakExpBCF (ξ : ℝ) : ℝ →ᵇ ℂ :=
  .mkOfBound ⟨fun x => exp (↑(ξ * x) * Complex.I), by fun_prop⟩ 2
    (fun x y => by
      calc dist (exp (↑(ξ * x) * Complex.I)) (exp (↑(ξ * y) * Complex.I))
          ≤ ‖exp (↑(ξ * x) * Complex.I)‖ + ‖exp (↑(ξ * y) * Complex.I)‖ :=
              dist_le_norm_add_norm _ _
        _ = 1 + 1 := by simp only [norm_exp_ofReal_mul_I]
        _ = 2 := by ring)
end LevyFoundations


