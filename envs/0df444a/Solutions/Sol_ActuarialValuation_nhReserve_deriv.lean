-- Prove2me | solution 1 for ActuarialValuation.nhReserve_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:16:19.004626+00:00
-- url     : https://prove2.me/submissions/ae2369a1-2773-454b-9456-f721b2d62ed7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhReserve
import Definitions.Def_actuarial_nhThieleRHS
import Theorems.Thm_ActuarialValuation_nhEndowment_deriv
import Theorems.Thm_ActuarialValuation_nhDeathPV_deriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p δ B1 B2 M T t : ℝ) : HasDerivAt (nhReserve a b p δ B1 B2 M T) (nhThieleRHS a b p δ B1 B2 t (nhReserve a b p δ B1 B2 M T t)) t := by
  have hE := ActuarialValuation.nhEndowment_deriv a b δ T M t
  have hD := ActuarialValuation.nhDeathPV_deriv a b p δ B1 B2 T t
  convert hE.add hD using 1 <;>
    first
    | rfl
    | (funext x; rfl)
    | (dsimp [nhReserve,nhThieleRHS]; ring)
