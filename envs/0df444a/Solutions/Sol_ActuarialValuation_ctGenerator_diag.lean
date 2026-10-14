-- Prove2me | solution 1 for ActuarialValuation.ctGenerator_diag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:07.048413+00:00
-- url     : https://prove2.me/submissions/89be9126-a747-43e9-b1bb-534d14e19b1e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRateOut
import Definitions.Def_actuarial_ctGenerator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ctGenerator r i i = -ctRateOut r i := by
  simp [ctGenerator]
