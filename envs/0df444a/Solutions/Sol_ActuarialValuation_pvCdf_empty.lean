-- Prove2me | solution 1 for ActuarialValuation.pvCdf_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:25.927592+00:00
-- url     : https://prove2.me/submissions/58710692-36cb-4034-8b60-1290cdc33dde

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (loss : Fin 0 → ℝ) (z : ℝ) : pvCdf (fun _ => 0) loss z = 0 := by
  simp [pvCdf]
