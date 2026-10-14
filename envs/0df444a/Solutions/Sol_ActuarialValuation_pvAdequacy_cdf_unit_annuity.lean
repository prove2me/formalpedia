-- Prove2me | solution 1 for ActuarialValuation.pvAdequacy_cdf_unit_annuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:23.743063+00:00
-- url     : https://prove2.me/submissions/e407fa4d-f7ad-4617-bbbb-44a6aa92ccf0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p benefit : Fin n → ℝ) (premium : ℝ) : pvAdequacy p benefit (fun _ => 1) premium = pvCdf p benefit premium := by
  simp [pvAdequacy, pvCdf]
