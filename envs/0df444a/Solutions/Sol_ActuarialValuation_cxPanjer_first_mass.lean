-- Prove2me | solution 1 for ActuarialValuation.cxPanjer_first_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T15:04:39.13926+00:00
-- url     : https://prove2.me/submissions/a33031d3-e870-44d1-b5a5-194087b21ec5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregateMass
import Definitions.Def_actuarial_cxPanjerA
import Definitions.Def_actuarial_cxPanjerB
import Definitions.Def_actuarial_cxPanjerAdjustment
import Definitions.Def_actuarial_cxPanjerFirstRHS
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 p1 f0 f1 : ℝ) (hp0 : p0 ≠ 0) : cxBernAggregateMass p0 p1 (fun k => if k=0 then f0 else if k=1 then f1 else 0) 1 * cxPanjerAdjustment (cxPanjerA p0 p1) f0 = cxPanjerFirstRHS (cxPanjerA p0 p1) (cxPanjerB p0 p1) f1 (p0+p1*f0) := by
  change p1 * f1 * (1 - (-p1 / p0) * f0) =
    ((-p1 / p0) + (2 * p1 / p0)) * f1 * (p0 + p1 * f0)
  field_simp [hp0] <;> ring
