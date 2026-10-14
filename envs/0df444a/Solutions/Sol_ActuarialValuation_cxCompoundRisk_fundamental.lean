-- Prove2me | solution 1 for ActuarialValuation.cxCompoundRisk_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:58:55.523175+00:00
-- url     : https://prove2.me/submissions/b272bc02-d7b7-4397-bbc0-6714d34a708c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
import Definitions.Def_actuarial_cxMass
import Definitions.Def_actuarial_cxBernAggregateMass
import Definitions.Def_actuarial_cxBernAggregatePGF
import Definitions.Def_actuarial_cxBernCountPGF
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

theorem solution (f : ℕ → ℝ) (n : ℕ) (p0 p1 z f1 : ℝ) (h0 : p0 ≠ 0) (hm : cxMass f n = 1) (hp : p0+p1=1) : (cxBernAggregatePGF p0 p1 f n z = cxBernCountPGF p0 p1 (cxPGF f n z)) ∧ (cxBernAggregatePGF p0 p1 f n 1 = 1) ∧ (cxBernAggregateMass p0 p1 f 0 = p0+p1*f 0) ∧ (cxBernAggregateMass p0 p1 (fun k => if k=0 then f 0 else if k=1 then f1 else 0) 1 * cxPanjerAdjustment (cxPanjerA p0 p1) (f 0) = cxPanjerFirstRHS (cxPanjerA p0 p1) (cxPanjerB p0 p1) f1 (p0+p1*f 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · have hG : cxPGF f n 1 = 1 := by
      simpa [cxPGF, cxMass] using hm
    simpa [cxBernAggregatePGF, hG] using hp
  · simp [cxBernAggregateMass]
  · change p1 * f1 * (1 - (-p1 / p0) * f 0) =
        ((-p1 / p0) + (2 * p1 / p0)) * f1 * (p0 + p1 * f 0)
    field_simp [h0] <;> ring
