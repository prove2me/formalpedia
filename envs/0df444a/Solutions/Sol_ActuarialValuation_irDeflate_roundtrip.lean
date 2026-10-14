-- Prove2me | solution 1 for ActuarialValuation.irDeflate_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:59:32.584976+00:00
-- url     : https://prove2.me/submissions/95ba343d-74a0-4b85-aff9-76ba976d3d3c

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDeflate
import Definitions.Def_actuarial_irReinflate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim base hist : ℝ) (hb : base≠0) (hh : hist≠0) : irReinflate (irDeflate claim base hist) hist base=claim := by
  unfold irDeflate irReinflate
  field_simp [hb, hh]
