-- Prove2me | solution 1 for ActuarialValuation.irReinflate_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:02:38.39937+00:00
-- url     : https://prove2.me/submissions/b98b0a4b-fd1f-484b-a244-87c3dd03eb6f

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

theorem solution (claim base future : ℝ) (hb : base≠0) (hf : future≠0) : irDeflate (irReinflate claim future base) base future=claim := by
  unfold irReinflate irDeflate
  field_simp [hb, hf]
