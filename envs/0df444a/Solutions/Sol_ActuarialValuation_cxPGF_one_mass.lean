-- Prove2me | solution 1 for ActuarialValuation.cxPGF_one_mass
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:31:43.524756+00:00
-- url     : https://prove2.me/submissions/e3953442-1587-4b31-a9d9-ec81bb6f4e38

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
import Definitions.Def_actuarial_cxMass
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (n : ℕ) : cxPGF f n 1 = cxMass f n := by
  first
  | (simp [cxPGF, cxMass]; done)
  | (norm_num [cxPGF, cxMass]; done)
  | (unfold cxPGF cxMass; positivity)
  | (simp only [cxPGF, cxMass]; positivity)
  | (unfold cxPGF cxMass; ring)
  | (unfold cxPGF cxMass; simp; done)
  | (unfold cxPGF cxMass; norm_num; done)
  | (simp [cxPGF, cxMass]; ring)
  | (unfold cxPGF cxMass; split_ifs <;> simp_all <;> linarith)
  | (unfold cxPGF cxMass; nlinarith [sq_nonneg 0])
  | (simp_all [cxPGF, cxMass]; done)
  | (unfold cxPGF cxMass; simp_all; done)
  | rfl
