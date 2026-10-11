-- Prove2me | solution 1 for ActuarialValuation.crSpread_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:43:55.735346+00:00
-- url     : https://prove2.me/submissions/ec1c24a5-f782-45b8-8d54-245ac7969c53

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crAmbiguitySpread
open ActuarialValuation

theorem solution{n : ℕ} (p q X : Fin n→ℝ) : 0≤crAmbiguitySpread p q X := by
  unfold crAmbiguitySpread crScenarioRisk crBestCaseRisk
  exact sub_nonneg.2 min_le_max
