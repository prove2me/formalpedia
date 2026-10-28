-- Prove2me | Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
-- name    : D1Bound5_BennettPoleSeries_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:21:15.243772+00:00
-- url     : https://prove2.me/theorems/c7307258-41e2-4ff3-ae7c-93283088533d
-- title:
--   Bennett Pole Series
-- statement:
--   The formal inverse-power expansion around a nonzero pole displacement. The named objects in this bundle include `bennettPoleSeries`.
-- source:
--   D1Bound5/BennettPoleSeries.lean, lines 10-12, SHA-256 d467fe1ce7d532a4e4fe7ebbe139b749331fe498c06b5ac2897ed0a4d7fa6354. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
open PowerSeries

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

/-- The formal inverse-power expansion around a nonzero pole displacement. -/
noncomputable def bennettPoleSeries (d : F) (k : ℕ) : PowerSeries F :=
  PowerSeries.C ((d⁻¹) ^ k) * rescale d⁻¹ (binomialSeries F (-(k : F)))







end D1Bound5
end


