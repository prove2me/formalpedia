-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_NNReal_F000
-- name    : BrownianMotion_Auxiliary_NNReal_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:05:48.916212+00:00
-- url     : https://prove2.me/theorems/c83c0978-5b9a-47fc-ac05-bb49855beb96
-- title:
--   Source declarations: BrownianMotion.Auxiliary.NNReal
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.NNReal, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Data.NNReal.Basic


@[expose] public section

namespace NNReal

set_option backward.isDefEq.respectTransparency false in
lemma add_sub_two_mul_min_eq_max (s t : ℝ≥0) : s + t - 2 * min s t = max (s - t) (t - s) := by
  wlog hst : s ≤ t
  · convert this t s (le_of_not_ge hst) using 1
    · rw [add_comm, min_comm]
    · rw [max_comm]
  rw [min_eq_left hst, max_eq_right, two_mul, add_tsub_add_eq_tsub_left]
  grw [hst]
end NNReal


