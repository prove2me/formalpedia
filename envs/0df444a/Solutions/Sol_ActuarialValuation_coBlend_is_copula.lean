-- Prove2me | solution 1 for ActuarialValuation.coBlend_is_copula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:25:08.031727+00:00
-- url     : https://prove2.me/submissions/f6f2f710-7178-4486-97a9-02d196163dbb

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coBlend
import Definitions.Def_actuarial_coIsCopula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (alpha : ℝ) (ha : 0≤alpha) (hb : alpha≤1) (C D : ℝ → ℝ → ℝ) (hC : coIsCopula C) (hD : coIsCopula D) : coIsCopula (coBlend alpha C D) := by
  rcases hC with ⟨hCm, hCr⟩
  rcases hD with ⟨hDm, hDr⟩
  constructor
  · intro u hu0 hu1
    rcases hCm u hu0 hu1 with ⟨hc0, hcL, hc1, hcR⟩
    rcases hDm u hu0 hu1 with ⟨hd0, hdL, hd1, hdR⟩
    constructor
    · simp [coBlend, hc0, hd0]
    constructor
    · simp [coBlend, hcL, hdL]
    constructor
    · simp [coBlend, hc1, hd1]; ring
    · simp [coBlend, hcR, hdR]; ring
  · intro u1 u2 v1 v2 hu1 hu2 hu3 hv1 hv2 hv3
    have hlin : coRectangle (coBlend alpha C D) u1 u2 v1 v2 =
      alpha * coRectangle C u1 u2 v1 v2 +
      (1-alpha) * coRectangle D u1 u2 v1 v2 := by
      unfold coRectangle coBlend
      ring
    rw [hlin]
    exact add_nonneg
      (mul_nonneg ha (hCr u1 u2 v1 v2 hu1 hu2 hu3 hv1 hv2 hv3))
      (mul_nonneg (sub_nonneg.mpr hb)
        (hDr u1 u2 v1 v2 hu1 hu2 hu3 hv1 hv2 hv3))
