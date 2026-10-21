-- Prove2me | solution 2 for AddictivePlatforms.Compete.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:36:03.676237+00:00
-- url     : https://prove2.me/submissions/436c2056-c3c4-444e-a379-a0d1e0d55b62

import Mathlib
set_option autoImplicit false
open Set

theorem solution (u : ℝ → ℝ) (hmono : MonotoneOn u (Ici 0))
    (hconc : StrictConcaveOn ℝ (Ici 0) u) (hdiff : DifferentiableOn ℝ u (Ici 0)) :
    StrictMonoOn (fun x => u x - x * derivWithin u (Ici 0) x) (Ici 0) := by
  intro x hx y hy hxy
  have hfc : StrictConvexOn ℝ (Ici (0:ℝ)) (-u) := hconc.neg
  have hxy' : x < y := hxy
  have hx0 : (0:ℝ) ≤ x := hx
  have hdx : HasDerivWithinAt (-u) (-derivWithin u (Ici 0) x) (Ici 0) x :=
    ((hdiff x hx).hasDerivWithinAt).neg
  have hdy : HasDerivWithinAt (-u) (-derivWithin u (Ici 0) y) (Ici 0) y :=
    ((hdiff y hy).hasDerivWithinAt).neg
  have A := hfc.lt_slope_of_hasDerivWithinAt hx hy hxy' hdx
  have B := hfc.slope_lt_of_hasDerivWithinAt hx hy hxy' hdy
  have hne : y - x ≠ 0 := by linarith
  simp only [slope_def_field, Pi.neg_apply] at A B
  set a := derivWithin u (Ici 0) x
  set b := derivWithin u (Ici 0) y
  have hpos : 0 < y - x := by linarith
  have A' : (u y - u x) < a * (y - x) := by
    have : -a < (-u y - -u x) / (y - x) := A
    rw [lt_div_iff₀ hpos] at this; linarith
  have B' : b * (y - x) < (u y - u x) := by
    have : (-u y - -u x) / (y - x) < -b := B
    rw [div_lt_iff₀ hpos] at this; linarith
  show u x - x * a < u y - y * b
  have hy0 : 0 < y := by linarith
  nlinarith [mul_nonneg hx0 (sub_nonneg.2 (le_of_lt (show b < a by nlinarith))), mul_pos hy0 hpos]
