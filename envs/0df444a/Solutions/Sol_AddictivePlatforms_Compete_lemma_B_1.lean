-- Prove2me | solution 1 for AddictivePlatforms.Compete.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T10:29:45.104602+00:00
-- url     : https://prove2.me/submissions/76efa0d2-e39a-4d77-add7-63e83f8e60ca

import Mathlib

open Set

-- Ichihashi and Kim, Addictive Platforms (2022-04-01), Lemma B.1, p. 28.
-- Alexander Richard Towell directed; OpenAI Codex formalized the source argument.
-- Mathlib supplies the strict secant-slope and derivative-monotonicity results.
theorem solution (u : ℝ → ℝ) (hmono : MonotoneOn u (Ici 0))
    (hconc : StrictConcaveOn ℝ (Ici 0) u) (hdiff : DifferentiableOn ℝ u (Ici 0)) :
    StrictMonoOn (fun x => u x - x * derivWithin u (Ici 0) x) (Ici 0) := by
  intro x hx y hy hxy
  have hs := hconc.derivWithin_lt_slope hx hy hxy (hdiff y hy)
  rw [slope_def_field] at hs
  have hs' := (lt_div_iff₀ (sub_pos.mpr hxy)).mp hs
  have hd := (hconc.strictAntiOn_derivWithin hdiff hx hy hxy).le
  have hm := mul_le_mul_of_nonneg_left hd hx
  nlinarith
