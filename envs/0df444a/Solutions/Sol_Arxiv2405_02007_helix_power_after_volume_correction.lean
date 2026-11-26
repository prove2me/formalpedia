-- Prove2me | solution 1 for Arxiv2405_02007.helix_power_after_volume_correction
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:36:06.590624+00:00
-- url     : https://prove2.me/submissions/15363164-f89a-48bc-b769-7f42224cbea6

import Mathlib
import Definitions.Def_Arxiv2405_02007_Basic

set_option autoImplicit false

open Arxiv2405_02007 in
theorem solution (span m tau m' dPv : ℝ) (hspan : 0 < span)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (h11 : volumePower m' span = volumePower m span + dPv) :
    helixPower m' span tau = helixPower m span tau * (1 - dPv / (span - volumePower m span)) ∧
    (0 < helixPower m span tau →
      (dPv < 0 → helixPower m span tau < helixPower m' span tau) ∧
      (0 < dPv → helixPower m' span tau < helixPower m span tau)) := by
  unfold volumePower at h11
  unfold helixPower volumePower
  have hms : 0 < m * span := mul_pos hm0 hspan
  have hm' : m' * span = m * span - dPv := by linarith
  have hd : span - (1 - m) * span = m * span := by ring
  rw [hd]
  refine ⟨?_, ?_⟩
  · rw [hm']; field_simp
  · intro hpos
    have hs : 0 < Real.sin (2 * tau) := by
      have := hpos; rw [mul_assoc] at this
      exact pos_of_mul_pos_right this hm0.le |> fun h => (pos_of_mul_pos_right h hspan.le)
    have e : m' * span * Real.sin (2 * tau) = m * span * Real.sin (2 * tau) - dPv * Real.sin (2 * tau) := by
      rw [hm']; ring
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [e]; nlinarith
    · rw [e]; nlinarith
