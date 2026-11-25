-- Prove2me | solution 1 for Arxiv2003_13288.inverse_transmittance_slope
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:22:25.044821+00:00
-- url     : https://prove2.me/submissions/d1f8b4a5-833f-4c87-8a2c-ba94a3bbe03a

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology
open Arxiv2003_13288

lemma inv_T (ltr Rbar L : ℝ) (hltr : 0 < ltr) (hR : 0 ≤ Rbar) (hL : 0 < L) :
    (ohmTransmittance ltr (extrapLength Rbar ltr) L)⁻¹ =
      (L + 2 * extrapLength Rbar ltr) / (ltr + extrapLength Rbar ltr) := by
  unfold ohmTransmittance
  rw [inv_div]

theorem solution (ltr Rbar : ℝ) (hltr : 0 < ltr) (hR : 0 ≤ Rbar) :
    (∀ L : ℝ, 0 < L →
      (ohmTransmittance ltr (extrapLength Rbar ltr) L)⁻¹ =
        L / (ltr + extrapLength Rbar ltr) + 2 * extrapLength Rbar ltr / (ltr + extrapLength Rbar ltr)) ∧
    (∀ L1 L2 : ℝ, 0 < L1 → 0 < L2 → L1 ≠ L2 →
      ((ohmTransmittance ltr (extrapLength Rbar ltr) L2)⁻¹ -
          (ohmTransmittance ltr (extrapLength Rbar ltr) L1)⁻¹) / (L2 - L1) =
        1 / (ltr * (1 + 2 * Rbar / 3)) ∧
      ltr = (L2 - L1) / ((1 + 2 * Rbar / 3) *
        ((ohmTransmittance ltr (extrapLength Rbar ltr) L2)⁻¹ -
          (ohmTransmittance ltr (extrapLength Rbar ltr) L1)⁻¹))) := by
  have hze : 0 ≤ extrapLength Rbar ltr := by unfold extrapLength; positivity
  have hden : ltr + extrapLength Rbar ltr = ltr * (1 + 2 * Rbar / 3) := by
    unfold extrapLength; ring
  have hpos : 0 < ltr * (1 + 2 * Rbar / 3) := by positivity
  have hc : 0 < 1 + 2 * Rbar / 3 := by positivity
  refine ⟨fun L hL => ?_, fun L1 L2 h1 h2 h12 => ?_⟩
  · rw [inv_T ltr Rbar L hltr hR hL, add_div]
  · rw [inv_T ltr Rbar L2 hltr hR h2, inv_T ltr Rbar L1 hltr hR h1, hden]
    have hd : L2 - L1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have hl : ltr ≠ 0 := hltr.ne'
    have hc' : (1 + 2 * Rbar / 3) ≠ 0 := hc.ne'
    have hs : (L2 + 2 * extrapLength Rbar ltr) / (ltr * (1 + 2 * Rbar / 3)) -
        (L1 + 2 * extrapLength Rbar ltr) / (ltr * (1 + 2 * Rbar / 3)) =
        (L2 - L1) / (ltr * (1 + 2 * Rbar / 3)) := by ring
    rw [hs]
    constructor
    · field_simp
    · field_simp

