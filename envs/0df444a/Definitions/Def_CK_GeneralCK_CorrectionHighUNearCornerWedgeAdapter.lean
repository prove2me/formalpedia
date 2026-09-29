-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerWedgeAdapter
-- name    : CK_GeneralCK_CorrectionHighUNearCornerWedgeAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:53:54.950055+00:00
-- url     : https://prove2.me/theorems/80f79cba-bbcd-47e7-874c-6caead349ddd
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerWedgeAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerWedgeAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerWedgeAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerWedgeAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerWedgeAdapter.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerWedgeTarget

/-!
The source-only wedge certificate target implies quantitative scaled margins.
The theorem remains conditional on the two raw wedge inequalities.
-/

namespace GeneralCK.Correction.HighU

theorem nearCorner_scaled_margins_of_raw_wedges
    (h : NearCornerRawWedgeTarget) {t rho : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    (1 / 2 : ℝ) ≤
      Natural.m11 (1 / 2 - t) (1 / 2 - (1 - rho) * t) / t ^ 2 ∧
    (1 : ℝ) ≤
      Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t) /
        (rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2)) := by
  obtain ⟨hm, hkSmall, hkLarge⟩ := h t rho ht ht1 hr hr1
  have ht2 : 0 < t ^ 2 := by positivity
  have hden : 0 < rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) := by positivity
  constructor
  · apply (le_div_iff₀ ht2).2
    nlinarith only [hm]
  · apply (le_div_iff₀ hden).2
    rcases le_total rho t with hrt | htr
    · have hsq : rho ^ 2 ≤ t ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hrt)
          (add_nonneg ht.le hr.le)]
      have hsum : t ^ 2 + rho ^ 2 ≤ t ^ 2 + t ^ 2 :=
        by simpa [add_comm] using add_le_add_left hsq (t ^ 2)
      have hfactor : 0 ≤ rho ^ 2 * t ^ 7 := by positivity
      have hdenBound := mul_le_mul_of_nonneg_left hsum hfactor
      have hdenBound' :
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) ≤
            2 * rho ^ 2 * t ^ 9 := by
        calc
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2)
              ≤ rho ^ 2 * t ^ 7 * (t ^ 2 + t ^ 2) := hdenBound
          _ = 2 * rho ^ 2 * t ^ 9 := by ring
      simpa only [one_mul] using hdenBound'.trans (hkSmall hrt)
    · have hsq : t ^ 2 ≤ rho ^ 2 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr htr)
          (add_nonneg ht.le hr.le)]
      have hsum : t ^ 2 + rho ^ 2 ≤ rho ^ 2 + rho ^ 2 :=
        by simpa [add_comm] using add_le_add_right hsq (rho ^ 2)
      have hfactor : 0 ≤ rho ^ 2 * t ^ 7 := by positivity
      have hdenBound := mul_le_mul_of_nonneg_left hsum hfactor
      have hdenBound' :
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2) ≤
            2 * rho ^ 4 * t ^ 7 := by
        calc
          rho ^ 2 * t ^ 7 * (t ^ 2 + rho ^ 2)
              ≤ rho ^ 2 * t ^ 7 * (rho ^ 2 + rho ^ 2) := hdenBound
          _ = 2 * rho ^ 4 * t ^ 7 := by ring
      simpa only [one_mul] using hdenBound'.trans (hkLarge htr)

#print axioms nearCorner_scaled_margins_of_raw_wedges

end GeneralCK.Correction.HighU


