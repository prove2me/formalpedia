-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiCompactCoordinates
-- name    : CK_GeneralCK_SmallBoundaryPhiCompactCoordinates
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:52:57.633979+00:00
-- url     : https://prove2.me/theorems/b52593cb-c1a4-405d-be70-6ee89e3c8590
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiCompactCoordinates` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiCompactCoordinates` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiCompactCoordinates` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiCompactCoordinates (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiCompactCoordinates.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiCompactTransport
import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiTailCoordinates

-- ===== source module GeneralCK.SmallBoundaryPhiCompactCoordinates =====
section

/-! Inclusive logarithmic-coordinate bounds on the compact owner's interval. -/

namespace GeneralCK.SmallBoundaryPhiSchur

open SmallMeanPhiCutoff

theorem compactDelta_pos : 0 < compactDelta := by norm_num [compactDelta]

theorem compactDelta_le_retainedCutoff : compactDelta ≤ retainedCutoff := by
  norm_num [compactDelta, retainedCutoff]

theorem compact_coordinates_box {t : ℝ} (ht : 0 < t) (htu : t ≤ retainedCutoff) :
    t ≤ 1/10000 ∧ 0 < tailZ t ∧ tailZ t ≤ 1/9 ∧
    0 ≤ tailB t-1 ∧ tailB t-1 ≤ 1/9999 := by
  have ht1 : t < 1 := by dsimp [retainedCutoff] at htu; linarith
  have hc : 0 < 1-t := by linarith
  have hi : (2:ℝ)^13 ≤ t⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ ht).mpr
    exact (mul_le_mul_of_nonneg_left htu (by positivity)).trans (by norm_num [retainedCutoff])
  have hl := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^13) hi
  rw [Real.log_pow, Real.log_inv] at hl
  norm_num at hl
  have hL : (693/1000:ℝ) ≤ Real.log 2 := by
    have hs := Certificates.PilotData.log_two.1
    norm_num at hs
    linarith
  have hx : 9 ≤ -Real.log t := by linarith
  have hz := tailZ_pos ht ht1
  have hzU : tailZ t ≤ 1/9 := one_div_le_one_div_of_le (by norm_num) hx
  have hb := tailB_bounds ht ht1
  have hbU : 1/(1-t) ≤ 10000/9999 := by
    apply (div_le_iff₀ hc).mpr
    dsimp [retainedCutoff] at htu
    linarith
  exact ⟨htu,hz,hzU,by linarith [hb.1],by linarith [hb.2]⟩

#print axioms compactDelta_pos
#print axioms compactDelta_le_retainedCutoff
#print axioms compact_coordinates_box

end GeneralCK.SmallBoundaryPhiSchur

end


