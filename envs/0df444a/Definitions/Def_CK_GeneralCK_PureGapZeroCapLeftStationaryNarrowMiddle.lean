-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryNarrowMiddle
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryNarrowMiddle
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:57:28.08996+00:00
-- url     : https://prove2.me/theorems/69be1126-3f36-4617-a3b8-6c2689020937
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddle` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddle` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddle` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddle (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryNarrowMiddle.lean)

import Definitions.Def_CK_GeneralCK_PureGapMiddleDeterministic

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryNarrowMiddle =====
section

/-! Conditional exact-rational narrow-middle left-stationary exclusion.
The three `e8Theta` endpoint witnesses are explicit premises until they
have been produced and audited in Lean. No numerical sample is used as proof. -/

namespace GeneralCK
namespace ZeroCapLeftStationaryNarrowMiddle

theorem derivative_positive_of_three_theta_anchors {a b c : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 129 / 1024)
    (hb : 129 / 1024 ≤ b) (hb' : b ≤ 65 / 512)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 5 / 16)
    (hElower : 323 / 300 ≤ H a + H b)
    (hEupper : H a + H b ≤ 57 / 50)
    (hBupper : H b ≤ 57 / 100)
    (hT1 : 121 / 100 ≤ e8Theta (3175 / 29184))
    (hT2 : 3 ≤ e8Theta (25 / 76))
    (hT3 : e8Theta (375 / 646) ≤ 417 / 100) :
    1 / 25 ≤ deriv (fun y => canonicalPureGap a y (H a) (H b)) c := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hac : a < c := by linarith
  have hcHalf : c < 1 / 2 := by linarith
  have hsum : a + c < 1 := by linarith
  have hHa : 0 < H a := H_pos ha0 (by linarith)
  have hHb : 0 < H b := H_pos hb0 (by linarith)
  let E : ℝ := H a + H b
  let U : ℝ := (c - a) / E
  let V : ℝ := (1 - a - c) / E
  let W : ℝ := (1 - 2 * c) / (2 * H b)
  have hE : 0 < E := by dsimp [E]; linarith
  have hUpos : 0 < U := by dsimp [U]; exact div_pos (by linarith) hE
  have hVpos : 0 < V := by dsimp [V]; exact div_pos (by linarith) hE
  have hWpos : 0 < W := by dsimp [W]; exact div_pos (by linarith) (mul_pos two_pos hHb)
  have hU : 3175 / 29184 ≤ U := by
    dsimp [U]
    apply (le_div_iff₀ hE).2
    dsimp [E] at *
    linarith
  have hV : V ≤ 375 / 646 := by
    dsimp [V]
    apply (div_le_iff₀ hE).2
    dsimp [E] at *
    linarith
  have hW : 25 / 76 ≤ W := by
    dsimp [W]
    apply (le_div_iff₀ (mul_pos two_pos hHb)).2
    linarith
  have hThetaU : e8Theta (3175 / 29184) ≤ e8Theta U :=
    strictMonoOn_e8Theta_pos.monotoneOn (by norm_num) hUpos hU
  have hThetaV : e8Theta V ≤ e8Theta (375 / 646) :=
    strictMonoOn_e8Theta_pos.monotoneOn hVpos (by norm_num) hV
  have hThetaW : e8Theta (25 / 76) ≤ e8Theta W :=
    strictMonoOn_e8Theta_pos.monotoneOn (by norm_num) hWpos hW
  have hDeriv : deriv (fun y => canonicalPureGap a y (H a) (H b)) c =
      e8Theta U - e8Theta V + e8Theta W := by
    rw [deriv_canonicalPureGap_right hac hsum hcHalf hHa hHb,
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) (by linarith),
      deriv_F_radius_eq_e8Theta (by linarith) hHb]
    congr 1 <;> dsimp [U, V, W, E] <;> field_simp <;> ring
  rw [hDeriv]
  linarith only [hT1, hT2, hT3, hThetaU, hThetaV, hThetaW]

theorem no_stationary_of_three_theta_anchors {a b c : ℝ}
    (ha : 1 / 8 ≤ a) (ha' : a ≤ 129 / 1024)
    (hb : 129 / 1024 ≤ b) (hb' : b ≤ 65 / 512)
    (hc : 1 / 4 ≤ c) (hc' : c ≤ 5 / 16)
    (hElower : 323 / 300 ≤ H a + H b)
    (hEupper : H a + H b ≤ 57 / 50)
    (hBupper : H b ≤ 57 / 100)
    (hT1 : 121 / 100 ≤ e8Theta (3175 / 29184))
    (hT2 : 3 ≤ e8Theta (25 / 76))
    (hT3 : e8Theta (375 / 646) ≤ 417 / 100) :
    deriv (fun y => canonicalPureGap a y (H a) (H b)) c ≠ 0 := by
  have hp := derivative_positive_of_three_theta_anchors ha ha' hb hb' hc hc'
    hElower hEupper hBupper hT1 hT2 hT3
  linarith

end ZeroCapLeftStationaryNarrowMiddle

#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddle.derivative_positive_of_three_theta_anchors
#print axioms GeneralCK.ZeroCapLeftStationaryNarrowMiddle.no_stationary_of_three_theta_anchors

end GeneralCK

end


