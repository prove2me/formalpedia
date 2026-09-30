-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryAfterNarrowMiddle
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryAfterNarrowMiddle
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:01:30.364223+00:00
-- url     : https://prove2.me/theorems/411ae3f6-0532-4114-9e43-d2ec60a8743d
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryAfterNarrowMiddle` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryAfterNarrowMiddle` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryAfterNarrowMiddle` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryAfterNarrowMiddle (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryAfterNarrowMiddle.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryNarrowMiddleCertified

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryAfterNarrowMiddle =====
section

/-! Exact residual stationary owner after the accepted narrow exclusion. -/

namespace GeneralCK

def LeftStationaryOutsideNarrowMiddleOwner : Prop :=
  ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
    entropyInverse f < c → c < 1 / 2 →
    deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
    ¬ ((1 / 8 : ℝ) ≤ entropyInverse e ∧
      entropyInverse e ≤ 129 / 1024 ∧
      129 / 1024 ≤ entropyInverse f ∧
      entropyInverse f ≤ 65 / 512 ∧
      1 / 4 ≤ c ∧ c ≤ 5 / 16) →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem leftStationary_of_outsideNarrowMiddle
    (h : LeftStationaryOutsideNarrowMiddleOwner) :
    ∀ e f c : ℝ, 0 < e → e < f → f < 1 →
      entropyInverse f < c → c < 1 / 2 →
      deriv (fun y => canonicalPureGap (entropyInverse e) y e f) c = 0 →
      0 ≤ canonicalPureGap (entropyInverse e) c e f := by
  intro e f c he hef hf hfc hc hstation
  by_cases hbox : (1 / 8 : ℝ) ≤ entropyInverse e ∧
      entropyInverse e ≤ 129 / 1024 ∧
      129 / 1024 ≤ entropyInverse f ∧
      entropyInverse f ≤ 65 / 512 ∧
      1 / 4 ≤ c ∧ c ≤ 5 / 16
  · have he1 : e ≤ 1 := (hef.trans hf).le
    have hf0 : 0 ≤ f := (he.trans hef).le
    have hie := entropyInverse_spec he.le he1
    have hif := entropyInverse_spec hf0 hf.le
    have hnot := ZeroCapLeftStationaryNarrowMiddleCertified.no_left_stationary_in_narrow_middle
      hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2.1 hbox.2.2.2.2.1 hbox.2.2.2.2.2
    rw [hie.2.2, hif.2.2] at hnot
    exact False.elim (hnot hstation)
  · exact h e f c he hef hf hfc hc hstation hbox

#print axioms leftStationary_of_outsideNarrowMiddle

end GeneralCK

end


