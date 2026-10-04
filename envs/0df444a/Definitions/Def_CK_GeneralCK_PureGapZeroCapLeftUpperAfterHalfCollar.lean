-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperAfterHalfCollar
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperAfterHalfCollar
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T17:26:13.56287+00:00
-- url     : https://prove2.me/theorems/d2e381b2-2808-4f06-b3d2-7bf4a9ffbe08
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollar` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollar` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollar` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollar (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperAfterHalfCollar.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarC600Actual

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperAfterHalfCollar =====
section

/-!
Exact remaining left-upper probability chamber after the accepted half-collar.
The outside sign remains an explicit analytic/certificate premise.
-/

namespace GeneralCK

def LeftUpperOutsideHalfCollarOwner : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 / 2 → a < 31 / 64 →
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b)

theorem leftUpper_probability_of_outsideHalfCollar
    (h : LeftUpperOutsideHalfCollarOwner) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    0 ≤ canonicalPureGap a (1 / 2) (H a) (H b) := by
  by_cases ha31 : (31 / 64 : ℝ) ≤ a
  · let z : ℝ := 1 / 2 - a
    let lambda : ℝ := (1 / 2 - b) / z
    have hz : 0 < z := by dsimp [z]; linarith
    have hzmax : z ≤ 1 / 64 := by dsimp [z]; linarith
    have hw : 0 < 1 / 2 - b := by linarith
    have hwz : 1 / 2 - b < z := by dsimp [z]; linarith
    have hlambda : 0 < lambda := div_pos hw hz
    have hlambda1 : lambda < 1 := (div_lt_one hz).2 hwz
    have hza : 1 / 2 - z = a := by dsimp [z]; ring
    have hzb : 1 / 2 - lambda * z = b := by
      dsimp [lambda]
      rw [div_mul_cancel₀ _ hz.ne']
      ring
    have hp := leftUpper_halfCollar_positive_unconditional
      hz hzmax hlambda hlambda1
    rw [hza, hzb] at hp
    exact hp.le
  · exact h a b ha hab hb (lt_of_not_ge ha31)

theorem zeroCap_leftUpper_of_outsideHalfCollar
    (h : LeftUpperOutsideHalfCollarOwner) :
    ∀ e f, 0 < e → e < f → f < 1 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f := by
  have hsign : ZeroCapLeftUpperRadialSign := by
    intro a b ha hab hb
    have hp := leftUpper_probability_of_outsideHalfCollar h ha hab hb
    rw [canonicalPureGap_leftUpper_radial_eq ha hab hb] at hp
    linarith
  exact zeroCap_leftUpper_of_radialSign hsign

#print axioms leftUpper_probability_of_outsideHalfCollar
#print axioms zeroCap_leftUpper_of_outsideHalfCollar

end GeneralCK

end


