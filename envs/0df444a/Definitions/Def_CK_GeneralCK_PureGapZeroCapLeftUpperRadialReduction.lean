-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperRadialReduction
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperRadialReduction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:38:29.020846+00:00
-- url     : https://prove2.me/theorems/5338693b-da6f-463c-a2de-2a0ea447dc6a
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperRadialReduction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperRadialReduction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperRadialReduction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperRadialReduction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperRadialReduction.lean)

import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperRadialReduction =====
section

/-!
# Exact radial form of the zero-cutoff left-upper cap value

The left-upper cap face has second mean (1/2).  Writing the two entropy
coordinates as (H a,H b) removes both entropy inverses from its value.
The identity below retains the actual radial contact function `F`.
-/

namespace GeneralCK

/-- The exact left-upper cap value on the strict lower-half mean chamber.
Here `h` is the average entropy.  No sign premise is used. -/
theorem canonicalPureGap_leftUpper_radial_eq {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1 / 2) :
    canonicalPureGap a (1 / 2) (H a) (H b) =
      interiorCost a b +
        2 * F (1 / 2 - a) ((H a + H b) / 2) -
        F (b - a) ((H a + H b) / 2) -
        eta ((H a + H b) / 2) + eta (H b) / 2 := by
  have haHalf : a ≤ 1 / 2 := (hab.trans hb).le
  have hbHalf : b ≤ 1 / 2 := hb.le
  have hleft : radialPhi (1 - 2 * a) (H a) = 0 := by
    simpa [radialPhi, phi, abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * a)]
      using phi_at_entropy_cap ha haHalf
  have hright : radialPhi (1 - 2 * (1 / 2 : ℝ)) (H b) = eta (H b) := by
    simp [radialPhi, F]
  have hcorr : entropyCorrection (H a) (H b) =
      interiorCost a b - F (b - a) ((H a + H b) / 2) := by
    simp only [entropyCorrection, atomCorrection,
      entropyInverse_H_lower ha.le haHalf,
      entropyInverse_H_lower (ha.trans hab).le hbHalf]
    rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
    ring
  rw [canonicalPureGap, hcorr, hleft, hright, radialPhi]
  ring

/-- This exact two-mean inequality is sufficient for the zero-cutoff
left-upper residual field; it can be checked by a future analytic or finite
certificate owner without inverses inside the inequality. -/
def ZeroCapLeftUpperRadialSign : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 / 2 →
    eta ((H a + H b) / 2) ≤
      interiorCost a b +
        2 * F (1 / 2 - a) ((H a + H b) / 2) -
        F (b - a) ((H a + H b) / 2) + eta (H b) / 2

theorem zeroCap_leftUpper_of_radialSign
    (h : ZeroCapLeftUpperRadialSign) :
    ∀ e f, 0 < e → e < f → f < 1 →
      0 ≤ canonicalPureGap (entropyInverse e) (1 / 2) e f := by
  intro e f he hef hf
  have he1 : e ≤ 1 := (hef.trans hf).le
  have hf0 : 0 < f := he.trans hef
  have hie := entropyInverse_spec he.le he1
  have hif := entropyInverse_spec hf0.le hf.le
  have ha : 0 < entropyInverse e := entropyInverse_pos he he1
  have hab : entropyInverse e < entropyInverse f :=
    entropyInverse_strictMonoOn ⟨he.le, he1⟩ ⟨hf0.le, hf.le⟩ hef
  have hb : entropyInverse f < 1 / 2 := entropyInverse_lt_half hf0.le hf
  have hsign := h (entropyInverse e) (entropyInverse f) ha hab hb
  have hval : 0 ≤ canonicalPureGap (entropyInverse e) (1 / 2)
      (H (entropyInverse e)) (H (entropyInverse f)) := by
    rw [canonicalPureGap_leftUpper_radial_eq ha hab hb]
    linarith
  simpa only [hie.2.2, hif.2.2] using hval

#print axioms canonicalPureGap_leftUpper_radial_eq
#print axioms zeroCap_leftUpper_of_radialSign

end GeneralCK

end


