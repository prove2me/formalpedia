-- Prove2me | Definitions.Def_CK_CKLaneP_SeamFinal
-- name    : CK_CKLaneP_SeamFinal
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T22:01:49.670286+00:00
-- url     : https://prove2.me/theorems/0a206091-bc95-4aa8-965e-262b89e7e424
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamFinal` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamFinal` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamFinal` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamFinal (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamFinal.lean)

import Definitions.Def_CK_CKLaneP_SeamFinal_q100

set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
/-- The seam field (with the cutoff unfolded) from the root box. -/
theorem seam_exclusion_of_box (hbox : SeamBox 0 (1 / 20000) 0 2) :
    StrictSeamMinimizerExclusion (1 / 10000) := by
  intro a c e f he hf hef hmem hsum hac hc hea hfc hres hneg
  obtain ⟨⟨ha0, -, hc12, -, -⟩, -⟩ := hmem
  have hHmono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → y ≤ 1 / 2 → H x ≤ H y :=
    fun hx hxy hy => H_strictMonoOn.monotoneOn ⟨hx, by linarith⟩ ⟨hx.trans hxy, hy⟩ hxy
  have he1 : e ≤ 1 := le_trans hea.le (H_le_one a)
  have hf1 : f ≤ 1 := le_trans hfc.le (H_le_one c)
  obtain ⟨hp0, hp12, hHp⟩ := entropyInverse_spec he.le he1
  obtain ⟨hq0, hq12, hHq⟩ := entropyInverse_spec hf.le hf1
  set p := entropyInverse e with hpdef
  set q := entropyInverse f with hqdef
  have hp : 0 < p := entropyInverse_pos he he1
  have hpa : p < a := by
    by_contra hcon
    push Not at hcon
    have := hHmono ha0 hcon hp12
    rw [hHp] at this
    linarith
  have hqc : q < c := by
    by_contra hcon
    push Not at hcon
    have := hHmono (ha0.trans hac.le) hcon hq12
    rw [hHq] at this
    linarith
  have hpq : p < q := by
    by_contra hcon
    push Not at hcon
    have := hHmono hq0 hcon hp12
    rw [hHp, hHq] at this
    linarith
  set ys := c - a with hys
  have hys0 : 0 < ys := by rw [hys]; linarith
  have hysq : 2 * q - 1 / 10000 < ys := by rw [hys]; linarith
  have hysS : ys < 1 / 10000 - 2 * p := by rw [hys]; linarith
  have hstat : seamD (1 / 10000) (H p) (H q) ys = 0 := by
    rw [hHp, hHq]
    have e1 : 1 - 1 / 10000 + ys = 1 - 2 * a := by rw [hys]; linarith
    have e2 : 1 - 1 / 10000 - ys = 1 - 2 * c := by rw [hys]; linarith
    unfold seamD
    rw [e1, e2]
    linarith
  have hbox' := hbox p q hp hpq (by push_cast; exact hp.le) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) ys hys0 hysq hysS hstat
  have hcurve : seamCurve (1 / 10000) (H p) (H q) ys = canonicalPureGap a c e f := by
    unfold seamCurve
    rw [hHp, hHq]
    have e1 : (1 / 10000 - ys) / 2 = a := by rw [hys]; linarith
    have e2 : (1 / 10000 + ys) / 2 = c := by rw [hys]; linarith
    rw [e1, e2]
  rw [hcurve] at hbox'
  linarith

end CKLaneP


