-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWKCheck_h00
-- name    : CK_CKLaneP_SeamWKCheck_h00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T09:51:35.779126+00:00
-- url     : https://prove2.me/theorems/943c43e7-e397-4133-a0da-9ca5254c21ce
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWKCheck (proof part 1 of 7)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWKCheck (proof part 1 of 7)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWKCheck (proof part 1 of 7)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWKCheck (proof part 1 of 7) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWKCheck (proof part 1 of 7).lean)

import Definitions.Def_CK_CKLaneP_SeamWKCheck_part00

/-
Lane P — the W-mode seam cell checker with the slope-gap dip (WK), case A (`0 < t0 < t1 ≤ 1`).

Same base as `wcheckA` (DC ≥ β_lo²·max(0, DCraw), right fiber, bulk).  The dip uses the exact K-bound
`s(y*) ≥ s(0) − dipK(E, y*)`, `dipK(E, y) = y·(radialSlope v − J v)` at the contact `v` of `y/E`
(`dipK_eq`), with
* `y*/E ≥ xK`: `Θ(y*/E) = Δ(y*) ≥ (Pmin/2)·log(f/e) > Shi(nxK) ≥ Θ(xK)`;
* `v ≤ v(nvK)` (contact bracket at `xK`), so `radialSlope v − J v ≤ (1 + 1/a1(nvK))/log 2`;
* `v ≥ v(nvH)` (contact bracket at `Yv/E_lo`), so also `radialSlope v − J v ≤ Shi(nvH) − Jlo(nvK)`
  (`radialSlope` and `J` are antitone);
* `y* ≤ Yv` (the stationary-point bound of `wcheckA`).
This is much sharper than `M·Y²/(2E)` when `y*/E` is not small (Θ concave and saturating).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

set_option maxHeartbeats 4000000 in
theorem wcheckK_sound_hDC (hdouble : CanonicalDoubleCapEntropyEndpoints) (c : WCell) (xK : ℚ)
    (nxK nvK nvH : ℕ) (hc : wcheckK c xK nxK nvK nvH = true) {p q ys : ℝ}
    (hp0 : ((c.p0 : ℚ) : ℝ) ≤ p) (hp1 : p ≤ ((c.p1 : ℚ) : ℝ))
    (ht0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤ q - p)
    (ht1 : q - p ≤ ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p))
    (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) :
    ((c.DC0 : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
  unfold wcheckK at hc
  obtain ⟨ok0, ok1, okql, okq, okvb, okva, okxb, okx2, hnp0, hnp1, hp0pos, hp01, hp1S,
    ht0pos, ht01, ht1le, hql, hqhi, hqd, ha12, heL, hfL, hJq, hkh1, hvb, hvba1, hXmin, hbrX,
    hVmin, hbrV, hbrW, hvab1, hxb, hxbv, hbrxb, hbrx2, hdhk, hM0, hPmin0, hPminmax, hfl1, hfl2,
    hflA, hflC, hneed, hden, okxK, okvK, hxK, hbrxK, haxK, hvxK, hflK, hshi, hbrvK, hvKa1,
    okvH, hvHh, haH, hbrvH, hfinal⟩ := of_decide_eq_true hc
  have d0 := dy_sound ok0
  have d1 := dy_sound ok1
  have dql := dy_sound okql
  have dq := dy_sound okq
  have dvb := dy_sound okvb
  have dva := dy_sound okva
  have dxb := dy_sound okxb
  have dx2 := dy_sound okx2
  have dh := dy_sound dh_ok
  -- domain
  have hp0R : (0 : ℝ) < ((c.p0 : ℚ) : ℝ) := by exact_mod_cast hp0pos
  have hp : 0 < p := lt_of_lt_of_le hp0R hp0
  have hp1SR : ((c.p1 : ℚ) : ℝ) ≤ 1 / 10000 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hp1S
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have ht0R : (0 : ℝ) < ((c.t0 : ℚ) : ℝ) := by exact_mod_cast ht0pos
  have ht1R : ((c.t1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast ht1le
  have ht1nn : (0 : ℝ) ≤ ((c.t1 : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ c.t1 := le_trans ht0pos.le ht01.le
    exact_mod_cast this
  have hε : 0 < 1 / 10000 / 2 - p := by
    by_contra hcon
    push Not at hcon
    have : q - p ≤ 0 := le_trans ht1 (mul_nonpos_of_nonneg_of_nonpos ht1nn hcon)
    have h2 : 0 ≤ 1 / 10000 / 2 - p := by
      linarith [mul_pos ht0R (show (0 : ℝ) < 1 by norm_num)]
    linarith
  have hβlo : ((c.blo : ℚ) : ℝ) ≤ q - p := by
    have e : ((c.blo : ℚ) : ℝ) = ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
      unfold WCell.blo; push_cast; rw [Sq_cast]
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_left (by linarith) ht0R.le) ht0
  have hblo0 : (0 : ℝ) ≤ ((c.blo : ℚ) : ℝ) := by
    have e : ((c.blo : ℚ) : ℝ) = ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
      unfold WCell.blo; push_cast; rw [Sq_cast]
    rw [e]; exact mul_nonneg ht0R.le (by linarith)
  have hβ0 : 0 < q - p := by
    have := mul_pos ht0R hε
    linarith
  have hbhi : q - p ≤ ((c.bhi : ℚ) : ℝ) := by
    have e : ((c.bhi : ℚ) : ℝ) = ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p0 : ℚ) : ℝ)) := by
      unfold WCell.bhi; push_cast; rw [Sq_cast]
    rw [e]
    exact le_trans ht1 (mul_le_mul_of_nonneg_left (by linarith) ht1nn)
  have hpq : p < q := by linarith
  have hqS : q ≤ 1 / 10000 / 2 := by
    have h1 : q - p ≤ 1 * (1 / 10000 / 2 - p) :=
      le_trans ht1 (mul_le_mul_of_nonneg_right ht1R hε.le)
    linarith
  have hqhiR : ((c.p1 : ℚ) : ℝ) + ((c.bhi : ℚ) : ℝ) ≤ ((c.qd : ℚ) : ℝ) := by exact_mod_cast hqhi
  have hqqd : q ≤ ((c.qd : ℚ) : ℝ) := by linarith
  have hqdR : ((c.qd : ℚ) : ℝ) ≤ 1 / 10000 := by
    have := (Rat.cast_le (K := ℝ)).mpr hqd
    rw [show ((1 / 10000 : ℚ) : ℝ) = 1 / 10000 by norm_num] at this
    exact this
  have hqlR : ((dy c.nql).v : ℝ) ≤ q := by
    rw [dy_v]
    have h := (Rat.cast_le (K := ℝ)).mpr hql
    push_cast at h
    have e : ((c.blo : ℚ) : ℝ) = ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p1 : ℚ) : ℝ)) := by
      unfold WCell.blo; push_cast; rw [Sq_cast]
    have h2 : ((dyq c.nql : ℚ) : ℝ) ≤ ((c.p0 : ℚ) : ℝ) + ((c.blo : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hql
      exact_mod_cast this
    linarith
  have hq0 : 0 < q := by linarith
  -- entropy data
  have hv0 : ((dy c.np0).v : ℝ) ≤ (c.p0 : ℝ) := by rw [dy_v]; exact_mod_cast hnp0
  have hv1 : (c.p1 : ℝ) ≤ ((dy c.np1).v : ℝ) := by rw [dy_v]; exact_mod_cast hnp1
  have hvq : ((dy c.nq).v : ℝ) = (c.qd : ℝ) := by rw [dy_v]; rfl
  have hv00 : (0 : ℝ) < ((dy c.np0).v : ℝ) := by exact_mod_cast d0.1
  have hvl0 : (0 : ℝ) < ((dy c.nql).v : ℝ) := by exact_mod_cast dql.1
  have hv1h : ((dy c.np1).v : ℝ) ≤ 1 / 2 := VD.cast_le_half d1.2.1
  have hHmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 / 2 → H a ≤ H b :=
    fun ha hab hb => H_strictMonoOn.monotoneOn ⟨ha, by linarith⟩ ⟨ha.trans hab, hb⟩ hab
  have heLR : ((c.eL : ℚ) : ℝ) ≤ H p :=
    le_trans (VD.Hlo_le d0) (hHmono hv00.le (hv0.trans hp0) (by linarith))
  have heHR : H p ≤ ((c.eH : ℚ) : ℝ) :=
    le_trans (hHmono hp.le (hp1.trans hv1) hv1h) (VD.le_Hhi d1)
  have hfLR : ((c.fL : ℚ) : ℝ) ≤ H q :=
    le_trans (VD.Hlo_le dql) (hHmono hvl0.le hqlR (by linarith))
  have hfHR : H q ≤ ((c.fH : ℚ) : ℝ) := by
    have h := VD.le_Hhi dq
    rw [hvq] at h
    exact le_trans (hHmono hq0.le hqqd (by linarith)) h
  have hHpq : H p ≤ H q := hHmono hp.le hpq.le (by linarith)
  have hJqR : ((c.Jq : ℚ) : ℝ) ≤ J q := by
    have h := VD.Jlo_le dq
    rw [hvq] at h
    exact le_trans h (J_antitone hq0 (by linarith) hqqd)
  have hrsR : radialSlope p ≤ ((c.rs0 : ℚ) : ℝ) :=
    le_trans (ZeroCapLeftStationaryThetaBracket.radialSlope_antitone ⟨hv00, by linarith⟩
      ⟨hp, by linarith⟩ (hv0.trans hp0)) (VD.le_Shi d0 ha12)
  have heL0 : (0 : ℝ) < ((c.eL : ℚ) : ℝ) := by exact_mod_cast heL
  have hfL0 : (0 : ℝ) < ((c.fL : ℚ) : ℝ) := by exact_mod_cast hfL
  have hJq0 : (0 : ℝ) < ((c.Jq : ℚ) : ℝ) := by exact_mod_cast hJq
  have hHp : 0 < H p := lt_of_lt_of_le heL0 heLR
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have eEL : ((c.EL : ℚ) : ℝ) = ((c.eL : ℚ) : ℝ) + ((c.fL : ℚ) : ℝ) := by
    unfold WCell.EL; push_cast; ring
  have eEH : ((c.EH : ℚ) : ℝ) = ((c.eH : ℚ) : ℝ) + ((c.fH : ℚ) : ℝ) := by
    unfold WCell.EH; push_cast; ring
  have hELR : ((c.EL : ℚ) : ℝ) ≤ H p + H q := by rw [eEL]; linarith
  have hEHR : H p + H q ≤ ((c.EH : ℚ) : ℝ) := by rw [eEH]; linarith
  have hEL0 : (0 : ℝ) < ((c.EL : ℚ) : ℝ) := by rw [eEL]; linarith
  have hEH0 : (0 : ℝ) < ((c.EH : ℚ) : ℝ) := lt_of_lt_of_le hE hEHR
  -- profile brackets
  have hvbv : (dy c.nvb).v ≤ 1 / 1000 := by rw [dy_v]; exact le_trans hvb (by norm_num)
  have hPmaxAll : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x →
      profile (radialContact (2 * x) 1) ≤ ((c.Pmax : ℚ) : ℝ) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx
    exact PmaxQ_sound dvb hvbv hvba1 (radialContact_pos (by linarith) one_pos)
      (contact_le_of_bracket dvb hXmin hbrX hx)
  have hPminAll : ∀ x : ℝ, ((c.Vmin : ℚ) : ℝ) ≤ x → x ≤ ((c.Wmax : ℚ) : ℝ) →
      ((c.Pmin : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1) := by
    intro x hx1 hx2
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hVmin) hx1
    exact PminQ_sound dva dvb hvbv hvba1 hvab1 (contact_ge_of_bracket dva hbrW hx0 hx2)
      (contact_le_of_bracket dvb hVmin hbrV hx1)
  have hPminAllX : ∀ x : ℝ, ((c.Xmin : ℚ) : ℝ) ≤ x → x ≤ ((c.Wmax : ℚ) : ℝ) →
      ((c.Pmin : ℚ) : ℝ) ≤ profile (radialContact (2 * x) 1) := by
    intro x hx1 hx2
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hXmin) hx1
    exact PminQ_sound dva dvb hvbv hvba1 hvab1 (contact_ge_of_bracket dva hbrW hx0 hx2)
      (contact_le_of_bracket dvb hXmin hbrX hx1)
  have hPmin0R : (0 : ℝ) ≤ ((c.Pmin : ℚ) : ℝ) := by exact_mod_cast hPmin0
  have hPminmaxR : ((c.Pmin : ℚ) : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := by exact_mod_cast hPminmax
  have hPmax0R : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) := le_trans hPmin0R hPminmaxR
  have eXmin : ((c.Xmin : ℚ) : ℝ) = (1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ)) /
      (2 * ((c.fH : ℚ) : ℝ)) := by
    unfold WCell.Xmin; push_cast; rw [Sq_cast]
  have eVmin : ((c.Vmin : ℚ) : ℝ) = (1 - 2 * ((c.qd : ℚ) : ℝ)) / ((c.EH : ℚ) : ℝ) := by
    unfold WCell.Vmin; push_cast; ring
  have eWmax : ((c.Wmax : ℚ) : ℝ) = 1 / (2 * ((c.eL : ℚ) : ℝ)) := by
    unfold WCell.Wmax; push_cast; ring
  have hA0 : (0 : ℝ) ≤ 1 - 2 * (1 / 10000) + 2 * ((c.p0 : ℚ) : ℝ) := by linarith
  -- (DC)
  unfold WCell.DC0
  rcases le_total c.DCraw 0 with hneg | hpos
  · rw [max_eq_left hneg, mul_zero]
    have h := canonicalPureGap_doubleCap_nonneg_of_scalar_endpoints hdouble hp hpq.le
      (by linarith : q ≤ 1 / 2)
    push_cast
    linarith
  · rw [max_eq_right hpos]
    have h := dc_cell_lower (p0 := ((c.p0 : ℚ) : ℝ)) (p1 := ((c.p1 : ℚ) : ℝ))
      (βhi := ((c.bhi : ℚ) : ℝ)) (Jq := ((c.Jq : ℚ) : ℝ)) (rs0 := ((c.rs0 : ℚ) : ℝ))
      (l2hi := ((L2hiD : ℚ) : ℝ)) (l2lo := ((L2loD : ℚ) : ℝ)) hp0R hp0 hp1 hpq
      (by linarith) hbhi hJqR hJq0 hrsR log2D_bounds.2 log2D_bounds.1 VD.L2lo_pos
    have hraw : (0 : ℝ) ≤ ((c.DCraw : ℚ) : ℝ) := by exact_mod_cast hpos
    have eraw : ((c.DCraw : ℚ) : ℝ) = 1 / (((c.p1 : ℚ) : ℝ) * (2 + ((c.bhi : ℚ) : ℝ) /
        ((c.p0 : ℚ) : ℝ)) * ((L2hiD : ℚ) : ℝ)) - ((c.rs0 : ℚ) : ℝ) / (4 * ((L2loD : ℚ) : ℝ) *
        (((c.p0 : ℚ) : ℝ) * (1 - ((c.p0 : ℚ) : ℝ))) * ((c.Jq : ℚ) : ℝ)) := by
      unfold WCell.DCraw; push_cast; ring
    rw [← eraw] at h
    have hb2 : ((c.blo : ℚ) : ℝ) ^ 2 ≤ (q - p) ^ 2 := pow_le_pow_left₀ hblo0 hβlo 2
    push_cast
    linarith [mul_le_mul_of_nonneg_right hb2 hraw]

end CKLaneP


