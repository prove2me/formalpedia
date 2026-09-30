-- Prove2me | Definitions.Def_CK_CKLaneP_SeamWCheck_q03
-- name    : CK_CKLaneP_SeamWCheck_q03
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T07:09:26.405645+00:00
-- url     : https://prove2.me/theorems/791c194a-0b65-40ee-9336-124ae0fb3cc5
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamWCheck (proof part)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamWCheck (proof part)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamWCheck (proof part)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamWCheck (proof part) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamWCheck (proof part).lean)

import Definitions.Def_CK_CKLaneP_SeamWCheck_q02

set_option autoImplicit false
namespace CKLaneP
open GeneralCK GeneralCK.Certificates.Mixed Set
set_option maxHeartbeats 4000000 in
theorem wcheckA_sound_hJv (hdouble : CanonicalDoubleCapEntropyEndpoints) (c : WCell)
    (hc : wcheckA c = true) {p q ys : ℝ}
    (hp0 : ((c.p0 : ℚ) : ℝ) ≤ p) (hp1 : p ≤ ((c.p1 : ℚ) : ℝ))
    (ht0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤ q - p)
    (ht1 : q - p ≤ ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p))
    (hys0 : 0 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) :
    ∀ m ∈ Icc q (1 / 10000 / 2), max 0 ((c.Jv : ℚ) : ℝ) ≤ jdef (H p) (H q) m := by
  unfold wcheckA at hc
  obtain ⟨ok0, ok1, okql, okq, okvb, okva, okxb, okx2, hnp0, hnp1, hp0pos, hp01, hp1S,
    ht0pos, ht01, ht1le, hql, hqhi, hqd, ha12, heL, hfL, hJq, hkh1, hvb, hvba1, hXmin, hbrX,
    hVmin, hbrV, hbrW, hvab1, hxb, hxbv, hbrxb, hbrx2, hdhk, hM0, hPmin0, hPminmax, hfl1, hfl2,
    hflA, hflC, hneed, hden, hfinal⟩ := of_decide_eq_true hc
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
  have hDC : ((c.DC0 : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
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
  -- (DC, sharp defect form)
  have hDC2 : ((c.DC2 : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
    have hqd12 : ((c.qd : ℚ) : ℝ) < 1 / 2 := by linarith
    have hLA : ((logDnQ ((c.p0 + c.blo) / c.p1) : ℚ) : ℝ) ≤
        Real.log ((((c.p0 : ℚ) : ℝ) + ((c.blo : ℚ) : ℝ)) / ((c.p1 : ℚ) : ℝ)) := by
      have h := logDnQ_sound hflA
      push_cast at h
      exact h
    have hLB : Real.log (2 * ((c.qd : ℚ) : ℝ) / (((c.qd : ℚ) : ℝ) + ((c.p0 : ℚ) : ℝ))) ≤
        ((logUpQ (2 * c.qd / (c.qd + c.p0)) : ℚ) : ℝ) := by
      have hpos : (0 : ℚ) < 2 * c.qd / (c.qd + c.p0) := by
        have : (0 : ℚ) < c.qd := by
          have : (0 : ℝ) < ((c.qd : ℚ) : ℝ) := by linarith
          exact_mod_cast this
        positivity
      have h := logUpQ_sound hpos
      push_cast at h
      exact h
    have hLC : ((logDnQ ((c.p1 + c.p0 + c.blo) / (2 * c.p1)) : ℚ) : ℝ) ≤
        Real.log ((((c.p1 : ℚ) : ℝ) + ((c.p0 : ℚ) : ℝ) + ((c.blo : ℚ) : ℝ)) / (2 * ((c.p1 : ℚ) : ℝ))) := by
      have h := logDnQ_sound hflC
      push_cast at h
      exact h
    have h := dc_cell_lower2 (p0 := ((c.p0 : ℚ) : ℝ)) (p1 := ((c.p1 : ℚ) : ℝ))
      (blo := ((c.blo : ℚ) : ℝ)) (bhi := ((c.bhi : ℚ) : ℝ)) (qd := ((c.qd : ℚ) : ℝ))
      (rs0 := ((c.rs0 : ℚ) : ℝ)) (Jq := ((c.Jq : ℚ) : ℝ)) (l2hi := ((L2hiD : ℚ) : ℝ))
      (l2lo := ((L2loD : ℚ) : ℝ)) hp0R hp0 hp1 hpq hqqd hqd12 hblo0 hβlo hbhi hJqR hJq0 hrsR
      log2D_bounds.2 log2D_bounds.1 VD.L2lo_pos hLA hLB hLC
    have e : ((c.DC2 : ℚ) : ℝ) = ((c.blo : ℚ) : ℝ) * max 0 ((logDnQ ((c.p0 + c.blo) / c.p1) : ℚ) : ℝ) /
        (2 * ((L2hiD : ℚ) : ℝ)) - 2 * ((c.rs0 : ℚ) : ℝ) * (((((c.qd : ℚ) : ℝ) *
        ((logUpQ (2 * c.qd / (c.qd + c.p0)) : ℚ) : ℝ) / 2 - ((c.p0 : ℚ) : ℝ) *
        max 0 ((logDnQ ((c.p1 + c.p0 + c.blo) / (2 * c.p1)) : ℚ) : ℝ) / 2) +
        ((c.bhi : ℚ) : ℝ) ^ 2 / (4 * (1 - ((c.qd : ℚ) : ℝ)))) / ((L2loD : ℚ) : ℝ)) / ((c.Jq : ℚ) : ℝ) := by
      unfold WCell.DC2; push_cast; ring
    rw [e]; exact h
  have hDCb : ((c.DCb : ℚ) : ℝ) ≤ canonicalPureGap p q (H p) (H q) := by
    unfold WCell.DCb; push_cast; exact max_le hDC hDC2
  -- (R)
  have hc1v : ∀ t ∈ Ioo p q, ((c.c1v : ℚ) : ℝ) - 12 / ((c.EL : ℚ) : ℝ) * (q - t) ≤
      rightD q (H p) (H q) t := by
    intro t ht
    have h := rightD_ge hp ht.1.le ht.2 (by linarith) hPmin0R
      (fun x hx => hPminAll x
        (by rw [eVmin]; exact le_trans (vmin_le_of (by linarith) hE hEHR (by linarith [ht.2])) hx.1)
        (by rw [eWmax]; exact le_trans hx.2 (w_le_wmax_of (by linarith [ht.1]) heL0 heLR)))
    have hlogv : ((logDnQ ((1 + c.fL / c.eH) / 2) : ℚ) : ℝ) ≤ Real.log ((H p + H q) / (2 * H p)) := by
      have h1 := logDnQ_sound hfl1
      refine le_trans h1 (Real.log_le_log ?_ ?_)
      · have : (0 : ℚ) < (1 + c.fL / c.eH) / 2 := by
          have : (0 : ℚ) < c.eH := lt_of_lt_of_le heL (by
            have := (Rat.cast_le (K := ℝ)).mp (le_trans heLR heHR); exact this)
          positivity
        exact_mod_cast this
      · push_cast
        have heH0 : (0 : ℝ) < ((c.eH : ℚ) : ℝ) := lt_of_lt_of_le hHp heHR
        have h2 : ((c.fL : ℚ) : ℝ) / ((c.eH : ℚ) : ℝ) ≤ H q / H p := by
          rw [div_le_div_iff₀ heH0 hHp]
          exact mul_le_mul hfLR heHR hHp.le (by linarith)
        have e3 : (H p + H q) / (2 * H p) = (1 + H q / H p) / 2 := by field_simp
        rw [e3]
        linarith
    have ec : ((c.c1v : ℚ) : ℝ) = ((c.Pmin : ℚ) : ℝ) * ((logDnQ ((1 + c.fL / c.eH) / 2) : ℚ) : ℝ) := by
      unfold WCell.c1v; push_cast; ring
    rw [ec]
    have h3 : 12 * ((q - t) / (H p + H q)) ≤ 12 / ((c.EL : ℚ) : ℝ) * (q - t) := by
      rw [mul_div_assoc', div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by linarith [ht.2]) hEL0 hELR
    have h4 := mul_le_mul_of_nonneg_left hlogv hPmin0R
    linarith
  have hR : ((c.R0 : ℚ) : ℝ) ≤ canonicalPureGap q q (H p) (H q) - canonicalPureGap p q (H p) (H q) := by
    have hmono := rightFiber_mono hp hpq.le le_rfl (by linarith)
    unfold WCell.R0
    push_cast
    rcases le_total (min (c.c1v * c.blo - 6 / c.EL * c.blo ^ 2) (c.c1v * c.bhi - 6 / c.EL * c.bhi ^ 2)) 0
      with hneg | hpos
    · have : ((max 0 (min (c.c1v * c.blo - 6 / c.EL * c.blo ^ 2)
          (c.c1v * c.bhi - 6 / c.EL * c.bhi ^ 2)) : ℚ) : ℝ) = 0 := by
        rw [max_eq_left hneg]; simp
      push_cast at this
      rw [this]
      linarith
    · have haff := rightFiber_affine (c1 := ((c.c1v : ℚ) : ℝ)) (c2 := 12 / ((c.EL : ℚ) : ℝ))
        hp le_rfl hpq.le le_rfl (by linarith) hc1v
      have hsq : (q - q) ^ 2 = (0 : ℝ) := by ring
      rw [hsq] at haff
      have hg := gap_concave_min (a := ((c.c1v : ℚ) : ℝ)) (b := 6 / ((c.EL : ℚ) : ℝ))
        (by positivity) hβlo hbhi
      have hmx : ((max 0 (min (c.c1v * c.blo - 6 / c.EL * c.blo ^ 2)
          (c.c1v * c.bhi - 6 / c.EL * c.bhi ^ 2)) : ℚ) : ℝ) =
          min (((c.c1v : ℚ) : ℝ) * ((c.blo : ℚ) : ℝ) - 6 / ((c.EL : ℚ) : ℝ) * ((c.blo : ℚ) : ℝ) ^ 2)
            (((c.c1v : ℚ) : ℝ) * ((c.bhi : ℚ) : ℝ) - 6 / ((c.EL : ℚ) : ℝ) * ((c.bhi : ℚ) : ℝ) ^ 2) := by
        rw [max_eq_right hpos]; push_cast; ring_nf
      push_cast at hmx
      rw [hmx]
      have e5 : 12 / ((c.EL : ℚ) : ℝ) * ((q - p) ^ 2 - 0) / 2 = 6 / ((c.EL : ℚ) : ℝ) * (q - p) ^ 2 := by
        ring
      linarith
  -- (B)
  intro m hm
  have hm12 : m < 1 / 2 := by linarith [hm.2]
  have hZ : 0 < 1 - 2 * m := by linarith
  -- contacts of the bulk arguments lie in [Xmin, Wmax]
  have hXZ : ∀ x : ℝ, (1 - 2 * m) / (2 * H q) ≤ x → ((c.Xmin : ℚ) : ℝ) ≤ x := by
    intro x hx
    refine le_trans ?_ hx
    rw [eXmin]; exact xmin_le_of hHq hfHR hA0 (by linarith [hm.2])
  have hcap : radialContact ((1 - 2 * m) / H q) 1 ≤ 1 / 10000 := by
    have e : (1 - 2 * m) / H q = 2 * ((1 - 2 * m) / (2 * H q)) := by field_simp
    rw [e]
    have hcb := contact_le_of_bracket dvb hXmin hbrX (hXZ _ le_rfl)
    have : ((dy c.nvb).v : ℝ) ≤ 1 / 10000 := by
      have h' : ((dy c.nvb).v : ℚ) ≤ 1 / 10000 := by rw [dy_v]; exact hvb
      have h2 := (Rat.cast_le (K := ℝ)).mpr h'
      rw [show ((1 / 10000 : ℚ) : ℝ) = 1 / 10000 by norm_num] at h2
      exact h2
    linarith
  have hjl := jdef_lower hHp hHpq hm12 hcap
  have hj0 : 0 ≤ jdef (H p) (H q) m := le_trans (by positivity) hjl
  -- κ-bounds
  have hκ : H p / H q ≤ ((c.kh : ℚ) : ℝ) := by
    have e : ((c.kh : ℚ) : ℝ) = ((c.eH : ℚ) : ℝ) / ((c.fL : ℚ) : ℝ) := by
      unfold WCell.kh; push_cast; ring
    rw [e, div_le_div_iff₀ hHq hfL0]
    exact mul_le_mul heHR hfLR hfL0.le (by linarith)
  have hκl : ((c.kl : ℚ) : ℝ) ≤ H p / H q := by
    have e : ((c.kl : ℚ) : ℝ) = ((c.eL : ℚ) : ℝ) / ((c.fH : ℚ) : ℝ) := by
      unfold WCell.kl; push_cast; ring
    have hfH0 : (0 : ℝ) < ((c.fH : ℚ) : ℝ) := lt_of_lt_of_le hHq hfHR
    rw [e, div_le_div_iff₀ hfH0 hHq]
    exact mul_le_mul heLR hfHR hHq.le hHp.le
  have hkh1R : ((c.kh : ℚ) : ℝ) ≤ 1 := by
    have e : ((c.kh : ℚ) : ℝ) = ((c.eH : ℚ) : ℝ) / ((c.fL : ℚ) : ℝ) := by
      unfold WCell.kh; push_cast; ring
    rw [e, div_le_one hfL0]
    exact_mod_cast hkh1
  have hkpos : 0 < H p / H q := div_pos hHp hHq
  -- 0.225 form
  have hj1 : 9 / 40 * (1 - ((c.kh : ℚ) : ℝ)) ^ 2 ≤ jdef (H p) (H q) m := by
    refine le_trans ?_ hjl
    have e : 9 / 10 * (H q - H p) ^ 2 / (4 * H q ^ 2) = 9 / 40 * (1 - H p / H q) ^ 2 := by
      field_simp; ring
    rw [e]
    have h1 : 0 ≤ 1 - ((c.kh : ℚ) : ℝ) := by linarith
    have h2 : 1 - ((c.kh : ℚ) : ℝ) ≤ 1 - H p / H q := by linarith
    have h3 := pow_le_pow_left₀ h1 h2 2
    linarith
  -- log form
  have hj2 : ((c.Pmin : ℚ) : ℝ) * ((logDnQ ((1 + c.kh) ^ 2 / (4 * c.kh)) : ℚ) : ℝ) -
      (((c.Pmax : ℚ) : ℝ) - ((c.Pmin : ℚ) : ℝ)) * ((logUpQ (2 / (1 + c.kl)) : ℚ) : ℝ) ≤
      jdef (H p) (H q) m := by
    have hjg := jdef_ge_log (Pm := ((c.Pmin : ℚ) : ℝ)) (PM := ((c.Pmax : ℚ) : ℝ)) hHp hHpq hm12
      (fun x hx => hPminAllX x (hXZ x (le_trans (div_le_div_of_nonneg_left hZ.le hE
        (by linarith)) hx.1))
        (by
          rw [eWmax]
          refine le_trans hx.2 ?_
          have h1 : (1 - 2 * m) / (2 * H p) ≤ 1 / (2 * H p) :=
            div_le_div_of_nonneg_right (by linarith [hm.1]) (by linarith)
          have h2 : 1 / (2 * H p) ≤ 1 / (2 * ((c.eL : ℚ) : ℝ)) :=
            div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
          linarith))
      (fun x hx => hPmaxAll x (hXZ x hx.1))
    -- log(E/2e) - log(2f/E) = log((1+κ)²/(4κ))
    set κ := H p / H q with hκd
    have hE2e : (H p + H q) / (2 * H p) = (1 + κ) / (2 * κ) := by
      rw [hκd]; field_simp; ring
    have h2fE : 2 * H q / (H p + H q) = 2 / (1 + κ) := by
      rw [hκd]; field_simp; ring
    rw [hE2e, h2fE] at hjg
    have hsplit : Real.log ((1 + κ) / (2 * κ)) = Real.log ((1 + κ) ^ 2 / (4 * κ)) +
        Real.log (2 / (1 + κ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    rw [hsplit] at hjg
    have hlog1 : ((logDnQ ((1 + c.kh) ^ 2 / (4 * c.kh)) : ℚ) : ℝ) ≤
        Real.log ((1 + κ) ^ 2 / (4 * κ)) := by
      refine le_trans (logDnQ_sound hfl2) ?_
      have hkh0 : (0 : ℝ) < ((c.kh : ℚ) : ℝ) := lt_of_lt_of_le hkpos hκ
      apply Real.log_le_log (by push_cast; positivity)
      push_cast
      exact kappa_ratio_mono hkpos hκ hkh1R
    have hlog2 : Real.log (2 / (1 + κ)) ≤ ((logUpQ (2 / (1 + c.kl)) : ℚ) : ℝ) := by
      have hkl0 : (0 : ℝ) ≤ ((c.kl : ℚ) : ℝ) := by
        have e : ((c.kl : ℚ) : ℝ) = ((c.eL : ℚ) : ℝ) / ((c.fH : ℚ) : ℝ) := by
          unfold WCell.kl; push_cast; ring
        rw [e]; have := lt_of_lt_of_le hHq hfHR; positivity
      have hpos : (0 : ℚ) < 2 / (1 + c.kl) := by
        have : (0 : ℚ) ≤ c.kl := by exact_mod_cast hkl0
        positivity
      refine le_trans (Real.log_le_log (by positivity) ?_) (by
        have := logUpQ_sound hpos
        push_cast at this
        exact this)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hPd : (0 : ℝ) ≤ ((c.Pmax : ℚ) : ℝ) - ((c.Pmin : ℚ) : ℝ) := by linarith
    have hlog2nn : 0 ≤ Real.log (2 / (1 + κ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      have : κ ≤ 1 := le_trans hκ hkh1R
      linarith
    linarith [mul_le_mul_of_nonneg_left hlog1 hPmin0R, mul_le_mul_of_nonneg_left hlog2 hPd]
  have eJv : ((c.Jv : ℚ) : ℝ) = max (9 / 40 * (1 - ((c.kh : ℚ) : ℝ)) ^ 2)
      (((c.Pmin : ℚ) : ℝ) * ((logDnQ ((1 + c.kh) ^ 2 / (4 * c.kh)) : ℚ) : ℝ) -
        (((c.Pmax : ℚ) : ℝ) - ((c.Pmin : ℚ) : ℝ)) * ((logUpQ (2 / (1 + c.kl)) : ℚ) : ℝ)) := by
    unfold WCell.Jv; push_cast; ring_nf
  rw [eJv]
  exact max_le hj0 (max_le hj1 hj2)

end CKLaneP


