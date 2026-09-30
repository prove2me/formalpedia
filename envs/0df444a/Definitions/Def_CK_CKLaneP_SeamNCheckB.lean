-- Prove2me | Definitions.Def_CK_CKLaneP_SeamNCheckB
-- name    : CK_CKLaneP_SeamNCheckB
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:07:27.839974+00:00
-- url     : https://prove2.me/theorems/4e838658-97d9-4850-a383-edeab9e0a15e
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamNCheckB` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamNCheckB` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamNCheckB` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamNCheckB (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamNCheckB.lean)

import Definitions.Def_CK_CKLaneP_SeamNCheck

-- ===== source module CKLaneP.SeamNCheckB =====
section
/-
Lane P — the normalized (N-mode) seam cell checker, case B (`1 ≤ t0 < t1 ≤ 2`, `q > S/2`).

Base point `y_lo = 2q − S`; `L_B = S − q − p = λβ` with `λ = 2/t − 1 ≥ λlo = (2 − t1)/t1`.
Three alternatives:
* `vac1`: `Θ(y_hi/E) ≤ 12·y_hi/E < ½·Pmin·Jq·β/fH ≤ Δ(y*)` (β cancels; `y_hi ≤ 2β/t0`);
* `vac2`: `y* ≤ β·Yn ≤ β(2 − 2/t0) ≤ y_lo` (the stationary point would lie below `y_lo`);
* `main`: `0 ≤ DCn + λlo(c1n − c2) + (c2/2)λlo² − M·(Yn − 2 + 2/t0)²/(2 E_lo)` with `c1n ≥ c2`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

namespace NCell

def lamlo (c : NCell) : ℚ := (2 - c.t1) / c.t1
def YB (c : NCell) : ℚ := c.Yn - (2 - 2 / c.t0)

end NCell

/-- Case-B N-cell check. -/
def ncheckB (c : NCell) : Bool :=
  ncommon c && decide (1 ≤ c.t0 ∧ c.t0 < c.t1 ∧ c.t1 ≤ 2 ∧
    ((c.Pmin * c.Jq / (2 * c.fH) > 24 / (c.t0 * c.EL) ∧ (Sq - 2 * c.p0) / c.EL ≤ 2 / 25) ∨
     c.Yn ≤ 2 - 2 / c.t0 ∨
     (c.c2 ≤ c.c1n ∧ 0 ≤ c.DCn + c.lamlo * (c.c1n - c.c2) + c.c2 / 2 * c.lamlo ^ 2 -
        c.M * c.YB ^ 2 / (2 * c.EL))))

/-- Case B master inequality with the weak hypothesis `S/2 ≤ q` (same proof as `seam_master_B`). -/
theorem seam_master_Bw {S p q ys DCn c1n c2 M Y : ℝ}
    (hS0 : 0 < S) (hS : S ≤ 1 / 10000) (hp : 0 < p) (hpq : p < q) (hqS : S / 2 ≤ q)
    (hpqS : p + q < S)
    (hys0 : 2 * q - S < ys) (hysS : ys < S - 2 * p)
    (hstat : seamD S (H p) (H q) ys = 0)
    (hDC : (q - p) ^ 2 * DCn ≤ canonicalPureGap p q (H p) (H q))
    (hR : ∀ t ∈ Ioo p (S - q), c1n * (q - p) - c2 * (q - t) ≤ rightD q (H p) (H q) t)
    (hM : ∀ t ∈ Ioo (2 * q - S) ys, e8Theta (ys / (H p + H q)) - e8Theta (t / (H p + H q)) ≤
      M * ((ys - t) / (H p + H q)))
    (hM0 : 0 ≤ M) (hY : ys - (2 * q - S) ≤ (q - p) * Y)
    (hcheck : 0 ≤ (q - p) ^ 2 * DCn + (c1n * (q - p) * (S - q - p) -
        c2 * ((q - p) ^ 2 - (2 * q - S) ^ 2) / 2) - M * ((q - p) * Y) ^ 2 / (2 * (H p + H q))) :
    0 ≤ seamCurve S (H p) (H q) ys := by
  have hq12 : q < 1 / 2 := by linarith
  have hHp : 0 < H p := H_pos hp (by linarith)
  have hHpq : H p ≤ H q := H_strictMonoOn.monotoneOn ⟨hp.le, by linarith⟩ ⟨(hp.trans hpq).le, by linarith⟩ hpq.le
  have hHq : 0 < H q := lt_of_lt_of_le hHp hHpq
  have hE : 0 < H p + H q := by linarith
  have hylo0 : 0 ≤ 2 * q - S := by linarith
  have hdip := seam_dip_M (S := S) hS0.le hHp hHq hylo0 hys0 (by linarith) hstat hM
  rw [seamCurve_ylo] at hdip
  have hright := rightFiber_affine (a := p) (b := q) (t1 := p) (t2 := S - q) (c1 := c1n * (q - p))
    (c2 := c2) hp le_rfl (by linarith) (by linarith) (by linarith) (fun t ht => hR t ht)
  have e2 : (q - (S - q)) = 2 * q - S := by ring
  rw [e2] at hright
  have hY2 : (ys - (2 * q - S)) ^ 2 ≤ ((q - p) * Y) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hY 2
  have hdip2 : M * (ys - (2 * q - S)) ^ 2 / (2 * (H p + H q)) ≤
      M * ((q - p) * Y) ^ 2 / (2 * (H p + H q)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hY2 hM0
  linarith

set_option maxHeartbeats 1000000 in
theorem ncheckB_sound (hdouble : CanonicalDoubleCapEntropyEndpoints) (c : NCell)
    (hc : ncheckB c = true) {p q ys : ℝ}
    (hp0 : ((c.p0 : ℚ) : ℝ) ≤ p) (hp1 : p ≤ ((c.p1 : ℚ) : ℝ))
    (ht0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) ≤ q - p)
    (ht1 : q - p ≤ ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - p))
    (hys0 : 2 * q - 1 / 10000 < ys) (hysS : ys < 1 / 10000 - 2 * p)
    (hstat : seamD (1 / 10000) (H p) (H q) ys = 0) :
    0 ≤ seamCurve (1 / 10000) (H p) (H q) ys := by
  unfold ncheckB at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hcom, hB⟩ := hc
  obtain ⟨ht0ge, ht01, ht1le, halt⟩ := of_decide_eq_true hB
  have hcom' := hcom
  unfold ncommon at hcom'
  obtain ⟨-, -, -, -, -, -, -, -, -, hp0pos, -, hp1S, -⟩ := of_decide_eq_true hcom'
  have hp0R : (0 : ℝ) < ((c.p0 : ℚ) : ℝ) := by exact_mod_cast hp0pos
  have hp : 0 < p := lt_of_lt_of_le hp0R hp0
  have hp1SR : ((c.p1 : ℚ) : ℝ) ≤ 1 / 10000 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hp1S
    rw [show ((Sq / 2 : ℚ) : ℝ) = 1 / 10000 / 2 by unfold Sq; norm_num] at this
    exact this
  have hpqS : p + q < 1 / 10000 := by linarith
  have hε : 0 < 1 / 10000 / 2 - p := by
    by_contra hcon
    push Not at hcon
    have hpe : p = 1 / 10000 / 2 := le_antisymm (le_trans hp1 hp1SR) (by linarith)
    have h0 : ((c.t0 : ℚ) : ℝ) * (1 / 10000 / 2 - p) = 0 := by rw [hpe, sub_self, mul_zero]
    linarith
  have ht0R : (1 : ℝ) ≤ ((c.t0 : ℚ) : ℝ) := by exact_mod_cast ht0ge
  have ht1R : ((c.t1 : ℚ) : ℝ) ≤ 2 := by exact_mod_cast ht1le
  have ht01R : ((c.t0 : ℚ) : ℝ) < ((c.t1 : ℚ) : ℝ) := by exact_mod_cast ht01
  have hqS : 1 / 10000 / 2 ≤ q := by
    have h1 := mul_le_mul_of_nonneg_right ht0R hε.le
    rw [one_mul] at h1
    linarith
  have hβ0 : 0 < q - p := by nlinarith
  have hys0' : 0 < ys := by linarith
  have hbhi : q - p ≤ ((c.bhi : ℚ) : ℝ) := by
    have e : ((c.bhi : ℚ) : ℝ) = ((c.t1 : ℚ) : ℝ) * (1 / 10000 / 2 - ((c.p0 : ℚ) : ℝ)) := by
      unfold NCell.bhi; push_cast; rw [Sq_cast]
    rw [e]
    exact le_trans ht1 (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  obtain ⟨hDC, hR, -, hM, hM0, hYn, hELR, hEL0, hqqd, hΔlo⟩ :=
    ncell_facts hdouble c hcom hp0 hp1 hβ0 hbhi hys0' hysS hstat
  have hE : 0 < H p + H q := lt_of_lt_of_le hEL0 hELR
  -- y_lo/β ≥ 2 − 2/t0
  have hylo : (q - p) * (2 - 2 / ((c.t0 : ℚ) : ℝ)) ≤ 2 * q - 1 / 10000 := by
    have ht0pos : (0 : ℝ) < ((c.t0 : ℚ) : ℝ) := by linarith
    have h1 : (1 / 10000 / 2 - p) ≤ (q - p) / ((c.t0 : ℚ) : ℝ) := by
      rw [le_div_iff₀ ht0pos]; linarith
    have e : (q - p) * (2 - 2 / ((c.t0 : ℚ) : ℝ)) = 2 * (q - p) - 2 * ((q - p) / ((c.t0 : ℚ) : ℝ)) := by
      ring
    rw [e]; linarith
  rcases halt with ⟨hv1, hsmall⟩ | hv2 | ⟨hc12, hmain⟩
  · -- vacuity via Θ ≤ 12x
    exfalso
    have hv1R : 24 / (((c.t0 : ℚ) : ℝ) * ((c.EL : ℚ) : ℝ)) <
        ((c.Pmin : ℚ) : ℝ) * ((c.Jq : ℚ) : ℝ) / (2 * ((c.fH : ℚ) : ℝ)) := by
      have := (Rat.cast_lt (K := ℝ)).mpr hv1
      push_cast at this
      exact this
    have hsmallR : (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) / ((c.EL : ℚ) : ℝ) ≤ 2 / 25 := by
      have := (Rat.cast_le (K := ℝ)).mpr hsmall
      push_cast at this
      rw [Sq_cast] at this
      exact this
    set yh := 1 / 10000 - 2 * p with hyh
    have hyhE : yh / (H p + H q) ≤ 2 / 25 := by
      have h1 : yh / (H p + H q) ≤ yh / ((c.EL : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left (by linarith) hEL0 hELR
      have h2 : yh / ((c.EL : ℚ) : ℝ) ≤ (1 / 10000 - 2 * ((c.p0 : ℚ) : ℝ)) / ((c.EL : ℚ) : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hEL0.le
      linarith
    have h12 := theta_le_twelve (div_pos (by linarith) hE) hyhE
    have hmono := e8Theta_mono (div_pos hys0' hE) (div_le_div_of_nonneg_right hysS.le hE.le)
    -- yh ≤ 2β/t0
    have ht0pos : (0 : ℝ) < ((c.t0 : ℚ) : ℝ) := by linarith
    have hyhβ : yh ≤ 2 * (q - p) / ((c.t0 : ℚ) : ℝ) := by
      rw [le_div_iff₀ ht0pos]; rw [hyh]; nlinarith
    -- 12 yh/E ≤ 24 β/(t0 EL)
    have h3 : 12 * (yh / (H p + H q)) ≤ (q - p) * (24 / (((c.t0 : ℚ) : ℝ) * ((c.EL : ℚ) : ℝ))) := by
      have h4 : yh / (H p + H q) ≤ yh / ((c.EL : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left (by linarith) hEL0 hELR
      have h5 : yh / ((c.EL : ℚ) : ℝ) ≤ 2 * (q - p) / ((c.t0 : ℚ) : ℝ) / ((c.EL : ℚ) : ℝ) :=
        div_le_div_of_nonneg_right hyhβ hEL0.le
      have e : 12 * (2 * (q - p) / ((c.t0 : ℚ) : ℝ) / ((c.EL : ℚ) : ℝ)) =
          (q - p) * (24 / (((c.t0 : ℚ) : ℝ) * ((c.EL : ℚ) : ℝ))) := by field_simp; ring
      nlinarith
    have h6 : (q - p) * (24 / (((c.t0 : ℚ) : ℝ) * ((c.EL : ℚ) : ℝ))) <
        (q - p) * (((c.Pmin : ℚ) : ℝ) * ((c.Jq : ℚ) : ℝ) / (2 * ((c.fH : ℚ) : ℝ))) :=
      mul_lt_mul_of_pos_left hv1R hβ0
    have e7 : ((c.Pmin : ℚ) : ℝ) * (((c.Jq : ℚ) : ℝ) * (q - p) / ((c.fH : ℚ) : ℝ)) / 2 =
        (q - p) * (((c.Pmin : ℚ) : ℝ) * ((c.Jq : ℚ) : ℝ) / (2 * ((c.fH : ℚ) : ℝ))) := by
      field_simp
    linarith
  · -- vacuity via the location bound
    exfalso
    have hv2R : ((c.Yn : ℚ) : ℝ) ≤ 2 - 2 / ((c.t0 : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hv2
      push_cast at this
      exact this
    have := mul_le_mul_of_nonneg_left hv2R hβ0.le
    linarith
  · -- main inequality
    have hc12R : ((c.c2 : ℚ) : ℝ) ≤ ((c.c1n : ℚ) : ℝ) := by exact_mod_cast hc12
    have hmainR := (Rat.cast_le (K := ℝ)).mpr hmain
    push_cast at hmainR
    set β := q - p with hβd
    set LB := 1 / 10000 - q - p with hLB
    have hLB0 : 0 ≤ LB := by rw [hLB]; linarith
    -- λ = LB/β ≥ λlo
    have hlam : ((c.lamlo : ℚ) : ℝ) ≤ LB / β := by
      have e : ((c.lamlo : ℚ) : ℝ) = (2 - ((c.t1 : ℚ) : ℝ)) / ((c.t1 : ℚ) : ℝ) := by
        unfold NCell.lamlo; push_cast; ring
      rw [e, div_le_div_iff₀ (by linarith) hβ0]
      rw [hLB, hβd]
      nlinarith
    have hlam0 : (0 : ℝ) ≤ ((c.lamlo : ℚ) : ℝ) := by
      have e : ((c.lamlo : ℚ) : ℝ) = (2 - ((c.t1 : ℚ) : ℝ)) / ((c.t1 : ℚ) : ℝ) := by
        unfold NCell.lamlo; push_cast; ring
      rw [e]; apply div_nonneg (by linarith) (by linarith)
    have hlam1 : LB / β ≤ 1 := by
      rw [div_le_one hβ0, hLB, hβd]; linarith
    -- base term in λ
    have hbase : β ^ 2 * (((c.lamlo : ℚ) : ℝ) * (((c.c1n : ℚ) : ℝ) - ((c.c2 : ℚ) : ℝ)) +
        ((c.c2 : ℚ) : ℝ) / 2 * ((c.lamlo : ℚ) : ℝ) ^ 2) ≤
        ((c.c1n : ℚ) : ℝ) * β * LB - ((c.c2 : ℚ) : ℝ) * (β ^ 2 - (2 * q - 1 / 10000) ^ 2) / 2 := by
      have hc20 : (0 : ℝ) ≤ ((c.c2 : ℚ) : ℝ) := by
        have e : ((c.c2 : ℚ) : ℝ) = 12 / ((c.EL : ℚ) : ℝ) := by unfold NCell.c2; push_cast; ring
        rw [e]; positivity
      set l := LB / β with hl
      have hLBl : LB = l * β := by rw [hl]; field_simp
      have e2 : 2 * q - 1 / 10000 = β - LB := by rw [hβd, hLB]; ring
      rw [e2, hLBl]
      have key : ((c.lamlo : ℚ) : ℝ) * (((c.c1n : ℚ) : ℝ) - ((c.c2 : ℚ) : ℝ)) +
          ((c.c2 : ℚ) : ℝ) / 2 * ((c.lamlo : ℚ) : ℝ) ^ 2 ≤
          l * (((c.c1n : ℚ) : ℝ) - ((c.c2 : ℚ) : ℝ)) + ((c.c2 : ℚ) : ℝ) / 2 * l ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hlam (sub_nonneg.2 hc12R),
          mul_le_mul hlam hlam hlam0 (le_trans hlam0 hlam)]
      have e3 : ((c.c1n : ℚ) : ℝ) * β * (l * β) - ((c.c2 : ℚ) : ℝ) * (β ^ 2 - (β - l * β) ^ 2) / 2 =
          β ^ 2 * (l * (((c.c1n : ℚ) : ℝ) - ((c.c2 : ℚ) : ℝ)) + ((c.c2 : ℚ) : ℝ) / 2 * l ^ 2) := by
        ring
      rw [e3]
      exact mul_le_mul_of_nonneg_left key (sq_nonneg _)
    have hY : ys - (2 * q - 1 / 10000) ≤ β * ((c.YB : ℚ) : ℝ) := by
      have e : ((c.YB : ℚ) : ℝ) = ((c.Yn : ℚ) : ℝ) - (2 - 2 / ((c.t0 : ℚ) : ℝ)) := by
        unfold NCell.YB; push_cast; ring
      rw [e]
      nlinarith
    have hdip := dip_mono_of (Y := β * ((c.YB : ℚ) : ℝ)) hM0 hEL0 hELR
    have hcheck : 0 ≤ β ^ 2 * ((c.DCn : ℚ) : ℝ) + (((c.c1n : ℚ) : ℝ) * β * LB -
        ((c.c2 : ℚ) : ℝ) * (β ^ 2 - (2 * q - 1 / 10000) ^ 2) / 2) -
        ((c.M : ℚ) : ℝ) * (β * ((c.YB : ℚ) : ℝ)) ^ 2 / (2 * (H p + H q)) := by
      have e4 : ((c.M : ℚ) : ℝ) * (β * ((c.YB : ℚ) : ℝ)) ^ 2 / (2 * ((c.EL : ℚ) : ℝ)) =
          β ^ 2 * (((c.M : ℚ) : ℝ) * ((c.YB : ℚ) : ℝ) ^ 2 / (2 * ((c.EL : ℚ) : ℝ))) := by ring
      have h5 : 0 ≤ β ^ 2 * (((c.DCn : ℚ) : ℝ) + ((c.lamlo : ℚ) : ℝ) * (((c.c1n : ℚ) : ℝ) -
          ((c.c2 : ℚ) : ℝ)) + ((c.c2 : ℚ) : ℝ) / 2 * ((c.lamlo : ℚ) : ℝ) ^ 2 -
          ((c.M : ℚ) : ℝ) * ((c.YB : ℚ) : ℝ) ^ 2 / (2 * ((c.EL : ℚ) : ℝ))) :=
        mul_nonneg (sq_nonneg _) hmainR
      nlinarith
    exact seam_master_Bw (by norm_num) le_rfl hp (by linarith) hqS (by linarith) hys0 hysS hstat
      hDC (fun t ht => hR t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hM t ⟨by linarith [ht.1], ht.2⟩) hM0 hY hcheck

end CKLaneP

end


