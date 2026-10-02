-- Prove2me | Definitions.Def_CK_CKLaneA1_R5PsiMono
-- name    : CK_CKLaneA1_R5PsiMono
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:49:22.921377+00:00
-- url     : https://prove2.me/theorems/a4bfdb2e-5ff2-4c97-920e-419fdd33206f
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5PsiMono` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5PsiMono` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5PsiMono` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5PsiMono (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5PsiMono.lean)

import Definitions.Def_CK_CKLaneA1_R5Box

-- ===== source module CKLaneA1.R5PsiMono =====
section

/-!
# CKLaneA1.R5PsiMono — monotonicity of `Psi = Θ'(contact)` on a certified range

`Θ'(x) = Psi(radialContact (2x) 1)` (Lane P, `deriv_e8Theta_eq_Psi`).  `Psi` is increasing in the contact
`v` on `[2^-10, 49/100]`; equivalently `Θ'` is decreasing on the corresponding `x`-range.  Proof: the
logarithmic derivative `Lam = Psi'/Psi` is bounded below on each interval of a dyadic grid by a
kernel-evaluated rational (`lamLo`), which is positive.  Consequence (`brB_sound`): on a contact bracket
inside the range, `Θ'` is bounded by the point value `PsiUB(db, db)`, much sharper than the factorwise
bound `PsiUB(da, db)`.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP Set

/-- Logarithmic derivative of `Psi`. -/
noncomputable def Lam (v : ℝ) : ℝ :=
  3 * (J v * Real.log 2) / hn v +
    (2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v)) / (2 * kap v - (1 - 2 * v) ^ 2) -
    2 * (4 * (1 - 2 * v)) / (4 * v * (1 - v)) -
    3 * (-(1 - 2 * v) / (2 * v * (1 - v))) / kap v

theorem hasDerivAt_H' {v : ℝ} (h0 : 0 < v) (h1 : v < 1) : HasDerivAt H (J v) v := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hfun : H = fun u => hn u / Real.log 2 := by
    funext u; rw [hn_eq_H_mul_log]; field_simp
  have h2 := (hasDerivAt_hn h0 h1).div_const (Real.log 2)
  rw [mul_div_cancel_right₀ _ hl, ← hfun] at h2
  exact h2

theorem two_kap_sub_pos {v : ℝ} (h0 : 0 < v) (h1 : v < 1 / 2) : 0 < 2 * kap v - (1 - 2 * v) ^ 2 := by
  have hk := GeneralCK.kap_ge_log_two h0 (by linarith)
  have hl : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have : (1 - 2 * v) ^ 2 < 1 := by nlinarith
  linarith

theorem hn_pos' {v : ℝ} (h0 : 0 < v) (h1 : v < 1) : 0 < hn v := by
  rw [hn_eq_H_mul_log]
  exact mul_pos (H_pos h0 h1) (Real.log_pos (by norm_num))

theorem Psi_pos {v : ℝ} (h0 : 0 < v) (h1 : v < 1 / 2) : 0 < Psi v := by
  unfold Psi
  have hH := H_pos h0 (by linarith)
  have hn0 := hn_pos' h0 (by linarith)
  have hK := two_kap_sub_pos h0 h1
  have hk := kap_pos h0 h1
  have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hq : 0 < 4 * v * (1 - v) := by nlinarith
  positivity

set_option maxHeartbeats 2000000 in
theorem hasDerivAt_Psi {v : ℝ} (h0 : 0 < v) (h1 : v < 1 / 2) :
    HasDerivAt Psi (Psi v * Lam v) v := by
  have hv1 : v < 1 := by linarith
  have hHd := hasDerivAt_H' h0 hv1
  have hh := hasDerivAt_hn h0 hv1
  have hk := hasDerivAt_kap h0 hv1
  have hr : HasDerivAt (fun u : ℝ => 1 - 2 * u) (-2) v := by
    simpa using ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hq : HasDerivAt (fun u : ℝ => 4 * u * (1 - u)) (4 * (1 - 2 * v)) v := by
    have h := ((hasDerivAt_id' v).const_mul (4 : ℝ)).mul ((hasDerivAt_id' v).const_sub (1 : ℝ))
    exact h.congr_deriv (by ring)
  have hN := ((hHd.const_mul 4).mul (hh.pow 2)).mul ((hk.const_mul 2).sub (hr.pow 2))
  have hD := ((hq.pow 2).mul (hk.pow 3)).const_mul (Real.log 2)
  have hH0 := H_pos h0 hv1
  have hn0 := hn_pos' h0 hv1
  have hK := two_kap_sub_pos h0 h1
  have hk0 := kap_pos h0 h1
  have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hqv : 0 < 4 * v * (1 - v) := by nlinarith
  have hDne : Real.log 2 * ((4 * v * (1 - v)) ^ 2 * kap v ^ 3) ≠ 0 := by positivity
  have hdiv := hN.div hD hDne
  have hfun : Psi = fun u => 4 * H u * hn u ^ 2 * (2 * kap u - (1 - 2 * u) ^ 2) /
      (Real.log 2 * ((4 * u * (1 - u)) ^ 2 * kap u ^ 3)) := by
    funext u; unfold Psi; ring
  have hHv : H v = hn v / Real.log 2 := by rw [hn_eq_H_mul_log]; field_simp
  have hv0 : v ≠ 0 := h0.ne'
  have h1v : 1 - v ≠ 0 := (sub_pos.mpr hv1).ne'
  have hk0' : kap v ≠ 0 := hk0.ne'
  have hn0' : hn v ≠ 0 := hn0.ne'
  have hl' : Real.log 2 ≠ 0 := hl.ne'
  have hK' : 2 * kap v - (1 - 2 * v) ^ 2 ≠ 0 := hK.ne'
  have h2 : HasDerivAt (fun u => 4 * H u * hn u ^ 2 * (2 * kap u - (1 - 2 * u) ^ 2) /
      (Real.log 2 * ((4 * u * (1 - u)) ^ 2 * kap u ^ 3))) (Psi v * Lam v) v := by
    refine hdiv.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.div_apply, Pi.add_apply,
      Nat.cast_ofNat, Nat.reduceSub, pow_one]
    unfold Psi Lam
    rw [hHv]
    field_simp
    ring
  rw [← hfun] at h2
  exact h2

/-! ## Rational lower bound of `Lam` on an interval -/

/-- Lower bound of `Lam` on `[va, vb]` (real form). -/
theorem lam_pos_real {va vb v A1 B2 hnH kL kH : ℝ} (hva0 : 0 < va) (hvbh : vb < 1 / 2)
    (hva : va ≤ v) (hvb : v ≤ vb)
    (hA1 : A1 ≤ -Real.log vb) (hB2 : -Real.log (1 - vb) ≤ B2) (hnum : 0 ≤ A1 - B2)
    (hhn : hn vb ≤ hnH) (hkL : kL ≤ kap vb) (hkH : kap va ≤ kH)
    (hden : 0 < 2 * kL - (1 - 2 * va) ^ 2)
    (hpos : 0 < 3 * (A1 - B2) / hnH -
      (1 - 2 * va) * (1 / (va * (1 - va)) - 4) / (2 * kL - (1 - 2 * va) ^ 2) -
      2 * (1 - 2 * va) / (va * (1 - va)) + 3 * (1 - 2 * vb) / (2 * vb * (1 - vb) * kH)) :
    0 < Lam v := by
  have hv0 : 0 < v := hva0.trans_le hva
  have hvh : v < 1 / 2 := hvb.trans_lt hvbh
  have hv1 : v < 1 := by linarith
  have hvb0 : 0 < vb := hv0.trans_le hvb
  have hv0' : v ≠ 0 := hv0.ne'
  have h1v : 1 - v ≠ 0 := (sub_pos.mpr hv1).ne'
  -- term 1
  have hJlog : J v * Real.log 2 = (-Real.log v) - (-Real.log (1 - v)) := by
    unfold J
    rw [Real.log_div h1v hv0']
    field_simp
    ring
  have hL1b : A1 ≤ -Real.log v := by
    have : -Real.log vb ≤ -Real.log v := by
      have := Real.log_le_log hv0 hvb; linarith
    linarith
  have hL2b : -Real.log (1 - v) ≤ B2 := by
    have : -Real.log (1 - v) ≤ -Real.log (1 - vb) := by
      have := Real.log_le_log (by linarith) (show 1 - vb ≤ 1 - v by linarith); linarith
    linarith
  have hnumv : A1 - B2 ≤ J v * Real.log 2 := by rw [hJlog]; linarith
  have hhnv : hn v ≤ hnH := (hn_mono_half hv0.le hvb hvbh.le).trans hhn
  have hn0 := hn_pos' hv0 hv1
  have t1 : 3 * (A1 - B2) / hnH ≤ 3 * (J v * Real.log 2) / hn v := by
    have e1 : 3 * (A1 - B2) / hnH ≤ 3 * (A1 - B2) / hn v :=
      div_le_div_of_nonneg_left (by linarith) hn0 hhnv
    have e2 : 3 * (A1 - B2) / hn v ≤ 3 * (J v * Real.log 2) / hn v :=
      div_le_div_of_nonneg_right (by linarith) hn0.le
    exact e1.trans e2
  -- kap bounds
  have hkv_hi : kap v ≤ kH := (kap_anti_half hva0 hva hvh.le).trans hkH
  have hk0 := kap_pos hv0 hvh
  -- term 2 (negative part)
  have hK := two_kap_sub_pos hv0 hvh
  have hvv : 0 < v * (1 - v) := mul_pos hv0 (by linarith)
  have hvav : 0 < va * (1 - va) := mul_pos hva0 (by linarith)
  have hprod1 : 0 ≤ (v - va) * (1 - v - va) :=
    mul_nonneg (sub_nonneg.mpr hva) (by linarith)
  have hvav_le : va * (1 - va) ≤ v * (1 - v) := by
    have e : v * (1 - v) - va * (1 - va) = (v - va) * (1 - v - va) := by ring
    linarith
  have hq4 : 4 * (v * (1 - v)) ≤ 1 := by
    have e : 1 - 4 * (v * (1 - v)) = (1 - 2 * v) ^ 2 := by ring
    have := sq_nonneg (1 - 2 * v)
    linarith
  have hnum3 : 0 ≤ (1 - 2 * v) * (1 / (v * (1 - v)) - 4) := by
    apply mul_nonneg (by linarith)
    rw [sub_nonneg, le_div_iff₀ hvv]; exact hq4
  have hnum3_le : (1 - 2 * v) * (1 / (v * (1 - v)) - 4) ≤
      (1 - 2 * va) * (1 / (va * (1 - va)) - 4) := by
    apply mul_le_mul (by linarith) _ _ (by linarith)
    · have : 1 / (v * (1 - v)) ≤ 1 / (va * (1 - va)) := one_div_le_one_div_of_le hvav hvav_le
      linarith
    · rw [sub_nonneg, le_div_iff₀ hvv]; exact hq4
  have hden3 : 2 * kL - (1 - 2 * va) ^ 2 ≤ 2 * kap v - (1 - 2 * v) ^ 2 := by
    have : (1 - 2 * v) ^ 2 ≤ (1 - 2 * va) ^ 2 := by
      have e : (1 - 2 * va) ^ 2 - (1 - 2 * v) ^ 2 = 4 * ((v - va) * (1 - v - va)) := by ring
      linarith
    have : kL ≤ kap v := hkL.trans (kap_anti_half hv0 hvb hvbh.le)
    linarith
  have t3 : -((1 - 2 * va) * (1 / (va * (1 - va)) - 4) / (2 * kL - (1 - 2 * va) ^ 2)) ≤
      (2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v)) / (2 * kap v - (1 - 2 * v) ^ 2) := by
    have e : 2 * (-(1 - 2 * v) / (2 * v * (1 - v))) + 4 * (1 - 2 * v) =
        -((1 - 2 * v) * (1 / (v * (1 - v)) - 4)) := by
      field_simp
      ring
    rw [e, neg_div]
    apply neg_le_neg
    calc (1 - 2 * v) * (1 / (v * (1 - v)) - 4) / (2 * kap v - (1 - 2 * v) ^ 2)
        ≤ (1 - 2 * va) * (1 / (va * (1 - va)) - 4) / (2 * kap v - (1 - 2 * v) ^ 2) :=
          div_le_div_of_nonneg_right hnum3_le hK.le
      _ ≤ (1 - 2 * va) * (1 / (va * (1 - va)) - 4) / (2 * kL - (1 - 2 * va) ^ 2) :=
          div_le_div_of_nonneg_left (hnum3.trans hnum3_le) hden hden3
  -- term 3
  have t4 : -(2 * (1 - 2 * va) / (va * (1 - va))) ≤ -(2 * (4 * (1 - 2 * v)) / (4 * v * (1 - v))) := by
    apply neg_le_neg
    have e : 2 * (4 * (1 - 2 * v)) / (4 * v * (1 - v)) = 2 * (1 - 2 * v) / (v * (1 - v)) := by
      rw [mul_assoc (4 : ℝ) v (1 - v),
        show (2 : ℝ) * (4 * (1 - 2 * v)) = 4 * (2 * (1 - 2 * v)) by ring,
        mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]
    rw [e]
    calc 2 * (1 - 2 * v) / (v * (1 - v)) ≤ 2 * (1 - 2 * va) / (v * (1 - v)) :=
          div_le_div_of_nonneg_right (by linarith) hvv.le
      _ ≤ 2 * (1 - 2 * va) / (va * (1 - va)) :=
          div_le_div_of_nonneg_left (by linarith) hvav hvav_le
  -- term 4
  have hvb_le : v * (1 - v) ≤ vb * (1 - vb) := by
    have hp : 0 ≤ (vb - v) * (1 - vb - v) := mul_nonneg (sub_nonneg.mpr hvb) (by linarith)
    have e : vb * (1 - vb) - v * (1 - v) = (vb - v) * (1 - vb - v) := by ring
    linarith
  have hvbv : 0 < vb * (1 - vb) := mul_pos hvb0 (by linarith)
  have hkh : 0 < kH := hk0.trans_le hkv_hi
  have t5 : 3 * (1 - 2 * vb) / (2 * vb * (1 - vb) * kH) ≤
      -(3 * (-(1 - 2 * v) / (2 * v * (1 - v))) / kap v) := by
    rw [neg_div, mul_neg, neg_div, neg_neg, ← mul_div_assoc, div_div]
    have hp1 : 0 < 2 * v * (1 - v) * kap v := by
      have := mul_pos hvv hk0
      have e : 2 * v * (1 - v) * kap v = 2 * (v * (1 - v) * kap v) := by ring
      rw [e]; linarith
    have hp2 : 0 < 2 * vb * (1 - vb) * kH := by
      have := mul_pos hvbv hkh
      have e : 2 * vb * (1 - vb) * kH = 2 * (vb * (1 - vb) * kH) := by ring
      rw [e]; linarith
    calc 3 * (1 - 2 * vb) / (2 * vb * (1 - vb) * kH)
        ≤ 3 * (1 - 2 * v) / (2 * vb * (1 - vb) * kH) :=
          div_le_div_of_nonneg_right (by linarith) hp2.le
      _ ≤ 3 * (1 - 2 * v) / (2 * v * (1 - v) * kap v) := by
          apply div_le_div_of_nonneg_left (by linarith) hp1
          have := mul_le_mul hvb_le hkv_hi hk0.le hvbv.le
          have e1 : 2 * v * (1 - v) * kap v = 2 * (v * (1 - v) * kap v) := by ring
          have e2 : 2 * vb * (1 - vb) * kH = 2 * (vb * (1 - vb) * kH) := by ring
          rw [e1, e2]; linarith
  have hLam : 3 * (A1 - B2) / hnH -
      (1 - 2 * va) * (1 / (va * (1 - va)) - 4) / (2 * kL - (1 - 2 * va) ^ 2) -
      2 * (1 - 2 * va) / (va * (1 - va)) + 3 * (1 - 2 * vb) / (2 * vb * (1 - vb) * kH) ≤ Lam v := by
    unfold Lam
    linarith only [t1, t3, t4, t5]
  exact hpos.trans_le hLam

/-- Lower bound of `Lam` on `[va, vb]` from the contact data at the endpoints. -/
def lamLo (da db : VD) : ℚ :=
  3 * (db.a1 - db.b2) / db.hnHi -
    (1 - 2 * da.v) * (1 / (da.v * (1 - da.v)) - 4) / (2 * db.kapLo - (1 - 2 * da.v) ^ 2) -
    2 * (1 - 2 * da.v) / (da.v * (1 - da.v)) +
    3 * (1 - 2 * db.v) / (2 * db.v * (1 - db.v) * da.kapHi)

theorem lam_pos_vd {da db : VD} (hda : da.Sound) (hdb : db.Sound) (hb2 : db.v < 1 / 2)
    (hnum : 0 ≤ db.a1 - db.b2) (hden : 0 < 2 * db.kapLo - (1 - 2 * da.v) ^ 2)
    (hpos : 0 < lamLo da db) {v : ℝ} (hva : ((da.v : ℚ) : ℝ) ≤ v) (hvb : v ≤ ((db.v : ℚ) : ℝ)) :
    0 < Lam v := by
  have hva0 : (0 : ℝ) < ((da.v : ℚ) : ℝ) := by exact_mod_cast hda.1
  have hvbh : ((db.v : ℚ) : ℝ) < 1 / 2 := VD.cast_lt_half hb2
  have hnumR : (0 : ℝ) ≤ ((db.a1 : ℚ) : ℝ) - ((db.b2 : ℚ) : ℝ) := by exact_mod_cast hnum
  have hdenR : (0 : ℝ) < 2 * ((db.kapLo : ℚ) : ℝ) - (1 - 2 * ((da.v : ℚ) : ℝ)) ^ 2 := by
    exact_mod_cast hden
  have hq : (0 : ℝ) < ((lamLo da db : ℚ) : ℝ) := by exact_mod_cast hpos
  unfold lamLo at hq
  push_cast at hq
  refine lam_pos_real hva0 hvbh hva hvb hdb.2.2.1 hdb.2.2.2.2.2 hnumR (VD.le_hnHi hdb)
    (VD.kapLo_le_kap hdb) (VD.kap_le_kapHi hda) hdenR ?_
  linarith only [hq]

/-- Interval check: `0 < lamLo` with admissible data and positive denominators. -/
def lamOK (Na Nb : ℕ) : Bool :=
  okN Na && okN Nb && decide ((vd Na).v < (vd Nb).v ∧ (vd Nb).v < 1 / 2 ∧
    0 ≤ (vd Nb).a1 - (vd Nb).b2 ∧ 0 < 2 * (vd Nb).kapLo - (1 - 2 * (vd Na).v) ^ 2 ∧
    0 < lamLo (vd Na) (vd Nb))

theorem lamOK_parts {Na Nb : ℕ} (h : lamOK Na Nb = true) :
    (vd Na).Sound ∧ (vd Nb).Sound ∧ (vd Na).v < (vd Nb).v ∧ (vd Nb).v < 1 / 2 ∧
      0 ≤ (vd Nb).a1 - (vd Nb).b2 ∧ 0 < 2 * (vd Nb).kapLo - (1 - 2 * (vd Na).v) ^ 2 ∧
      0 < lamLo (vd Na) (vd Nb) := by
  unfold lamOK at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  obtain ⟨a, b, c, d, e⟩ := of_decide_eq_true h1.2
  exact ⟨vd_sound h2.1, vd_sound h2.2, a, b, c, d, e⟩

theorem psi_monoOn_seg {Na Nb : ℕ} (h : lamOK Na Nb = true) :
    MonotoneOn Psi (Icc (((vd Na).v : ℚ) : ℝ) (((vd Nb).v : ℚ) : ℝ)) := by
  obtain ⟨da, db, -, hb2, hnum, hden, hpos⟩ := lamOK_parts h
  have hva0 : (0 : ℝ) < (((vd Na).v : ℚ) : ℝ) := by exact_mod_cast da.1
  have hvbh : (((vd Nb).v : ℚ) : ℝ) < 1 / 2 := VD.cast_lt_half hb2
  apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) _ _).monotoneOn
  · intro v hv
    exact (hasDerivAt_Psi (hva0.trans_le hv.1) (hv.2.trans_lt hvbh)).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Icc] at hv
    have h0 : 0 < v := hva0.trans hv.1
    have h1 : v < 1 / 2 := hv.2.trans hvbh
    rw [(hasDerivAt_Psi h0 h1).deriv]
    exact mul_pos (Psi_pos h0 h1) (lam_pos_vd da db hb2 hnum hden hpos hv.1.le hv.2.le)

theorem monotoneOn_Icc_union {f : ℝ → ℝ} {a b c : ℝ} (h1 : MonotoneOn f (Icc a b))
    (h2 : MonotoneOn f (Icc b c)) : MonotoneOn f (Icc a c) := by
  intro x hx y hy hxy
  rcases le_total x b with hxb | hxb
  · rcases le_total y b with hyb | hyb
    · exact h1 ⟨hx.1, hxb⟩ ⟨hy.1, hyb⟩ hxy
    · have hab : a ≤ b := hx.1.trans hxb
      have hbc : b ≤ c := hyb.trans hy.2
      exact (h1 ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb).trans (h2 ⟨le_rfl, hbc⟩ ⟨hyb, hy.2⟩ hyb)
  · exact h2 ⟨hxb, hx.2⟩ ⟨hxb.trans hxy, hy.2⟩ hxy

/-- Consecutive-pair check along a grid. -/
def lamChain : ℕ → List ℕ → Bool
  | _, [] => true
  | a, b :: rest => lamOK a b && lamChain b rest

theorem lamChain_mono : ∀ (l : List ℕ) (a : ℕ), lamChain a l = true →
    MonotoneOn Psi (Icc (((vd a).v : ℚ) : ℝ) (((vd (l.getLastD a)).v : ℚ) : ℝ))
  | [], a, _ => by
    intro x hx y hy _
    have : x = y := le_antisymm (hx.2.trans hy.1) (hy.2.trans hx.1)
    rw [this]
  | b :: rest, a, h => by
    simp only [lamChain, Bool.and_eq_true] at h
    have h1 := psi_monoOn_seg h.1
    have h2 := lamChain_mono rest b h.2
    rw [List.getLastD_cons]
    exact monotoneOn_Icc_union h1 h2

/-! ## The certified monotone range -/

/-- Left end of the monotone range: `2^-10`. -/
def V1N : ℕ := 1073741824
/-- Right end of the monotone range: `⌊0.49 · 2^40⌋ / 2^40`. -/
def V2N : ℕ := 538760697610

/-- Grid (after `V1N`) certifying `Lam > 0` on each consecutive interval. -/
def psiGridTail : List ℕ :=
  [1090519040, 1124073472, 1191182336, 1325400064, 1593835520, 2130706432, 2667577344,
    3204448256, 4278190080, 5351931904, 6425673728, 8573157376, 10720641024, 12868124672,
    17163091968, 21458059264, 25753026560, 34342961152, 42932895744, 51522830336, 68702699520,
    85882568704, 103062437888, 137422176256, 171781914624, 206141652992, 274861129728,
    343580606464, 412300083200, 446659821568, 481019559936, 515379298304, 532559167488,
    538760697610]

theorem psiGrid_ok : lamChain V1N psiGridTail = true := by decide +kernel

theorem psiGrid_last : psiGridTail.getLastD V1N = V2N := by decide

/-- `Psi` is monotone on `[2^-10, V2N/2^40]`. -/
theorem psi_mono : MonotoneOn Psi (Icc ((dyq V1N : ℚ) : ℝ) ((dyq V2N : ℚ) : ℝ)) := by
  have h := lamChain_mono psiGridTail V1N psiGrid_ok
  rw [psiGrid_last, vd_v, vd_v] at h
  exact h

theorem dyq_mono {a b : ℕ} (h : a ≤ b) : dyq a ≤ dyq b := by
  unfold dyq
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast h

/-! ## The bracket bound -/

/-- `Θ'` upper bound on a contact bracket `[Na, Nb]`: the point value `PsiUB(db,db)` inside the
certified monotone range of `Psi`, else the factorwise `PsiUB(da,db)`. -/
def brB (Na Nb : ℕ) : ℚ :=
  if V1N ≤ Na ∧ Nb ≤ V2N then PsiUB (vd Nb) (vd Nb) else PsiUB (vd Na) (vd Nb)

theorem brB_sound {x1 x2 : ℚ} {Na Nb : ℕ} (h : brOK x1 x2 Na Nb = true) {x y : ℝ}
    (hx : (x1 : ℝ) ≤ x) (hxy : x ≤ y) (hy : y ≤ (x2 : ℝ)) :
    e8Theta y - e8Theta x ≤ ((brB Na Nb : ℚ) : ℝ) * (y - x) := by
  unfold brB
  split_ifs with hr
  · obtain ⟨da, db, hx1, -, -, hA, hB, hk⟩ := brOK_parts h
    have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1
    apply theta_sub_le_of_deriv (hx1R.trans_le hx) hxy
    intro t ht
    have ht0 : 0 < t := hx1R.trans_le (hx.trans ht.1)
    rw [deriv_e8Theta_eq_Psi ht0]
    obtain ⟨hc1, hc2⟩ := contact_mem_of_brackets da db hx1 hA hB (hx.trans ht.1) (ht.2.trans hy)
    have hV1 : ((dyq V1N : ℚ) : ℝ) ≤ (((vd Na).v : ℚ) : ℝ) := by
      rw [vd_v]; exact_mod_cast dyq_mono hr.1
    have hV2 : (((vd Nb).v : ℚ) : ℝ) ≤ ((dyq V2N : ℚ) : ℝ) := by
      rw [vd_v]; exact_mod_cast dyq_mono hr.2
    have hm := psi_mono ⟨hV1.trans hc1, hc2.trans hV2⟩ ⟨hV1.trans (hc1.trans hc2), hV2⟩ hc2
    exact hm.trans (Psi_le_PsiUB db db hk le_rfl le_rfl)
  · exact brOK_sound h hx hxy hy

theorem brB_pos {x1 x2 : ℚ} {Na Nb : ℕ} (h : brOK x1 x2 Na Nb = true) :
    (0 : ℝ) < ((brB Na Nb : ℚ) : ℝ) := by
  unfold brB
  split_ifs with hr
  · obtain ⟨da, db, hx1, hx12, hab, hA, hB, hk⟩ := brOK_parts h
    have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1
    have hc := contact_mem_of_brackets da db hx1 hA hB (x := (x1 : ℝ)) le_rfl
      (by exact_mod_cast hx12)
    have hvb0 : (0 : ℝ) < (((vd Nb).v : ℚ) : ℝ) := by exact_mod_cast db.1
    have hvbh : (((vd Nb).v : ℚ) : ℝ) < 1 / 2 := by
      have h1 : (((vd Nb).v : ℚ) : ℝ) ≤ ((dyq V2N : ℚ) : ℝ) := by
        rw [vd_v]; exact_mod_cast dyq_mono hr.2
      have h2 : ((dyq V2N : ℚ) : ℝ) < 1 / 2 := by
        unfold dyq V2N; norm_num
      linarith
    have hle := Psi_le_PsiUB db db hk (v := (((vd Nb).v : ℚ) : ℝ)) le_rfl le_rfl
    have hp := Psi_pos hvb0 hvbh
    linarith
  · exact PsiUB_pos_of_brOK h

#print axioms hasDerivAt_Psi
#print axioms lam_pos_vd
#print axioms psi_mono
#print axioms brB_sound
#print axioms brB_pos

end CKLaneA1.R5

end


