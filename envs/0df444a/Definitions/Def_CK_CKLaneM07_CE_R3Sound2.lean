-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Sound2
-- name    : CK_CKLaneM07_CE_R3Sound2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:29:08.468211+00:00
-- url     : https://prove2.me/theorems/41e55077-fac3-4db1-9096-22a64353d5d7
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Sound2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Sound2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Sound2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Sound2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Sound2.lean)

import Definitions.Def_CK_CKLaneM07_CE_R3Sound

-- ===== source module CKLaneM07.CE.R3Sound2 =====
section

/-!
# Lane M07 / CE-stat row 3: soundness of the box checker `r3BoxOK` (part 2)

`r3Box_sound`: for every real point `(a, z, y)` of a box accepted by `r3BoxOK` with `0 < z < 1`,
`0 < y` and `y ≤ (H a + H b)/20` (`b = a + z y`), `0 ≤ gapLB (H a) (H b) (a + y)`.

Every rational quantity of the checker is turned into a real inequality here: Lane E point enclosures
(`ptOk_sound`, `H_bounds`, `lam_bounds`), N1 slope bounds (`slopeLo_le`, `le_slopeHi`, `theta_ge`,
`hn_bounds`, `kap_bounds`, `J_ge`), N1 `JH_eq`/`Chat_mono`, and the analytic lemmas of `R3Bound` /
`R3Combine` (mean-value bound for `Υ`, contact step, Jensen facts).
-/

set_option autoImplicit false

namespace CKLaneM07.CE.R3

open GeneralCK GeneralCK.Certificates.Mixed Set CKLaneN1 CKLaneN1.Edge CKLaneN1.Capital CKLaneE.FP
  CKLaneM07.CE

/-! ## `C(r) = (1+r) log(1+r) + (1-r) log(1-r)` -/

theorem Cfun_nonneg' {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 ≤ Cfun s := by
  unfold Cfun
  have hp : 0 < 1 + s := by linarith
  have hm : 0 < 1 - s := by linarith
  have e1 := Real.one_sub_inv_le_log_of_pos hp
  have e2 := Real.one_sub_inv_le_log_of_pos hm
  have f1 : (1 + s) * (1 - (1 + s)⁻¹) = s := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ hp.ne']; ring
  have f2 : (1 - s) * (1 - (1 - s)⁻¹) = -s := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ hm.ne']; ring
  have g1 := mul_le_mul_of_nonneg_left e1 hp.le
  have g2 := mul_le_mul_of_nonneg_left e2 hm.le
  linarith

theorem chatHi_ge {s : ℚ} (h0 : 0 < s) (h1 : s < 1) (hp1 : ptOk s = true)
    (hp2 : ptOk (s / (1 + s)) = true) :
    Cfun (s : ℝ) / (s : ℝ) ^ 2 ≤ ((chatHi s : ℚ) : ℝ) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast h0
  have hs1 : (s : ℝ) < 1 := by exact_mod_cast h1
  obtain ⟨-, -, -, hl1⟩ := ptOk_sound hp1
  obtain ⟨-, -, hl2, -⟩ := ptOk_sound hp2
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hcast : (((s / (1 + s) : ℚ)) : ℝ) = (s : ℝ) / (1 + (s : ℝ)) := by push_cast; ring
  rw [hcast] at hl2
  have e : (1 : ℝ) - (s : ℝ) / (1 + (s : ℝ)) = (1 + (s : ℝ))⁻¹ := by
    rw [inv_eq_one_div, eq_div_iff hp.ne', sub_mul, div_mul_cancel₀ _ hp.ne']; ring
  rw [e, Real.log_inv] at hl2
  have k1 : (1 + (s : ℝ)) * Real.log (1 + s) ≤
      (1 + (s : ℝ)) * (-((l1Lo (s / (1 + s)) : ℚ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hp.le
  have k2 : (1 - (s : ℝ)) * Real.log (1 - s) ≤ (1 - (s : ℝ)) * ((l1Hi s : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hl1 (by linarith)
  have hC : Cfun (s : ℝ) ≤ (1 + (s : ℝ)) * (-((l1Lo (s / (1 + s)) : ℚ) : ℝ)) +
      (1 - (s : ℝ)) * ((l1Hi s : ℚ) : ℝ) := by
    unfold Cfun; linarith
  have hsq : (0 : ℝ) < (s : ℝ) ^ 2 := pow_pos hs0 2
  have hchat : ((chatHi s : ℚ) : ℝ) = ((1 + (s : ℝ)) * (-((l1Lo (s / (1 + s)) : ℚ) : ℝ)) +
      (1 - (s : ℝ)) * ((l1Hi s : ℚ) : ℝ)) / (s : ℝ) ^ 2 := by
    unfold chatHi; push_cast; ring
  rw [hchat]
  exact div_le_div_of_nonneg_right hC hsq.le

/-- the Jensen gap `JH = H(M) − (H a + H b)/2` is `O((b−a)²)` with explicit constant -/
theorem JH_le_gen {a b ρ ρ' m0 m1 K1 K2 L : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hρ : (b - a) / (a + b) ≤ ρ) (hρ1 : ρ < 1)
    (hρ' : (b - a) / (2 * (1 - (a + b) / 2)) ≤ ρ') (hρ'1 : ρ' < 1)
    (hm0 : 0 < m0) (hm0' : m0 ≤ (a + b) / 2) (hm1 : (a + b) / 2 ≤ m1) (hm1' : m1 < 1)
    (hK1 : Cfun ρ / ρ ^ 2 ≤ K1) (hK2 : Cfun ρ' / ρ' ^ 2 ≤ K2)
    (hL : 0 < L) (hL2 : L ≤ Real.log 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (b - a) ^ 2 * ((K1 / m0 + K2 / (1 - m1)) / (8 * L)) := by
  rw [JH_eq ha hab hb]
  have hs : 0 < a + b := by linarith
  have hsne : a + b ≠ 0 := hs.ne'
  have hM : 0 < (a + b) / 2 := by linarith
  have hM1 : 0 < 1 - (a + b) / 2 := by linarith
  have hM1ne : 1 - (a + b) / 2 ≠ 0 := hM1.ne'
  have hd : 0 < b - a := by linarith
  have hm1p : 0 < 1 - m1 := by linarith
  have hr : 0 < (b - a) / (a + b) := div_pos hd hs
  have hr' : 0 < (b - a) / (2 * (1 - (a + b) / 2)) := div_pos hd (by linarith)
  have hρ0 : 0 < ρ := hr.trans_le hρ
  have hρ'0 : 0 < ρ' := hr'.trans_le hρ'
  have hK1' : 0 ≤ K1 := le_trans (div_nonneg (Cfun_nonneg' hρ0 hρ1) (sq_nonneg _)) hK1
  have hK2' : 0 ≤ K2 := le_trans (div_nonneg (Cfun_nonneg' hρ'0 hρ'1) (sq_nonneg _)) hK2
  have d1 : Cfun ((b - a) / (a + b)) ≤ K1 * ((b - a) / (a + b)) ^ 2 := by
    have c1 := Chat_mono hr hρ hρ1
    have hρ2 : 0 < ρ ^ 2 := pow_pos hρ0 2
    have : Cfun ((b - a) / (a + b)) ≤ Cfun ρ / ρ ^ 2 * ((b - a) / (a + b)) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ2]; linarith
    exact this.trans (mul_le_mul_of_nonneg_right hK1 (sq_nonneg _))
  have d2 : Cfun ((b - a) / (2 * (1 - (a + b) / 2))) ≤
      K2 * ((b - a) / (2 * (1 - (a + b) / 2))) ^ 2 := by
    have c2 := Chat_mono hr' hρ' hρ'1
    have hρ2 : 0 < ρ' ^ 2 := pow_pos hρ'0 2
    have : Cfun ((b - a) / (2 * (1 - (a + b) / 2))) ≤
        Cfun ρ' / ρ' ^ 2 * ((b - a) / (2 * (1 - (a + b) / 2))) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ2]; linarith
    exact this.trans (mul_le_mul_of_nonneg_right hK2 (sq_nonneg _))
  have e1 : (a + b) / 2 * (K1 * ((b - a) / (a + b)) ^ 2) =
      K1 * (b - a) ^ 2 / (4 * ((a + b) / 2)) := by
    field_simp
    ring
  have e2 : (1 - (a + b) / 2) * (K2 * ((b - a) / (2 * (1 - (a + b) / 2))) ^ 2) =
      K2 * (b - a) ^ 2 / (4 * (1 - (a + b) / 2)) := by
    field_simp
    ring
  have f1 : K1 * (b - a) ^ 2 / (4 * ((a + b) / 2)) ≤ K1 * (b - a) ^ 2 / (4 * m0) :=
    div_le_div_of_nonneg_left (mul_nonneg hK1' (sq_nonneg _)) (by linarith) (by linarith)
  have f2 : K2 * (b - a) ^ 2 / (4 * (1 - (a + b) / 2)) ≤ K2 * (b - a) ^ 2 / (4 * (1 - m1)) :=
    div_le_div_of_nonneg_left (mul_nonneg hK2' (sq_nonneg _)) (by linarith) (by linarith)
  have g1 := mul_le_mul_of_nonneg_left d1 hM.le
  have g2 := mul_le_mul_of_nonneg_left d2 hM1.le
  have hX0 : 0 ≤ (a + b) / 2 * Cfun ((b - a) / (a + b)) +
      (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2))) :=
    add_nonneg (mul_nonneg hM.le (Cfun_nonneg' hr (lt_of_le_of_lt hρ hρ1)))
      (mul_nonneg hM1.le (Cfun_nonneg' hr' (lt_of_le_of_lt hρ' hρ'1)))
  have hXle : (a + b) / 2 * Cfun ((b - a) / (a + b)) +
      (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2))) ≤
      K1 * (b - a) ^ 2 / (4 * m0) + K2 * (b - a) ^ 2 / (4 * (1 - m1)) := by
    linarith
  have hlog : 2 * L ≤ 2 * Real.log 2 := by linarith
  have hY0 : 0 ≤ K1 * (b - a) ^ 2 / (4 * m0) + K2 * (b - a) ^ 2 / (4 * (1 - m1)) := hX0.trans hXle
  calc ((a + b) / 2 * Cfun ((b - a) / (a + b)) +
        (1 - (a + b) / 2) * Cfun ((b - a) / (2 * (1 - (a + b) / 2)))) / (2 * Real.log 2)
      ≤ (K1 * (b - a) ^ 2 / (4 * m0) + K2 * (b - a) ^ 2 / (4 * (1 - m1))) / (2 * Real.log 2) :=
        div_le_div_of_nonneg_right hXle (by linarith)
    _ ≤ (K1 * (b - a) ^ 2 / (4 * m0) + K2 * (b - a) ^ 2 / (4 * (1 - m1))) / (2 * L) :=
        div_le_div_of_nonneg_left hY0 (by linarith) hlog
    _ = (b - a) ^ 2 * ((K1 / m0 + K2 / (1 - m1)) / (8 * L)) := by
        rw [← div_div (K2 * (b - a) ^ 2) 4 (1 - m1)]; ring

/-- the outer-tangent penalty algebra (mean-value form) -/
theorem T4_alg {D K z y b0 b1 R E : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (hz1 : z ≤ 1) (hy : 0 ≤ y)
    (hb0 : b0 ≤ z) (hb1 : z ≤ b1) (hz0 : 0 ≤ z) (hR : R ≤ y * E) (hE : 0 ≤ E) :
    D * ((1 - z) * y) * (2 * K * ((1 - z) * y) + z * y / 2 + R) ≤
      y ^ 2 * (D * (1 - b0) * (2 * K * (1 - b0) + b1 / 2 + E)) := by
  have h1b0 : 0 ≤ 1 - b0 := by linarith
  have hb1' : 0 ≤ b1 := by linarith
  have hQ : 0 ≤ 2 * K * (1 - b0) + b1 / 2 + E := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK) h1b0
    linarith
  have hin : 2 * K * ((1 - z) * y) + z * y / 2 + R ≤ y * (2 * K * (1 - b0) + b1 / 2 + E) := by
    have k1 : K * (1 - z) ≤ K * (1 - b0) := mul_le_mul_of_nonneg_left (by linarith) hK
    have k2 := mul_le_mul_of_nonneg_right k1 hy
    have k3 : z * y ≤ b1 * y := mul_le_mul_of_nonneg_right hb1 hy
    nlinarith
  have hA : 0 ≤ D * ((1 - z) * y) := mul_nonneg hD (mul_nonneg (by linarith) hy)
  calc D * ((1 - z) * y) * (2 * K * ((1 - z) * y) + z * y / 2 + R)
      ≤ D * ((1 - z) * y) * (y * (2 * K * (1 - b0) + b1 / 2 + E)) :=
        mul_le_mul_of_nonneg_left hin hA
    _ = y ^ 2 * (D * (1 - z) * (2 * K * (1 - b0) + b1 / 2 + E)) := by ring
    _ ≤ y ^ 2 * (D * (1 - b0) * (2 * K * (1 - b0) + b1 / 2 + E)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg y)
        apply mul_le_mul_of_nonneg_right _ hQ
        exact mul_le_mul_of_nonneg_left (by linarith) hD

/-! ## casts of the checker quantities -/

theorem bHi_cast (B : B3) : ((bHi B : ℚ) : ℝ) = ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) := by
  unfold bHi; push_cast; ring
theorem MLo_cast (B : B3) :
    ((MLo B : ℚ) : ℝ) = ((B.a0 : ℚ) : ℝ) + ((B.b0 : ℚ) : ℝ) * ((B.c0 : ℚ) : ℝ) / 2 := by
  unfold MLo; push_cast; ring
theorem MHi_cast (B : B3) :
    ((MHi B : ℚ) : ℝ) = ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) / 2 := by
  unfold MHi; push_cast; ring
theorem hLo_cast (B : B3) : ((hLo B : ℚ) : ℝ) = (((Ha0 B : ℚ) : ℝ) + ((Hb0 B : ℚ) : ℝ)) / 2 := by
  unfold hLo; push_cast; ring
theorem hHi_cast (B : B3) : ((hHi B : ℚ) : ℝ) = (((Ha1 B : ℚ) : ℝ) + ((Hb1 B : ℚ) : ℝ)) / 2 := by
  unfold hHi; push_cast; ring
theorem Xq_cast (B : B3) : ((Xq B : ℚ) : ℝ) = ((B.c1 : ℚ) : ℝ) / (2 * ((hLo B : ℚ) : ℝ)) := by
  unfold Xq; push_cast; ring
theorem betaQ_cast (B : B3) : ((betaQ B : ℚ) : ℝ) =
    1 / ((2 * ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) * ((LqHi : ℚ) : ℝ)) := by
  unfold betaQ; push_cast; ring
theorem JMq_cast (B : B3) :
    ((JMq B : ℚ) : ℝ) = ((lamLo (MHi B) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) := by
  unfold JMq; push_cast; ring
theorem rhoHi_cast (B : B3) : ((rhoHi B : ℚ) : ℝ) =
    ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) / (2 * ((B.a0 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) := by
  unfold rhoHi; push_cast; ring
theorem rhopHi_cast (B : B3) : ((rhopHi B : ℚ) : ℝ) =
    ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) / (2 * (1 - ((MHi B : ℚ) : ℝ))) := by
  unfold rhopHi; push_cast; ring
theorem JHn_cast (B : B3) : ((JHn B : ℚ) : ℝ) =
    (((chatHi (rhoHi B) : ℚ) : ℝ) / ((MLo B : ℚ) : ℝ) +
      ((chatHi (rhopHi B) : ℚ) : ℝ) / (1 - ((MHi B : ℚ) : ℝ))) / (8 * ((LqLo : ℚ) : ℝ)) := by
  unfold JHn; push_cast; ring
theorem JHd_cast (B : B3) : ((JHd B : ℚ) : ℝ) =
    ((Hhi (MHi B) : ℚ) : ℝ) - (((Ha0 B : ℚ) : ℝ) + ((Hb0 B : ℚ) : ℝ)) / 2 := by
  unfold JHd; push_cast; ring
theorem kappaQ_cast (B : B3) : ((kappaQ B : ℚ) : ℝ) = ((Hhi (cHi B) : ℚ) : ℝ) /
    ((1 - 2 * ((cHi B : ℚ) : ℝ)) * (((lamLo (cHi B) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) +
      2 * ((Hb0 B : ℚ) : ℝ)) := by
  unfold kappaQ; push_cast; ring
theorem DQ_cast (B : B3) (q : ℚ) : ((DQ B q : ℚ) : ℝ) = ((HnumHi (cHi B) : ℚ) : ℝ) *
    (2 * ((kapHiQ q : ℚ) : ℝ)) / (4 * ((LqLo : ℚ) : ℝ) * (q : ℝ) ^ 2 *
      (1 - ((cHi B : ℚ) : ℝ)) ^ 2 * ((kapLoQ (cHi B) : ℚ) : ℝ) ^ 2) := by
  unfold DQ; push_cast; ring
theorem alphaQ_cast (B : B3) (w : RWit) : ((alphaQ B w : ℚ) : ℝ) =
    ((slopeLo w.v : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) / (4 * ((hHi B : ℚ) : ℝ)) := by
  unfold alphaQ; push_cast; ring
theorem PloQ_cast (B : B3) (w : RWit) : ((PloQ B w : ℚ) : ℝ) =
    ((alphaQ B w : ℚ) : ℝ) * (1 - ((B.b1 : ℚ) : ℝ) ^ 2) + ((betaQ B : ℚ) : ℝ) * ((B.b0 : ℚ) : ℝ) ^ 2 -
      ((T3q B w.q : ℚ) : ℝ) - ((T4q B w : ℚ) : ℝ) := by
  unfold PloQ; push_cast; ring

/-! ## pointwise bounds on an accepted box -/

section pt

variable {B : B3} {a z y : ℝ} (P : PtBox B a z y)
include P

theorem PtBox.hzy : 0 < z * y := mul_pos P.hz0 P.hy
theorem PtBox.M_lo : ((MLo B : ℚ) : ℝ) ≤ (a + (a + z * y)) / 2 := by
  rw [MLo_cast]; linarith [P.a0, P.zy_lo]
theorem PtBox.M_hi : (a + (a + z * y)) / 2 ≤ ((MHi B : ℚ) : ℝ) := by
  rw [MHi_cast]; linarith [P.a1, P.zy_hi]
theorem PtBox.MHi_le : ((MHi B : ℚ) : ℝ) ≤ ((cHi B : ℚ) : ℝ) := by
  rw [MHi_cast, cHi_cast]
  have hc1 : 0 ≤ ((B.c1 : ℚ) : ℝ) := P.hy.le.trans P.y1
  nlinarith [P.b1le]

theorem PtBox.JH_nonneg : 0 ≤ H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 := by
  obtain ⟨-, j2, j3⟩ := P.cfg.jensen
  have hJ := J_pos P.cfg.hM.1 P.cfg.hM.2
  have h := (le_div_iff₀ hJ).mp j3
  nlinarith [mul_nonneg (sub_nonneg.mpr j2) hJ.le]

theorem PtBox.JH_n (hH : okH B = true) (hR : okRho B = true) :
    H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤ (z * y) ^ 2 * ((JHn B : ℚ) : ℝ) ∧
      0 ≤ ((JHn B : ℚ) : ℝ) := by
  simp only [okH, okRho, Bool.and_eq_true, decide_eq_true_eq] at hH hR
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hMLo⟩, hMHi⟩ := hH
  obtain ⟨⟨⟨⟨⟨⟨⟨hr0, hr1⟩, hrpt⟩, hrpt2⟩, hp0⟩, hp1⟩, hppt⟩, hppt2⟩ := hR
  have hMLoR : (0 : ℝ) < ((MLo B : ℚ) : ℝ) := by exact_mod_cast hMLo
  have hMHiR : ((MHi B : ℚ) : ℝ) < 1 := by exact_mod_cast hMHi
  have hch1 := chatHi_ge hr0 hr1 hrpt hrpt2
  have hch2 := chatHi_ge hp0 hp1 hppt hppt2
  have hr0R : (0 : ℝ) < ((rhoHi B : ℚ) : ℝ) := by exact_mod_cast hr0
  have hr1R : ((rhoHi B : ℚ) : ℝ) < 1 := by exact_mod_cast hr1
  have hp0R : (0 : ℝ) < ((rhopHi B : ℚ) : ℝ) := by exact_mod_cast hp0
  have hp1R : ((rhopHi B : ℚ) : ℝ) < 1 := by exact_mod_cast hp1
  have hs1 : 0 ≤ ((chatHi (rhoHi B) : ℚ) : ℝ) :=
    le_trans (div_nonneg (Cfun_nonneg' hr0R hr1R) (sq_nonneg _)) hch1
  have hs2 : 0 ≤ ((chatHi (rhopHi B) : ℚ) : ℝ) :=
    le_trans (div_nonneg (Cfun_nonneg' hp0R hp1R) (sq_nonneg _)) hch2
  have hL := LqLo_pos
  have hJHn0 : 0 ≤ ((JHn B : ℚ) : ℝ) := by
    rw [JHn_cast]
    have h1m : 0 < 1 - ((MHi B : ℚ) : ℝ) := by linarith
    exact div_nonneg (add_nonneg (div_nonneg hs1 hMLoR.le) (div_nonneg hs2 h1m.le)) (by linarith)
  refine ⟨?_, hJHn0⟩
  have hab : a < a + z * y := by linarith [P.hzy]
  have hb1 : a + z * y < 1 := by linarith [P.b_lt_c, P.c_half]
  have hρ : (a + z * y - a) / (a + (a + z * y)) ≤ ((rhoHi B : ℚ) : ℝ) := by
    rw [rhoHi_cast, show a + z * y - a = z * y by ring]
    have hden1 : 0 < a + (a + z * y) := by linarith [P.ha, P.hzy]
    have hbc : 0 ≤ ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) := P.hzy.le.trans P.zy_hi
    have hden2 : 0 < 2 * ((B.a0 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ) := by
      linarith [P.pa0]
    rw [div_le_div_iff₀ hden1 hden2]
    have k1 := mul_le_mul_of_nonneg_right P.a0 P.hzy.le
    have k2 := mul_le_mul_of_nonneg_left P.zy_hi P.ha.le
    nlinarith [k1, k2]
  have hρ' : (a + z * y - a) / (2 * (1 - (a + (a + z * y)) / 2)) ≤ ((rhopHi B : ℚ) : ℝ) := by
    rw [rhopHi_cast, show a + z * y - a = z * y by ring]
    have hM' := P.M_hi
    exact div_le_div₀ (P.hzy.le.trans P.zy_hi) P.zy_hi (by linarith) (by linarith)
  have hg := JH_le_gen P.ha hab hb1 hρ hr1R hρ' hp1R hMLoR P.M_lo P.M_hi hMHiR hch1 hch2 hL
    LqLo_le'
  rw [JHn_cast]
  rw [show a + z * y - a = z * y by ring] at hg
  exact hg

theorem PtBox.JH_d (hH : okH B = true) :
    H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤ ((JHd B : ℚ) : ℝ) := by
  simp only [okH, Bool.and_eq_true, decide_eq_true_eq] at hH
  obtain ⟨⟨⟨⟨⟨-, hMpt⟩, -⟩, -⟩, -⟩, -⟩ := hH
  have hM0 : 0 ≤ (a + (a + z * y)) / 2 := by linarith [P.ha, P.hzy]
  have hHM : H ((a + (a + z * y)) / 2) ≤ ((Hhi (MHi B) : ℚ) : ℝ) :=
    H_le_hi hMpt hM0 P.M_hi (by linarith [P.MHi_le, P.hcHi])
  rw [JHd_cast]
  linarith [P.Ha_lo, P.Hb_lo]

theorem PtBox.JH_up (hH : okH B = true) (hR : okRho B = true) :
    H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤ ((JHup B : ℚ) : ℝ) := by
  obtain ⟨hn, hn0⟩ := P.JH_n hH hR
  have hd := P.JH_d hH
  have hzy2 : (z * y) ^ 2 ≤ (((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ P.hzy.le P.zy_hi 2
  have h1 : H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤
      ((B.b1 : ℚ) : ℝ) ^ 2 * ((B.c1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ) := by
    have k := mul_le_mul_of_nonneg_right hzy2 hn0
    rw [mul_pow] at k
    linarith
  have en : ((B.b1 ^ 2 * B.c1 ^ 2 * JHn B : ℚ) : ℝ) =
      ((B.b1 : ℚ) : ℝ) ^ 2 * ((B.c1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ) := by
    push_cast; ring
  unfold JHup
  split_ifs
  · rw [Rat.cast_min, en]
    exact le_min h1 hd
  · rw [en]
    exact h1

theorem PtBox.JM (hH : okH B = true) :
    0 < ((JMq B : ℚ) : ℝ) ∧ ((JMq B : ℚ) : ℝ) ≤ J ((a + (a + z * y)) / 2) := by
  simp only [okH, Bool.and_eq_true, decide_eq_true_eq] at hH
  obtain ⟨⟨⟨⟨⟨-, hMpt⟩, hlam⟩, hJM⟩, -⟩, hMHi⟩ := hH
  have hMHiR : ((MHi B : ℚ) : ℝ) < 1 := by exact_mod_cast hMHi
  refine ⟨by exact_mod_cast hJM, ?_⟩
  rw [JMq_cast]
  have hM0 : 0 < (a + (a + z * y)) / 2 := by linarith [P.ha, P.hzy]
  exact (J_ge hMpt hlam).trans (J_anti hM0 P.M_hi hMHiR)

theorem PtBox.q_le (hH : okH B = true) (hR : okRho B = true) {w : RWit} (hQ : okQ B w = true) :
    0 < (w.q : ℝ) ∧ (w.q : ℝ) ≤ entropyInverse ((H a + H (a + z * y)) / 2) ∧
      slopeHiOk w.q = true := by
  simp only [okQ, Bool.and_eq_true, decide_eq_true_eq] at hQ
  obtain ⟨⟨hq0, hqs⟩, hqc⟩ := hQ
  refine ⟨by exact_mod_cast hq0, ?_, hqs⟩
  obtain ⟨j1, j2, j3⟩ := P.cfg.jensen
  rcases hqc with h | h
  · have h' : (w.q : ℝ) ≤ ((B.a0 : ℚ) : ℝ) := by exact_mod_cast h
    linarith [P.a0]
  · have h' : (w.q : ℝ) ≤ ((MLo B : ℚ) : ℝ) - ((JHup B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ) := by
      exact_mod_cast h
    obtain ⟨hJM0, hJM⟩ := P.JM hH
    have hJpos : 0 < J ((a + (a + z * y)) / 2) := hJM0.trans_le hJM
    have hup := P.JH_up hH hR
    have hJH0 := P.JH_nonneg
    have k1 : (H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) /
        J ((a + (a + z * y)) / 2) ≤ ((JHup B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ) :=
      (div_le_div_of_nonneg_right hup hJpos.le).trans
        (div_le_div_of_nonneg_left (hJH0.trans hup) hJM0 hJM)
    linarith [P.M_lo]

theorem PtBox.T3 (hH : okH B = true) (hR : okRho B = true) {w : RWit} (hQ : okQ B w = true) :
    radialSlope (entropyInverse ((H a + H (a + z * y)) / 2)) *
        (a + (a + z * y) - 2 * entropyInverse ((H a + H (a + z * y)) / 2)) ≤
      y ^ 2 * ((T3q B w.q : ℚ) : ℝ) := by
  obtain ⟨hq0, hq, hqs⟩ := P.q_le hH hR hQ
  have h := P.cfg.T3 hq0 hq
  have hqs' := hqs
  simp only [slopeHiOk, Bool.and_eq_true, decide_eq_true_eq] at hqs'
  obtain ⟨⟨-, hqh⟩, -⟩ := hqs'
  have hqhR : (w.q : ℝ) < 1 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hqh
    push_cast at this
    linarith
  have hU0 : 0 < radialSlope (w.q : ℝ) := ups_pos hq0 hqhR
  have hU1 : radialSlope (w.q : ℝ) ≤ ((slopeHi w.q : ℚ) : ℝ) := le_slopeHi hqs
  obtain ⟨hJM0, hJM⟩ := P.JM hH
  obtain ⟨hn, hn0⟩ := P.JH_n hH hR
  have hd := P.JH_d hH
  have hJH0 := P.JH_nonneg
  have hJpos : 0 < J ((a + (a + z * y)) / 2) := hJM0.trans_le hJM
  have hR0 : 0 ≤ (H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) /
      J ((a + (a + z * y)) / 2) := div_nonneg hJH0 hJpos.le
  have hsl0 : 0 ≤ ((slopeHi w.q : ℚ) : ℝ) := hU0.le.trans hU1
  have key : radialSlope (entropyInverse ((H a + H (a + z * y)) / 2)) *
        (a + (a + z * y) - 2 * entropyInverse ((H a + H (a + z * y)) / 2)) ≤
      ((slopeHi w.q : ℚ) : ℝ) * (2 * ((H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) /
        J ((a + (a + z * y)) / 2))) :=
    h.trans (mul_le_mul_of_nonneg_right hU1 (by linarith))
  have hz2 : z ^ 2 ≤ ((B.b1 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ P.hz0.le P.z1 2
  have bn : (H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) / J ((a + (a + z * y)) / 2) ≤
      y ^ 2 * (((B.b1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ)) / ((JMq B : ℚ) : ℝ) := by
    have e1 : H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤
        y ^ 2 * (((B.b1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ)) := by
      have k := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hz2 hn0) (sq_nonneg y)
      have e : (z * y) ^ 2 * ((JHn B : ℚ) : ℝ) = y ^ 2 * (z ^ 2 * ((JHn B : ℚ) : ℝ)) := by ring
      linarith
    have hnum0 : 0 ≤ y ^ 2 * (((B.b1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ)) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hn0)
    exact (div_le_div_of_nonneg_right e1 hJpos.le).trans (div_le_div_of_nonneg_left hnum0 hJM0 hJM)
  have fn : radialSlope (entropyInverse ((H a + H (a + z * y)) / 2)) *
        (a + (a + z * y) - 2 * entropyInverse ((H a + H (a + z * y)) / 2)) ≤
      y ^ 2 * (((slopeHi w.q : ℚ) : ℝ) * 2 * (((B.b1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ)) /
        ((JMq B : ℚ) : ℝ)) := by
    have k := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bn (by norm_num : (0 : ℝ) ≤ 2))
      hsl0
    have e : ((slopeHi w.q : ℚ) : ℝ) * (2 * (y ^ 2 * (((B.b1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ)) /
        ((JMq B : ℚ) : ℝ))) = y ^ 2 * (((slopeHi w.q : ℚ) : ℝ) * 2 * (((B.b1 : ℚ) : ℝ) ^ 2 *
          ((JHn B : ℚ) : ℝ)) / ((JMq B : ℚ) : ℝ)) := by ring
    linarith
  have en : ((slopeHi w.q * 2 * (B.b1 ^ 2 * JHn B) / JMq B : ℚ) : ℝ) =
      ((slopeHi w.q : ℚ) : ℝ) * 2 * (((B.b1 : ℚ) : ℝ) ^ 2 * ((JHn B : ℚ) : ℝ)) /
        ((JMq B : ℚ) : ℝ) := by
    push_cast; ring
  unfold T3q
  split_ifs with hc0
  · rw [Rat.cast_min, mul_min_of_nonneg _ _ (sq_nonneg y), en]
    refine le_min fn ?_
    have hc0R : (0 : ℝ) < ((B.c0 : ℚ) : ℝ) := by exact_mod_cast hc0
    have hJHd0 : 0 ≤ ((JHd B : ℚ) : ℝ) := hJH0.trans hd
    have bd : (H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) /
        J ((a + (a + z * y)) / 2) ≤ ((JHd B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ) :=
      (div_le_div_of_nonneg_right hd hJpos.le).trans (div_le_div_of_nonneg_left hJHd0 hJM0 hJM)
    have ed : ((slopeHi w.q * 2 * JHd B / (JMq B * B.c0 ^ 2) : ℚ) : ℝ) =
        ((slopeHi w.q : ℚ) : ℝ) * 2 * ((JHd B : ℚ) : ℝ) /
          (((JMq B : ℚ) : ℝ) * ((B.c0 : ℚ) : ℝ) ^ 2) := by
      push_cast; ring
    rw [ed]
    have hc2 : 0 < ((B.c0 : ℚ) : ℝ) ^ 2 := pow_pos hc0R 2
    have hy2 : ((B.c0 : ℚ) : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hc0R.le P.y0 2
    have hS : 0 ≤ ((slopeHi w.q : ℚ) : ℝ) * 2 * ((JHd B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg hsl0 (by norm_num)) hJHd0) hJM0.le
    have hq1 : 1 ≤ y ^ 2 / ((B.c0 : ℚ) : ℝ) ^ 2 := by rw [le_div_iff₀ hc2]; linarith
    have e2 : y ^ 2 * (((slopeHi w.q : ℚ) : ℝ) * 2 * ((JHd B : ℚ) : ℝ) /
        (((JMq B : ℚ) : ℝ) * ((B.c0 : ℚ) : ℝ) ^ 2)) =
        ((slopeHi w.q : ℚ) : ℝ) * 2 * ((JHd B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ) *
          (y ^ 2 / ((B.c0 : ℚ) : ℝ) ^ 2) := by ring
    rw [e2]
    have k1 := le_mul_of_one_le_right hS hq1
    have k2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bd (by norm_num : (0 : ℝ) ≤ 2))
      hsl0
    have e3 : ((slopeHi w.q : ℚ) : ℝ) * (2 * (((JHd B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ))) =
        ((slopeHi w.q : ℚ) : ℝ) * 2 * ((JHd B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ) := by ring
    linarith
  · rw [en]; exact fn

theorem PtBox.JH_E1 (hH : okH B = true) (hR : okRho B = true) :
    H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤ y * ((E1q B : ℚ) : ℝ) := by
  obtain ⟨hn, hn0⟩ := P.JH_n hH hR
  have hd := P.JH_d hH
  have hJH0 := P.JH_nonneg
  have hz2 : z ^ 2 ≤ ((B.b1 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ P.hz0.le P.z1 2
  have h1 : H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2 ≤
      y * (((B.b1 : ℚ) : ℝ) ^ 2 * ((B.c1 : ℚ) : ℝ) * ((JHn B : ℚ) : ℝ)) := by
    have k1 : z ^ 2 * y ≤ ((B.b1 : ℚ) : ℝ) ^ 2 * ((B.c1 : ℚ) : ℝ) :=
      mul_le_mul hz2 P.y1 P.hy.le (sq_nonneg _)
    have k2 := mul_le_mul_of_nonneg_right k1 (mul_nonneg P.hy.le hn0)
    have e : (z * y) ^ 2 * ((JHn B : ℚ) : ℝ) = z ^ 2 * y * (y * ((JHn B : ℚ) : ℝ)) := by ring
    have e2 : y * (((B.b1 : ℚ) : ℝ) ^ 2 * ((B.c1 : ℚ) : ℝ) * ((JHn B : ℚ) : ℝ)) =
        ((B.b1 : ℚ) : ℝ) ^ 2 * ((B.c1 : ℚ) : ℝ) * (y * ((JHn B : ℚ) : ℝ)) := by ring
    linarith
  have en : ((B.b1 ^ 2 * B.c1 * JHn B : ℚ) : ℝ) =
      ((B.b1 : ℚ) : ℝ) ^ 2 * ((B.c1 : ℚ) : ℝ) * ((JHn B : ℚ) : ℝ) := by
    push_cast; ring
  unfold E1q
  split_ifs with hc0
  · rw [Rat.cast_min, mul_min_of_nonneg _ _ P.hy.le, en]
    refine le_min h1 ?_
    have hc0R : (0 : ℝ) < ((B.c0 : ℚ) : ℝ) := by exact_mod_cast hc0
    have ed : ((JHd B / B.c0 : ℚ) : ℝ) = ((JHd B : ℚ) : ℝ) / ((B.c0 : ℚ) : ℝ) := by
      push_cast; ring
    rw [ed]
    have hJHd0 : 0 ≤ ((JHd B : ℚ) : ℝ) := hJH0.trans hd
    have k : ((JHd B : ℚ) : ℝ) ≤ y * (((JHd B : ℚ) : ℝ) / ((B.c0 : ℚ) : ℝ)) := by
      rw [mul_div_assoc', le_div_iff₀ hc0R]
      nlinarith [P.y0]
    linarith
  · rw [en]; exact h1

theorem PtBox.kappa (hC : okC B = true) :
    H (a + y) / ((1 - 2 * (a + y)) * J (a + y) + 2 * H (a + z * y)) ≤ ((kappaQ B : ℚ) : ℝ) ∧
      0 ≤ ((kappaQ B : ℚ) : ℝ) := by
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨hcpt, hlam⟩, -⟩, hkden⟩, -⟩ := hC
  have hc := P.c_le
  have hch := P.hcHi
  have hch2 := P.c_half
  have hc0 : 0 < a + y := by linarith [P.ha, P.hy]
  have hHc : H (a + y) ≤ ((Hhi (cHi B) : ℚ) : ℝ) := H_le_hi hcpt hc0.le hc (by linarith)
  have hJ1 : J ((cHi B : ℚ) : ℝ) ≤ J (a + y) := J_anti hc0 hc (by linarith)
  have hJ2 := J_ge hcpt hlam
  have hLq : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := log2_pos.trans_le LqHi_ge'
  have hlamR : (0 : ℝ) ≤ ((lamLo (cHi B) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) := by
    have : (0 : ℝ) ≤ ((lamLo (cHi B) : ℚ) : ℝ) := by exact_mod_cast hlam
    exact div_nonneg this hLq.le
  have hden : (1 - 2 * ((cHi B : ℚ) : ℝ)) * (((lamLo (cHi B) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) +
      2 * ((Hb0 B : ℚ) : ℝ) ≤ (1 - 2 * (a + y)) * J (a + y) + 2 * H (a + z * y) := by
    have e1 : (1 - 2 * ((cHi B : ℚ) : ℝ)) * (((lamLo (cHi B) : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) ≤
        (1 - 2 * (a + y)) * J (a + y) :=
      mul_le_mul (by linarith) (hJ2.trans hJ1) hlamR (by linarith)
    linarith [P.Hb_lo]
  have hkdenR : (0 : ℝ) < (1 - 2 * ((cHi B : ℚ) : ℝ)) * (((lamLo (cHi B) : ℚ) : ℝ) /
      ((LqHi : ℚ) : ℝ)) + 2 * ((Hb0 B : ℚ) : ℝ) := by exact_mod_cast hkden
  have hHhi0 : (0 : ℝ) ≤ ((Hhi (cHi B) : ℚ) : ℝ) := (H_nonneg hc0.le (by linarith)).trans hHc
  rw [kappaQ_cast]
  exact ⟨div_le_div₀ hHhi0 hHc hkdenR hden, div_nonneg hHhi0 hkdenR.le⟩

theorem PtBox.dUps_DQ (hC : okC B = true) {q : ℚ} (hqs : slopeHiOk q = true) :
    dUpsBound (q : ℝ) ((cHi B : ℚ) : ℝ) ≤ ((DQ B q : ℚ) : ℝ) ∧ 0 ≤ ((DQ B q : ℚ) : ℝ) := by
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨hcpt, -⟩, hkap⟩, -⟩, -⟩ := hC
  have hqs' := hqs
  simp only [slopeHiOk, Bool.and_eq_true, decide_eq_true_eq] at hqs'
  obtain ⟨⟨hqpt, hqh⟩, -⟩ := hqs'
  obtain ⟨hq0, -⟩ := ptOk_pos hqpt
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqhR : (q : ℝ) < 1 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hqh; push_cast at this; linarith
  have hch := P.hcHi
  have hc0 : (0 : ℝ) < ((cHi B : ℚ) : ℝ) := by linarith [P.c_le, P.ha, P.hy]
  have hkapR : (0 : ℝ) < ((kapLoQ (cHi B) : ℚ) : ℝ) := by exact_mod_cast hkap
  obtain ⟨-, hn2⟩ := hn_bounds hcpt
  obtain ⟨hk1, -⟩ := kap_bounds hcpt
  obtain ⟨-, hkq2⟩ := kap_bounds hqpt
  have hnc0 : 0 < hn ((cHi B : ℚ) : ℝ) := hn_pos' hc0 (by linarith)
  have hkq0 : 0 < kap (q : ℝ) := kap_pos hq0R hqhR
  have hL := LqLo_pos
  have hL2 := LqLo_le'
  have hL0 := log2_pos
  have h1c : (0 : ℝ) < 1 - ((cHi B : ℚ) : ℝ) := by linarith
  have hnum : hn ((cHi B : ℚ) : ℝ) * (2 * kap (q : ℝ)) ≤
      ((HnumHi (cHi B) : ℚ) : ℝ) * (2 * ((kapHiQ q : ℚ) : ℝ)) :=
    mul_le_mul hn2 (by linarith) (by linarith) (hnc0.le.trans hn2)
  have hnum0 : 0 ≤ ((HnumHi (cHi B) : ℚ) : ℝ) * (2 * ((kapHiQ q : ℚ) : ℝ)) :=
    mul_nonneg (hnc0.le.trans hn2) (by linarith)
  have hdQ : 0 < 4 * ((LqLo : ℚ) : ℝ) * (q : ℝ) ^ 2 * (1 - ((cHi B : ℚ) : ℝ)) ^ 2 *
      ((kapLoQ (cHi B) : ℚ) : ℝ) ^ 2 :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hL) (pow_pos hq0R 2)) (pow_pos h1c 2))
      (pow_pos hkapR 2)
  have hdle : 4 * ((LqLo : ℚ) : ℝ) * (q : ℝ) ^ 2 * (1 - ((cHi B : ℚ) : ℝ)) ^ 2 *
      ((kapLoQ (cHi B) : ℚ) : ℝ) ^ 2 ≤
      4 * Real.log 2 * (q : ℝ) ^ 2 * (1 - ((cHi B : ℚ) : ℝ)) ^ 2 * kap ((cHi B : ℚ) : ℝ) ^ 2 := by
    have k1 : ((kapLoQ (cHi B) : ℚ) : ℝ) ^ 2 ≤ kap ((cHi B : ℚ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ hkapR.le hk1 2
    have hA : 0 ≤ (q : ℝ) ^ 2 * (1 - ((cHi B : ℚ) : ℝ)) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have k2 : 4 * ((LqLo : ℚ) : ℝ) * (q : ℝ) ^ 2 * (1 - ((cHi B : ℚ) : ℝ)) ^ 2 ≤
        4 * Real.log 2 * (q : ℝ) ^ 2 * (1 - ((cHi B : ℚ) : ℝ)) ^ 2 := by
      have k := mul_le_mul_of_nonneg_right hL2 hA
      nlinarith [k]
    have hB : 0 ≤ 4 * Real.log 2 * (q : ℝ) ^ 2 * (1 - ((cHi B : ℚ) : ℝ)) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL0.le) (sq_nonneg _)) (sq_nonneg _)
    exact mul_le_mul k2 k1 (sq_nonneg _) hB
  have hdb : dUpsBound (q : ℝ) ((cHi B : ℚ) : ℝ) ≤ ((HnumHi (cHi B) : ℚ) : ℝ) *
      (2 * ((kapHiQ q : ℚ) : ℝ)) / (4 * ((LqLo : ℚ) : ℝ) * (q : ℝ) ^ 2 *
        (1 - ((cHi B : ℚ) : ℝ)) ^ 2 * ((kapLoQ (cHi B) : ℚ) : ℝ) ^ 2) := by
    unfold dUpsBound
    exact div_le_div₀ hnum0 hnum hdQ hdle
  rw [DQ_cast]
  exact ⟨hdb, div_nonneg hnum0 hdQ.le⟩

theorem PtBox.T4 (hH : okH B = true) (hC : okC B = true) (hR : okRho B = true) {w : RWit}
    (hQ : okQ B w = true) (h4 : okT4 B w = true) :
    (radialSlope (entropyInverse ((H a + H (a + z * y)) / 2)) -
        radialSlope (radialContact (1 - 2 * (a + y)) (H (a + z * y)))) * (a + y - (a + z * y)) ≤
      y ^ 2 * ((T4q B w : ℚ) : ℝ) := by
  obtain ⟨hq0, hq, hqs⟩ := P.q_le hH hR hQ
  obtain ⟨hκ, hκ0⟩ := P.kappa hC
  have ecb : a + y - (a + z * y) = (1 - z) * y := by ring
  have h1z : 0 ≤ 1 - z := by linarith [P.hz1]
  have h1b : 1 - z ≤ 1 - ((B.b0 : ℚ) : ℝ) := by linarith [P.z0]
  have hcb0 : 0 ≤ a + y - (a + z * y) := by rw [ecb]; exact mul_nonneg h1z P.hy.le
  unfold okT4 at h4
  unfold T4q
  by_cases hm : w.mvt = true
  · rw [if_pos hm] at h4
    rw [if_pos hm]
    obtain ⟨hDQ, hDQ0⟩ := P.dUps_DQ hC hqs
    have hD : ∀ w' ∈ Icc (w.q : ℝ) (a + y), dUps w' ≤ ((DQ B w.q : ℚ) : ℝ) := fun w' hw' =>
      (dUps_le hq0 hw'.1 (hw'.2.trans P.c_le) P.hcHi).trans hDQ
    have h := P.cfg.T4 hq0 hq hD hκ
    rw [ecb, show a + z * y - a = z * y by ring] at h
    rw [ecb]
    have hE := P.JH_E1 hH hR
    obtain ⟨hJM0, hJM⟩ := P.JM hH
    have hJpos : 0 < J ((a + (a + z * y)) / 2) := hJM0.trans_le hJM
    have hJH0 := P.JH_nonneg
    have hE0 : 0 ≤ ((E1q B : ℚ) : ℝ) := by
      have k := hJH0.trans hE
      nlinarith [P.hy]
    have hR' : (H ((a + (a + z * y)) / 2) - (H a + H (a + z * y)) / 2) /
        J ((a + (a + z * y)) / 2) ≤ y * (((E1q B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ)) := by
      have k := (div_le_div_of_nonneg_right hE hJpos.le).trans
        (div_le_div_of_nonneg_left (mul_nonneg P.hy.le hE0) hJM0 hJM)
      rw [mul_div_assoc] at k
      exact k
    have hT := T4_alg hDQ0 hκ0 P.hz1.le P.hy.le P.z0 P.z1 P.hz0.le hR' (div_nonneg hE0 hJM0.le)
    have eT : ((DQ B w.q * (1 - B.b0) * (2 * kappaQ B * (1 - B.b0) + B.b1 / 2 + E1q B / JMq B) :
        ℚ) : ℝ) = ((DQ B w.q : ℚ) : ℝ) * (1 - ((B.b0 : ℚ) : ℝ)) * (2 * ((kappaQ B : ℚ) : ℝ) *
          (1 - ((B.b0 : ℚ) : ℝ)) + ((B.b1 : ℚ) : ℝ) / 2 + ((E1q B : ℚ) : ℝ) / ((JMq B : ℚ) : ℝ)) := by
      push_cast; ring
    rw [eT]
    linarith
  · rw [if_neg hm] at h4
    rw [if_neg hm]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
    obtain ⟨⟨⟨⟨hc0, hts⟩, hth⟩, htC⟩, hS⟩ := h4
    have hc0R : (0 : ℝ) < ((B.c0 : ℚ) : ℝ) := by exact_mod_cast hc0
    have hthR : (w.t : ℝ) < 1 / 2 := by
      have := (Rat.cast_lt (K := ℝ)).mpr hth; push_cast at this; linarith
    have htCR : min ((cHi B : ℚ) : ℝ) (((bHi B : ℚ) : ℝ) + 2 * ((kappaQ B : ℚ) : ℝ) *
        (1 - ((B.b0 : ℚ) : ℝ)) * ((B.c1 : ℚ) : ℝ)) ≤ (w.t : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr htC
      push_cast at this
      exact this
    obtain ⟨t1, t2⟩ := P.cfg.contact
    have hstep := contact_step P.cfg.hb0 P.cfg.hbc P.cfg.hc
    have htc1 : radialContact (1 - 2 * (a + y)) (H (a + z * y)) ≤ ((cHi B : ℚ) : ℝ) := by
      linarith [P.c_le]
    have htc2 : radialContact (1 - 2 * (a + y)) (H (a + z * y)) ≤ ((bHi B : ℚ) : ℝ) +
        2 * ((kappaQ B : ℚ) : ℝ) * (1 - ((B.b0 : ℚ) : ℝ)) * ((B.c1 : ℚ) : ℝ) := by
      have hcb : a + y - (a + z * y) ≤ (1 - ((B.b0 : ℚ) : ℝ)) * ((B.c1 : ℚ) : ℝ) := by
        rw [ecb]; exact mul_le_mul h1b P.y1 P.hy.le (by linarith [P.z0, P.hz1])
      have k1 : 2 * (a + y - (a + z * y)) *
          (H (a + y) / ((1 - 2 * (a + y)) * J (a + y) + 2 * H (a + z * y))) ≤
          2 * (a + y - (a + z * y)) * ((kappaQ B : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hκ (by linarith)
      have k2 : 2 * (a + y - (a + z * y)) * ((kappaQ B : ℚ) : ℝ) ≤
          2 * ((1 - ((B.b0 : ℚ) : ℝ)) * ((B.c1 : ℚ) : ℝ)) * ((kappaQ B : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hκ0
      nlinarith [P.b_hi]
    have htt : radialContact (1 - 2 * (a + y)) (H (a + z * y)) ≤ (w.t : ℝ) :=
      (le_min htc1 htc2).trans htCR
    have h := P.cfg.T4' hq0 hq htt hthR
    have hSR : (0 : ℝ) ≤ ((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hS; push_cast at this; linarith
    have hU1 := le_slopeHi hqs
    have hU2 := slopeLo_le hts
    have k1 : (radialSlope (w.q : ℝ) - radialSlope (w.t : ℝ)) * (a + y - (a + z * y)) ≤
        (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * (a + y - (a + z * y)) :=
      mul_le_mul_of_nonneg_right (by linarith) hcb0
    have eT : ((((slopeHi w.q - slopeLo w.t) * (1 - B.b0) / B.c0) : ℚ) : ℝ) =
        (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * (1 - ((B.b0 : ℚ) : ℝ)) /
          ((B.c0 : ℚ) : ℝ) := by
      push_cast; ring
    rw [eT]
    have k2 : (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * (a + y - (a + z * y)) ≤
        y ^ 2 * ((((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * (1 - ((B.b0 : ℚ) : ℝ)) /
          ((B.c0 : ℚ) : ℝ)) := by
      rw [ecb]
      have hyc : y ≤ y ^ 2 / ((B.c0 : ℚ) : ℝ) := by
        rw [le_div_iff₀ hc0R]; nlinarith [P.y0, P.hy]
      have e : y ^ 2 * ((((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) *
          (1 - ((B.b0 : ℚ) : ℝ)) / ((B.c0 : ℚ) : ℝ)) =
          (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * (1 - ((B.b0 : ℚ) : ℝ)) *
            (y ^ 2 / ((B.c0 : ℚ) : ℝ)) := by ring
      rw [e]
      have hS1 : 0 ≤ (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) *
          (1 - ((B.b0 : ℚ) : ℝ)) := mul_nonneg hSR (by linarith [P.z0, P.hz1])
      calc (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * ((1 - z) * y)
          ≤ (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * ((1 - ((B.b0 : ℚ) : ℝ)) * y) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1b P.hy.le) hSR
        _ = (((slopeHi w.q : ℚ) : ℝ) - ((slopeLo w.t : ℚ) : ℝ)) * (1 - ((B.b0 : ℚ) : ℝ)) * y := by
            ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hyc hS1
    linarith

theorem PtBox.T12 (hH : okH B = true) (hC : okC B = true) {w : RWit} (hT : okTheta B w = true) :
    (a + y - a) / (2 * ((H a + H (a + z * y)) / 2)) ≤ ((Xq B : ℚ) : ℝ) ∧
    y ^ 2 * (((alphaQ B w : ℚ) : ℝ) * (1 - ((B.b1 : ℚ) : ℝ) ^ 2) +
        ((betaQ B : ℚ) : ℝ) * ((B.b0 : ℚ) : ℝ) ^ 2) ≤
      e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) * ((a + y - a) ^ 2 - (a + z * y - a) ^ 2) /
          (4 * ((H a + H (a + z * y)) / 2)) +
        (a + z * y - a) ^ 2 / ((a + (a + z * y)) * Real.log 2) := by
  simp only [okH, Bool.and_eq_true, decide_eq_true_eq] at hH
  obtain ⟨⟨⟨⟨⟨hhLo, -⟩, -⟩, -⟩, -⟩, -⟩ := hH
  simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hc1⟩ := hC
  simp only [okTheta, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨⟨hvok, hv0⟩, hres⟩ := hT
  have hhLoR : (0 : ℝ) < ((hLo B : ℚ) : ℝ) := by exact_mod_cast hhLo
  have hc1R : (0 : ℝ) < ((B.c1 : ℚ) : ℝ) := by exact_mod_cast hc1
  have hh_lo : ((hLo B : ℚ) : ℝ) ≤ (H a + H (a + z * y)) / 2 := by
    rw [hLo_cast]; linarith [P.Ha_lo, P.Hb_lo]
  have hh_hi : (H a + H (a + z * y)) / 2 ≤ ((hHi B : ℚ) : ℝ) := by
    rw [hHi_cast]; linarith [P.Ha_hi, P.Hb_hi]
  have hh0 : 0 < (H a + H (a + z * y)) / 2 := hhLoR.trans_le hh_lo
  have hX0 : (0 : ℝ) < ((Xq B : ℚ) : ℝ) := by
    rw [Xq_cast]; exact div_pos hc1R (by linarith)
  have hX : (a + y - a) / (2 * ((H a + H (a + z * y)) / 2)) ≤ ((Xq B : ℚ) : ℝ) := by
    rw [Xq_cast, show a + y - a = y by ring]
    exact div_le_div₀ hc1R.le P.y1 (by linarith) (by linarith)
  refine ⟨hX, ?_⟩
  have hresR : 1 - 2 * ((w.v : ℚ) : ℝ) ≤ 2 * ((Xq B : ℚ) : ℝ) * ((Hlo w.v : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hres; push_cast at this; linarith
  have hth := theta_ge hX0 hvok hresR
  have hv0R : (0 : ℝ) ≤ ((slopeLo w.v : ℚ) : ℝ) := by exact_mod_cast hv0
  have e1 : (a + y - a) ^ 2 - (a + z * y - a) ^ 2 = y ^ 2 * (1 - z ^ 2) := by ring
  have hz2 : z ^ 2 ≤ ((B.b1 : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ P.hz0.le P.z1 2
  have hb1sq : ((B.b1 : ℚ) : ℝ) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ ((B.b1 : ℚ) : ℝ) := P.pb0.trans (P.z0.trans P.z1)
    nlinarith [P.b1le]
  have T1 : y ^ 2 * (((alphaQ B w : ℚ) : ℝ) * (1 - ((B.b1 : ℚ) : ℝ) ^ 2)) ≤
      e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) * ((a + y - a) ^ 2 - (a + z * y - a) ^ 2) /
        (4 * ((H a + H (a + z * y)) / 2)) := by
    rw [e1, alphaQ_cast]
    have k1 : ((slopeLo w.v : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) ≤
        e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) :=
      div_le_div_of_nonneg_right hth hX0.le
    have k2 : (1 - ((B.b1 : ℚ) : ℝ) ^ 2) * y ^ 2 / (4 * ((hHi B : ℚ) : ℝ)) ≤
        (1 - z ^ 2) * y ^ 2 / (4 * ((H a + H (a + z * y)) / 2)) :=
      div_le_div₀ (mul_nonneg (by linarith) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) (by linarith) (by linarith)
    have k3 : 0 ≤ (1 - ((B.b1 : ℚ) : ℝ) ^ 2) * y ^ 2 / (4 * ((hHi B : ℚ) : ℝ)) :=
      div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
    have k4 : 0 ≤ e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) := div_nonneg (hv0R.trans hth) hX0.le
    have k := mul_le_mul k1 k2 k3 k4
    have eL : y ^ 2 * (((slopeLo w.v : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) / (4 * ((hHi B : ℚ) : ℝ)) *
        (1 - ((B.b1 : ℚ) : ℝ) ^ 2)) = ((slopeLo w.v : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) *
        ((1 - ((B.b1 : ℚ) : ℝ) ^ 2) * y ^ 2 / (4 * ((hHi B : ℚ) : ℝ))) := by ring
    have eR : e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) * (y ^ 2 * (1 - z ^ 2)) /
        (4 * ((H a + H (a + z * y)) / 2)) = e8Theta ((Xq B : ℚ) : ℝ) / ((Xq B : ℚ) : ℝ) *
        ((1 - z ^ 2) * y ^ 2 / (4 * ((H a + H (a + z * y)) / 2))) := by ring
    rw [eL, eR]; exact k
  have T2 : y ^ 2 * (((betaQ B : ℚ) : ℝ) * ((B.b0 : ℚ) : ℝ) ^ 2) ≤
      (a + z * y - a) ^ 2 / ((a + (a + z * y)) * Real.log 2) := by
    rw [betaQ_cast, show a + z * y - a = z * y by ring]
    have hb0y : ((B.b0 : ℚ) : ℝ) * y ≤ z * y := mul_le_mul_of_nonneg_right P.z0 P.hy.le
    have hsq : (((B.b0 : ℚ) : ℝ) * y) ^ 2 ≤ (z * y) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg P.pb0 P.hy.le) hb0y 2
    have hden0 : 0 < (a + (a + z * y)) * Real.log 2 :=
      mul_pos (by linarith [P.ha, P.hzy]) log2_pos
    have hden : (a + (a + z * y)) * Real.log 2 ≤
        (2 * ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) * ((LqHi : ℚ) : ℝ) :=
      mul_le_mul (by linarith [P.a1, P.zy_hi]) LqHi_ge' log2_pos.le
        (by linarith [P.pa0, P.a0, P.a1, P.hzy, P.zy_hi])
    have k := div_le_div₀ (sq_nonneg _) hsq hden0 hden
    have e : y ^ 2 * (1 / ((2 * ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) *
        ((LqHi : ℚ) : ℝ)) * ((B.b0 : ℚ) : ℝ) ^ 2) = (((B.b0 : ℚ) : ℝ) * y) ^ 2 /
        ((2 * ((B.a1 : ℚ) : ℝ) + ((B.b1 : ℚ) : ℝ) * ((B.c1 : ℚ) : ℝ)) * ((LqHi : ℚ) : ℝ)) := by
      ring
    rw [e]; exact k
  nlinarith [T1, T2]

/-- the bound case: `gapLB ≥ y² · PloQ > 0` -/
theorem PtBox.bound {w : RWit} (hb : boundOK B w = true) :
    0 < gapLB (H a) (H (a + z * y)) (a + y) := by
  simp only [boundOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨hH, hC⟩, hT⟩, hQ⟩, hR⟩, h4⟩, hP⟩ := hb
  obtain ⟨hX, h12⟩ := P.T12 hH hC hT
  have h3 := P.T3 hH hR hQ
  have h4' := P.T4 hH hC hR hQ h4
  have hG := P.cfg.gapLB_ge hX h3 h4'
  have hPR : (0 : ℝ) < ((PloQ B w : ℚ) : ℝ) := by exact_mod_cast hP
  rw [PloQ_cast] at hPR
  have hy2 : 0 < y ^ 2 := pow_pos P.hy 2
  have k := mul_pos hy2 hPR
  nlinarith [k, h12, hG]

end pt

theorem PtBox.of_geom {B : B3} {a z y : ℝ} (hg : geomOK B = true) (hm : B.Mem a z y)
    (hz0 : 0 < z) (hz1 : z < 1) (hy : 0 < y) : PtBox B a z y := by
  simp only [geomOK, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, -⟩, h5⟩, h6⟩, -⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hg
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hm
  have hc8 : ((cHi B : ℚ) : ℝ) < 1 / 2 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h8; push_cast at this; linarith
  exact ⟨m1, m2, m3, m4, m5, m6, hz0, hz1, hy, by exact_mod_cast h1, by exact_mod_cast h3,
    by exact_mod_cast h6, hc8, by exact_mod_cast h5, h9, h10, h11, h12⟩

/-- **Soundness of the row-3 box checker.** -/
theorem r3Box_sound {B : B3} {w : RWit} (h : r3BoxOK B w = true) {a z y : ℝ} (hm : B.Mem a z y)
    (hz0 : 0 < z) (hz1 : z < 1) (hy : 0 < y) (hA : y ≤ (H a + H (a + z * y)) / 20) :
    0 ≤ gapLB (H a) (H (a + z * y)) (a + y) := by
  simp only [r3BoxOK, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hg, hv | hb⟩ := h
  · exfalso
    have P := PtBox.of_geom hg hm hz0 hz1 hy
    simp only [vacOK, decide_eq_true_eq] at hv
    have hvR : ((Ha1 B : ℚ) : ℝ) + ((Hb1 B : ℚ) : ℝ) < 20 * ((B.c0 : ℚ) : ℝ) := by
      exact_mod_cast hv
    linarith [P.Ha_hi, P.Hb_hi, P.y0]
  · exact ((PtBox.of_geom hg hm hz0 hz1 hy).bound hb).le

end CKLaneM07.CE.R3

end


