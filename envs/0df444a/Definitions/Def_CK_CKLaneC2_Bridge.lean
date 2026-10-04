-- Prove2me | Definitions.Def_CK_CKLaneC2_Bridge
-- name    : CK_CKLaneC2_Bridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-03T11:10:18.458298+00:00
-- url     : https://prove2.me/theorems/6d9c0a13-2d88-4636-87f4-6ee37a1748d6
-- title:
--   Courtade–Kumar proof module `CKLaneC2.Bridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.Bridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.Bridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.Bridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/Bridge.lean)

import Definitions.Def_CK_CKLaneC2_Structural
import Definitions.Def_CK_CKLaneC2_Deriv
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaHigherDerivatives

-- ===== source module CKLaneC2.Bridge =====
section
/-
Lane C2 — bridge between `e8Theta` (radius `t`) and the contact coordinate `c`.

Corpus facts used (all printed with `#check` in `Probe01`):
  `E8AnalyticGerm.xParamReal c = log 2 · c / (2 biasE c)`,
  `radialContact_two_mul_xParamReal : radialContact (2 xParamReal c) 1 = (1-c)/2`,
  `e8Theta_xParamReal : e8Theta (xParamReal c) = thetaParamReal c`,
  `deriv_e8Theta_eq_profile : deriv e8Theta x = profile (radialContact (2x) 1) / x`,
  `biasE_probability`, `biasB_probability`, `radialContact_equation`, `radialContact_le_iff_ratio`.
Results: `gfun (xParamReal c) = Gf c`; the point quantities in atom form; and the contact map
`cOf t = 1 - 2·radialContact (2t) 1` with `xParamReal (cOf t) = t`, monotone in `t`, so that
`Gf` antitone on `[c₁,c_T]` gives `gfun` antitone on `[xParamReal c₁, xParamReal c_T]`.
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

theorem xParam_eq {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    E8AnalyticGerm.xParamReal c = Real.log 2 * c / (2 * Ef c) := by
  unfold E8AnalyticGerm.xParamReal
  rw [Ef_eq_biasE (by linarith) h1]

theorem xParam_pos {c : ℝ} (h0 : 0 < c) (h1 : c < 1) : 0 < E8AnalyticGerm.xParamReal c := by
  rw [xParam_eq h0 h1]
  have := Ef_pos h0.le h1
  have := log_two_pos'
  positivity

theorem thetaParam_eq {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    E8AnalyticGerm.thetaParamReal c
      = Af c / Real.log 2 + 2 * c * Ef c / (Real.log 2 * (1 - c ^ 2) * Kf c) := by
  have hL := log_two_pos'
  have hK := Kf_pos h0.le h1
  have hne : (1 : ℝ) - c ^ 2 ≠ 0 := by nlinarith
  unfold E8AnalyticGerm.thetaParamReal
  rw [← Ef_eq_biasE (by linarith) h1, ← Kf_eq_biasB,
    show SmallMean.A c = Af c / 2 by rw [Af_eq_two_A]; ring]
  field_simp

theorem profile_param {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    Certificates.Mixed.profile ((1 - c) / 2)
      = 2 * c * Ef c ^ 2 * (2 * Kf c - c ^ 2) / (Real.log 2 * (1 - c ^ 2) ^ 2 * Kf c ^ 3) := by
  have hv0 : (0 : ℝ) < (1 - c) / 2 := by linarith
  have hv1 : (1 - c) / 2 < (1 : ℝ) := by linarith
  have hsub : 1 - 2 * ((1 - c) / 2) = c := by ring
  have hE : Certificates.Mixed.hn ((1 - c) / 2) = Ef c := by
    rw [← Correction.Natural.biasE_probability hv0 hv1, hsub, Ef_eq_biasE (by linarith) h1]
  have hK : Certificates.Mixed.kap ((1 - c) / 2) = Kf c := by
    rw [← Correction.Natural.biasB_probability hv0 hv1, hsub, Kf_eq_biasB]
  unfold Certificates.Mixed.profile
  rw [hE, hK, hsub]
  ring

theorem deriv_xParam {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    deriv e8Theta (E8AnalyticGerm.xParamReal c)
      = 4 * Ef c ^ 3 * (2 * Kf c - c ^ 2) / (Real.log 2 ^ 2 * (1 - c ^ 2) ^ 2 * Kf c ^ 3) := by
  have hx := xParam_pos h0 h1
  have hL := log_two_pos'
  have hE := Ef_pos h0.le h1
  have hK := Kf_pos h0.le h1
  have hne : (1 : ℝ) - c ^ 2 ≠ 0 := by nlinarith
  rw [deriv_e8Theta_eq_profile hx, E8AnalyticGerm.radialContact_two_mul_xParamReal h0 h1,
    profile_param h0 h1, xParam_eq h0 h1]
  field_simp
  ring

theorem gfun_xParam {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    gfun (E8AnalyticGerm.xParamReal c) = Gf c := by
  have hL := log_two_pos'
  have hE := Ef_pos h0.le h1
  have hK := Kf_pos h0.le h1
  have h2K := two_Kf_sub_pos h0.le h1
  have hne : (1 : ℝ) - c ^ 2 ≠ 0 := by nlinarith
  unfold gfun
  rw [deriv_xParam h0 h1, xParam_eq h0 h1]
  unfold Gf Nf Dnf r0
  field_simp
  ring

theorem tau_identity {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    gfun (E8AnalyticGerm.xParamReal c) * (E8AnalyticGerm.xParamReal c) ^ 2 / r0
      = Nf c / (Ef c ^ 3 * (2 * Kf c - c ^ 2)) := by
  have hL := log_two_pos'
  have hE := Ef_pos h0.le h1
  have hK := Kf_pos h0.le h1
  have h2K := two_Kf_sub_pos h0.le h1
  have hne : (1 : ℝ) - c ^ 2 ≠ 0 := by nlinarith
  unfold gfun
  rw [deriv_xParam h0 h1, xParam_eq h0 h1]
  unfold Nf r0
  field_simp
  ring

theorem theta0_mul_xParam {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    pureGapTheta0 * E8AnalyticGerm.xParamReal c = 4 * c / Ef c := by
  have hL := log_two_pos'
  have hE := Ef_pos h0.le h1
  rw [xParam_eq h0 h1]
  unfold pureGapTheta0
  field_simp
  ring

/-! ### the contact map -/

noncomputable def cOf (t : ℝ) : ℝ := 1 - 2 * radialContact (2 * t) 1

theorem cOf_mem {t : ℝ} (ht : 0 < t) : 0 < cOf t ∧ cOf t < 1 := by
  have hz : (0 : ℝ) < 2 * t := by linarith
  have h1 := radialContact_pos hz one_pos
  have h2 := radialContact_lt_half hz one_pos
  unfold cOf
  constructor <;> linarith

theorem xParam_cOf {t : ℝ} (ht : 0 < t) : E8AnalyticGerm.xParamReal (cOf t) = t := by
  have hz : (0 : ℝ) < 2 * t := by linarith
  set v := radialContact (2 * t) 1 with hv
  have hv0 : 0 < v := radialContact_pos hz one_pos
  have hv1 : v < 1 / 2 := radialContact_lt_half hz one_pos
  have heq : 2 * t * H v = 1 * (1 - 2 * v) := radialContact_equation hz one_pos
  have hH : 0 < H v := H_pos hv0 (by linarith)
  have hL := log_two_pos'
  unfold E8AnalyticGerm.xParamReal cOf
  rw [← hv, Correction.Natural.biasE_probability hv0 (by linarith),
    Certificates.Mixed.hn_eq_H_mul_log]
  field_simp
  linarith

theorem cOf_mono {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t') : cOf t ≤ cOf t' := by
  have ht' : 0 < t' := lt_of_lt_of_le ht htt'
  have h := (radialContact_le_iff_ratio (z₁ := 2 * t') (z₂ := 2 * t) (h₁ := 1) (h₂ := 1)
    (by linarith) (by linarith) one_pos one_pos).mpr
    (by rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith)
  unfold cOf
  linarith

theorem cOf_xParam {c : ℝ} (h0 : 0 < c) (h1 : c < 1) : cOf (E8AnalyticGerm.xParamReal c) = c := by
  unfold cOf
  rw [E8AnalyticGerm.radialContact_two_mul_xParamReal h0 h1]
  ring

theorem gfun_eq_Gf_cOf {t : ℝ} (ht : 0 < t) : gfun t = Gf (cOf t) := by
  obtain ⟨h0, h1⟩ := cOf_mem ht
  conv_lhs => rw [← xParam_cOf ht]
  exact gfun_xParam h0 h1

/-- `Gf` antitone on `[c₁, c_T]` ⟹ `gfun` antitone on `[xParamReal c₁, xParamReal c_T]`. -/
theorem gfun_antitone_of_Gf {c₁ cT : ℝ} (h0 : 0 < c₁) (hT : cT < 1) (h1T : c₁ ≤ cT)
    (hG : AntitoneOn Gf (Icc c₁ cT)) :
    AntitoneOn gfun (Icc (E8AnalyticGerm.xParamReal c₁) (E8AnalyticGerm.xParamReal cT)) := by
  have hx1 := xParam_pos h0 (lt_of_le_of_lt h1T hT)
  intro t ht t' ht' htt'
  have htpos : 0 < t := lt_of_lt_of_le hx1 ht.1
  have ht'pos : 0 < t' := lt_of_lt_of_le hx1 ht'.1
  rw [gfun_eq_Gf_cOf htpos, gfun_eq_Gf_cOf ht'pos]
  have hc1 : c₁ ≤ cOf t := by
    have := cOf_mono hx1 ht.1
    rwa [cOf_xParam h0 (lt_of_le_of_lt h1T hT)] at this
  have hcT : cOf t' ≤ cT := by
    have := cOf_mono ht'pos ht'.2
    rwa [cOf_xParam (lt_of_lt_of_le h0 h1T) hT] at this
  have hmono := cOf_mono htpos htt'
  exact hG ⟨hc1, le_trans hmono hcT⟩ ⟨le_trans hc1 hmono, hcT⟩ hmono

end CKLaneC2

end


