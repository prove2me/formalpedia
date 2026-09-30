-- Prove2me | Definitions.Def_CK_CKLaneP_ThetaPrime
-- name    : CK_CKLaneP_ThetaPrime
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:48:15.866225+00:00
-- url     : https://prove2.me/theorems/9799be5e-3958-44fa-9aba-32bb7c33be5b
-- title:
--   Courtade–Kumar proof module `CKLaneP.ThetaPrime` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.ThetaPrime` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.ThetaPrime` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.ThetaPrime (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/ThetaPrime.lean)

import Definitions.Def_CK_CKLaneP_EvalTheta
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaHigherDerivatives

-- ===== source module CKLaneP.ThetaPrime =====
section
/-
Lane P — certified bounds on `Θ' = deriv e8Theta` over intervals, and mean-value consequences.

`Θ'(x) = Psi(v)`, `v = radialContact (2x) 1`, where
    Psi v = 4·H v·hn v²·(2 kap v − (1−2v)²) / (log 2 · (4v(1−v))² · kap v³)
(`deriv_e8Theta_eq_Psi`, from the corpus `deriv_e8Theta_eq_profile` and the contact equation).
On a contact bracket `va ≤ v ≤ vb ≤ 1/2` each factor is monotone, giving rational bounds
`PsiUB da db`, `PsiLB da db` from contact data at `va`, `vb`.  With contact brackets of an
`x`-interval this bounds `Θ'` there, hence `Θ(y) − Θ(x)` (`theta_sub_le`, `theta_sub_ge`).
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK GeneralCK.Certificates.Mixed Set

/-- `Θ'` at the contact point. -/
noncomputable def Psi (v : ℝ) : ℝ :=
  4 * H v * hn v ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) /
    (Real.log 2 * (4 * v * (1 - v)) ^ 2 * kap v ^ 3)

theorem deriv_e8Theta_eq_Psi {x : ℝ} (hx : 0 < x) :
    deriv e8Theta x = Psi (radialContact (2 * x) 1) := by
  rw [deriv_e8Theta_eq_profile hx]
  set v := radialContact (2 * x) 1 with hv
  have heq : 2 * x * H v = 1 * (1 - 2 * v) := radialContact_equation (by positivity) one_pos
  set G := 2 * hn v ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) /
    (Real.log 2 * (4 * v * (1 - v)) ^ 2 * kap v ^ 3) with hG
  have hp : profile v = (1 - 2 * v) * G := by
    rw [hG]; unfold profile; ring
  have hP : Psi v = 2 * H v * G := by
    rw [hG]; unfold Psi; ring
  rw [hp, hP, ← one_mul (1 - 2 * v), ← heq]
  field_simp

/-! ### Monotonicity of the factors on `(0, 1/2]` -/

theorem H_mono_half {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) : H u ≤ H v :=
  H_strictMonoOn.monotoneOn ⟨hu, huv.trans hv⟩ ⟨hu.trans huv, hv⟩ huv

theorem hn_mono_half {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) : hn u ≤ hn v := by
  rw [hn_eq_H_mul_log, hn_eq_H_mul_log]
  exact mul_le_mul_of_nonneg_right (H_mono_half hu huv hv) log_two_pos.le

theorem quad_mono_half {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 2) :
    u * (1 - u) ≤ v * (1 - v) := by nlinarith

theorem kap_anti_half {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1 / 2) : kap v ≤ kap u := by
  unfold kap
  have h1 : 0 < u * (1 - u) := mul_pos hu (by linarith)
  have h2 := quad_mono_half hu.le huv hv
  have := Real.log_le_log h1 h2
  linarith

theorem kap_pos' {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1 / 2) : 0 < kap v := by
  have := kap_ge_log_two hv (by linarith)
  linarith [log_two_pos]

/-! ### Rational bounds of `Psi` on a bracket -/

namespace VD

/-- Upper bound of `kap v` from data. -/
def kapHi (d : VD) : ℚ := (d.b1 + d.b2) / 2
/-- Lower bound of `kap v` from data. -/
def kapLo (d : VD) : ℚ := (d.a1 + d.a2) / 2

theorem kap_le_kapHi {d : VD} (hd : d.Sound) : kap (d.v : ℝ) ≤ ((d.kapHi : ℚ) : ℝ) := by
  obtain ⟨h0, h1, _, hb1, _, hb2⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  rw [kap_eq_logs hv0 (by linarith)]
  unfold kapHi; push_cast; linarith

theorem kapLo_le_kap {d : VD} (hd : d.Sound) : ((d.kapLo : ℚ) : ℝ) ≤ kap (d.v : ℝ) := by
  obtain ⟨h0, h1, ha1, _, ha2, _⟩ := hd
  have hv0 : (0 : ℝ) < d.v := by exact_mod_cast h0
  have hv1 : (d.v : ℝ) ≤ 1 / 2 := cast_le_half h1
  rw [kap_eq_logs hv0 (by linarith)]
  unfold kapLo; push_cast; linarith

end VD

/-- Rational upper bound of `Psi` on `[da.v, db.v]`. -/
def PsiUB (da db : VD) : ℚ :=
  4 * db.Hhi * db.hnHi ^ 2 * (2 * da.kapHi - (1 - 2 * db.v) ^ 2) /
    (L2loD * (4 * da.v * (1 - da.v)) ^ 2 * db.kapLo ^ 3)

/-- Rational lower bound of `Psi` on `[da.v, db.v]`. -/
def PsiLB (da db : VD) : ℚ :=
  4 * da.Hlo * da.hnLo ^ 2 * max 0 (2 * db.kapLo - (1 - 2 * da.v) ^ 2) /
    (L2hiD * (4 * db.v * (1 - db.v)) ^ 2 * da.kapHi ^ 3)

theorem L2hiD_pos : (0 : ℝ) < (L2hiD : ℝ) := lt_of_lt_of_le VD.L2lo_pos
  (by have h := log2D_bounds; linarith [h.1, h.2])

theorem Psi_le_PsiUB {da db : VD} (hda : da.Sound) (hdb : db.Sound) (hk : 0 < db.kapLo)
    {v : ℝ} (hav : (da.v : ℝ) ≤ v) (hvb : v ≤ (db.v : ℝ)) :
    Psi v ≤ ((PsiUB da db : ℚ) : ℝ) := by
  have ha0 : (0 : ℝ) < da.v := by exact_mod_cast hda.1
  have hb1 : (db.v : ℝ) ≤ 1 / 2 := VD.cast_le_half hdb.2.1
  have hv0 : 0 < v := lt_of_lt_of_le ha0 hav
  have hv1 : v ≤ 1 / 2 := hvb.trans hb1
  have hl2 := log2D_bounds
  have hL := log_two_pos
  -- factor bounds
  have hH0 : 0 ≤ H v := H_nonneg hv0.le (by linarith)
  have hHle : H v ≤ ((db.Hhi : ℚ) : ℝ) := (H_mono_half hv0.le hvb hb1).trans (VD.le_Hhi hdb)
  have hn0 : 0 ≤ hn v := VD.hn_nonneg' hv0 (by linarith)
  have hnle : hn v ≤ ((db.hnHi : ℚ) : ℝ) := (hn_mono_half hv0.le hvb hb1).trans (VD.le_hnHi hdb)
  have hk0 : 0 ≤ 2 * kap v - (1 - 2 * v) ^ 2 := kap_sq_gap_nonneg hv0 (by linarith)
  have hkle : 2 * kap v - (1 - 2 * v) ^ 2 ≤
      2 * ((da.kapHi : ℚ) : ℝ) - (1 - 2 * (db.v : ℝ)) ^ 2 := by
    have h1 := (kap_anti_half ha0 hav hv1).trans (VD.kap_le_kapHi hda)
    have h2 : (1 - 2 * (db.v : ℝ)) ^ 2 ≤ (1 - 2 * v) ^ 2 := by
      have : 0 ≤ 1 - 2 * (db.v : ℝ) := by linarith
      nlinarith
    linarith
  have hq0 : 0 < 4 * (da.v : ℝ) * (1 - da.v) := by nlinarith
  have hqle : 4 * (da.v : ℝ) * (1 - da.v) ≤ 4 * v * (1 - v) := by
    have := quad_mono_half ha0.le hav hv1; nlinarith
  have hkLo : ((db.kapLo : ℚ) : ℝ) ≤ kap v :=
    (VD.kapLo_le_kap hdb).trans (kap_anti_half hv0 hvb hb1)
  have hkLo0 : (0 : ℝ) < ((db.kapLo : ℚ) : ℝ) := by exact_mod_cast hk
  -- numerator and denominator
  have hnum : 4 * H v * hn v ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) ≤
      4 * ((db.Hhi : ℚ) : ℝ) * ((db.hnHi : ℚ) : ℝ) ^ 2 *
        (2 * ((da.kapHi : ℚ) : ℝ) - (1 - 2 * (db.v : ℝ)) ^ 2) := by
    have e1 : hn v ^ 2 ≤ ((db.hnHi : ℚ) : ℝ) ^ 2 := pow_le_pow_left₀ hn0 hnle 2
    have e2 : 4 * H v * hn v ^ 2 ≤ 4 * ((db.Hhi : ℚ) : ℝ) * ((db.hnHi : ℚ) : ℝ) ^ 2 := by
      have := mul_le_mul hHle e1 (by positivity) (hH0.trans hHle)
      nlinarith
    exact mul_le_mul e2 hkle hk0 (by nlinarith [hH0.trans hHle, sq_nonneg ((db.hnHi : ℚ) : ℝ)])
  have hden : (L2loD : ℝ) * (4 * (da.v : ℝ) * (1 - da.v)) ^ 2 * ((db.kapLo : ℚ) : ℝ) ^ 3 ≤
      Real.log 2 * (4 * v * (1 - v)) ^ 2 * kap v ^ 3 := by
    have e1 := pow_le_pow_left₀ hq0.le hqle 2
    have e2 := pow_le_pow_left₀ hkLo0.le hkLo 3
    have e3 := mul_le_mul hl2.1 e1 (by positivity) hL.le
    exact mul_le_mul e3 e2 (by positivity) (by positivity)
  have hdenpos : (0 : ℝ) < (L2loD : ℝ) * (4 * (da.v : ℝ) * (1 - da.v)) ^ 2 *
      ((db.kapLo : ℚ) : ℝ) ^ 3 := by
    have := VD.L2lo_pos; positivity
  unfold Psi PsiUB
  push_cast
  calc 4 * H v * hn v ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) /
        (Real.log 2 * (4 * v * (1 - v)) ^ 2 * kap v ^ 3)
      ≤ 4 * H v * hn v ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) /
        ((L2loD : ℝ) * (4 * (da.v : ℝ) * (1 - da.v)) ^ 2 * ((db.kapLo : ℚ) : ℝ) ^ 3) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hden
    _ ≤ _ := div_le_div_of_nonneg_right hnum hdenpos.le

theorem PsiLB_le_Psi {da db : VD} (hda : da.Sound) (hdb : db.Sound)
    {v : ℝ} (hav : (da.v : ℝ) ≤ v) (hvb : v ≤ (db.v : ℝ)) :
    ((PsiLB da db : ℚ) : ℝ) ≤ Psi v := by
  have ha0 : (0 : ℝ) < da.v := by exact_mod_cast hda.1
  have hb1 : (db.v : ℝ) ≤ 1 / 2 := VD.cast_le_half hdb.2.1
  have hv0 : 0 < v := lt_of_lt_of_le ha0 hav
  have hv1 : v ≤ 1 / 2 := hvb.trans hb1
  have hl2 := log2D_bounds
  have hL := log_two_pos
  have hHlo0 : (0 : ℝ) ≤ ((da.Hlo : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ da.Hlo := by
      unfold VD.Hlo; apply div_nonneg (le_max_left _ _); unfold L2hiD; norm_num
    exact_mod_cast this
  have hnlo0 : (0 : ℝ) ≤ ((da.hnLo : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ da.hnLo := le_max_left _ _
    exact_mod_cast this
  have hHle : ((da.Hlo : ℚ) : ℝ) ≤ H v := (VD.Hlo_le hda).trans (H_mono_half ha0.le hav hv1)
  have hnle : ((da.hnLo : ℚ) : ℝ) ≤ hn v := (VD.hnLo_le hda).trans (hn_mono_half ha0.le hav hv1)
  have hk0 : 0 ≤ 2 * kap v - (1 - 2 * v) ^ 2 := kap_sq_gap_nonneg hv0 (by linarith)
  have hkge : max 0 (2 * ((db.kapLo : ℚ) : ℝ) - (1 - 2 * (da.v : ℝ)) ^ 2) ≤
      2 * kap v - (1 - 2 * v) ^ 2 := by
    apply max_le hk0
    have h1 := (VD.kapLo_le_kap hdb).trans (kap_anti_half hv0 hvb hb1)
    have h2 : (1 - 2 * v) ^ 2 ≤ (1 - 2 * (da.v : ℝ)) ^ 2 := by
      have : 0 ≤ 1 - 2 * v := by linarith
      nlinarith
    linarith
  have hkv0 : 0 < kap v := kap_pos' hv0 hv1
  have hkhi : kap v ≤ ((da.kapHi : ℚ) : ℝ) := (kap_anti_half ha0 hav hv1).trans (VD.kap_le_kapHi hda)
  have hqv : 0 < 4 * v * (1 - v) := by nlinarith
  have hqle : 4 * v * (1 - v) ≤ 4 * (db.v : ℝ) * (1 - db.v) := by
    have := quad_mono_half hv0.le hvb hb1; nlinarith
  have hnum : 4 * ((da.Hlo : ℚ) : ℝ) * ((da.hnLo : ℚ) : ℝ) ^ 2 *
      max 0 (2 * ((db.kapLo : ℚ) : ℝ) - (1 - 2 * (da.v : ℝ)) ^ 2) ≤
      4 * H v * hn v ^ 2 * (2 * kap v - (1 - 2 * v) ^ 2) := by
    have e1 : ((da.hnLo : ℚ) : ℝ) ^ 2 ≤ hn v ^ 2 := pow_le_pow_left₀ hnlo0 hnle 2
    have e2 : 4 * ((da.Hlo : ℚ) : ℝ) * ((da.hnLo : ℚ) : ℝ) ^ 2 ≤ 4 * H v * hn v ^ 2 := by
      have := mul_le_mul hHle e1 (by positivity) (hHlo0.trans hHle)
      nlinarith
    have hHv0 : 0 ≤ H v := hHlo0.trans hHle
    exact mul_le_mul e2 hkge (le_max_left _ _) (by positivity)
  have hdenpos : 0 < Real.log 2 * (4 * v * (1 - v)) ^ 2 * kap v ^ 3 := by positivity
  have hden : Real.log 2 * (4 * v * (1 - v)) ^ 2 * kap v ^ 3 ≤
      (L2hiD : ℝ) * (4 * (db.v : ℝ) * (1 - db.v)) ^ 2 * ((da.kapHi : ℚ) : ℝ) ^ 3 := by
    have e1 := pow_le_pow_left₀ hqv.le hqle 2
    have e2 := pow_le_pow_left₀ hkv0.le hkhi 3
    have e3 := mul_le_mul hl2.2 e1 (by positivity) (le_of_lt L2hiD_pos)
    have hL2p := L2hiD_pos
    exact mul_le_mul e3 e2 (pow_nonneg hkv0.le 3) (by positivity)
  unfold Psi PsiLB
  push_cast
  calc 4 * ((da.Hlo : ℚ) : ℝ) * ((da.hnLo : ℚ) : ℝ) ^ 2 *
        max 0 (2 * ((db.kapLo : ℚ) : ℝ) - (1 - 2 * (da.v : ℝ)) ^ 2) /
        ((L2hiD : ℝ) * (4 * (db.v : ℝ) * (1 - db.v)) ^ 2 * ((da.kapHi : ℚ) : ℝ) ^ 3)
      ≤ 4 * ((da.Hlo : ℚ) : ℝ) * ((da.hnLo : ℚ) : ℝ) ^ 2 *
        max 0 (2 * ((db.kapLo : ℚ) : ℝ) - (1 - 2 * (da.v : ℝ)) ^ 2) /
        (Real.log 2 * (4 * v * (1 - v)) ^ 2 * kap v ^ 3) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hden
    _ ≤ _ := div_le_div_of_nonneg_right hnum hdenpos.le

/-! ### Contact brackets for an `x`-interval, and mean-value bounds for Θ -/

open ZeroCapLeftStationaryThetaBracket in
/-- Contacts of all `x ∈ [x1, x2]` lie in `[da.v, db.v]` given the bracket inequalities. -/
theorem contact_mem_of_brackets {da db : VD} (hda : da.Sound) (hdb : db.Sound)
    {x1 x2 : ℚ} (hx1 : 0 < x1)
    (hA : 2 * x2 * da.Hhi ≤ 1 - 2 * da.v) (hB : 1 - 2 * db.v ≤ 2 * x1 * db.Hlo)
    {x : ℝ} (hxl : (x1 : ℝ) ≤ x) (hxu : x ≤ (x2 : ℝ)) :
    (da.v : ℝ) ≤ radialContact (2 * x) 1 ∧ radialContact (2 * x) 1 ≤ (db.v : ℝ) := by
  have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have hx : 0 < x := lt_of_lt_of_le hx1R hxl
  have ha0 : (0 : ℝ) < da.v := by exact_mod_cast hda.1
  have ha1 : (da.v : ℝ) ≤ 1 / 2 := VD.cast_le_half hda.2.1
  have hb0 : (0 : ℝ) < db.v := by exact_mod_cast hdb.1
  have hb1 : (db.v : ℝ) ≤ 1 / 2 := VD.cast_le_half hdb.2.1
  constructor
  · have hHhi := VD.le_Hhi hda
    have hH0 : 0 ≤ H (da.v : ℝ) := H_nonneg ha0.le (by linarith)
    have hAR : 2 * (x2 : ℝ) * ((da.Hhi : ℚ) : ℝ) ≤ 1 - 2 * (da.v : ℝ) := by exact_mod_cast hA
    have hres : 2 * x * ((da.Hhi : ℚ) : ℝ) ≤ 1 - 2 * (da.v : ℝ) := by
      have := mul_le_mul_of_nonneg_right hxu (hH0.trans hHhi)
      linarith
    exact contact_lower_of_entropy_upper hx ha0.le ha1 hHhi hres
  · have hHlo := VD.Hlo_le hdb
    have hHlo0 : (0 : ℝ) ≤ ((db.Hlo : ℚ) : ℝ) := by
      have : (0 : ℚ) ≤ db.Hlo := by
        unfold VD.Hlo; apply div_nonneg (le_max_left _ _); unfold L2hiD; norm_num
      exact_mod_cast this
    have hBR : 1 - 2 * (db.v : ℝ) ≤ 2 * (x1 : ℝ) * ((db.Hlo : ℚ) : ℝ) := by exact_mod_cast hB
    have hres : 1 - 2 * (db.v : ℝ) ≤ 2 * x * ((db.Hlo : ℚ) : ℝ) := by
      have := mul_le_mul_of_nonneg_right hxl hHlo0
      linarith
    exact contact_upper_of_entropy_lower hx hb0.le hb1 hHlo hres

/-- Mean-value upper bound for Θ on a bracketed interval. -/
theorem theta_sub_le {da db : VD} (hda : da.Sound) (hdb : db.Sound) (hk : 0 < db.kapLo)
    {x1 x2 : ℚ} (hx1 : 0 < x1)
    (hA : 2 * x2 * da.Hhi ≤ 1 - 2 * da.v) (hB : 1 - 2 * db.v ≤ 2 * x1 * db.Hlo)
    {x y : ℝ} (hxl : (x1 : ℝ) ≤ x) (hxy : x ≤ y) (hyu : y ≤ (x2 : ℝ)) :
    e8Theta y - e8Theta x ≤ ((PsiUB da db : ℚ) : ℝ) * (y - x) := by
  set M : ℝ := ((PsiUB da db : ℚ) : ℝ)
  have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have hpos : ∀ t ∈ Icc x y, 0 < t := fun t ht => lt_of_lt_of_le hx1R (hxl.trans ht.1)
  have hderiv : ∀ t ∈ Icc x y, deriv e8Theta t ≤ M := by
    intro t ht
    have ht0 := hpos t ht
    rw [deriv_e8Theta_eq_Psi ht0]
    obtain ⟨h1, h2⟩ := contact_mem_of_brackets hda hdb hx1 hA hB (hxl.trans ht.1)
      (ht.2.trans hyu)
    exact Psi_le_PsiUB hda hdb hk h1 h2
  have hcont : ContinuousOn (fun t => M * t - e8Theta t) (Icc x y) := by
    apply ContinuousOn.sub (continuousOn_const.mul continuousOn_id)
    exact continuousOn_e8Theta_pos.mono (fun t ht => hpos t ht)
  have hmono : MonotoneOn (fun t => M * t - e8Theta t) (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont
    · intro t ht
      have ht0 := hpos t (interior_subset ht)
      exact ((differentiableAt_id.const_mul M).sub
        (hasDerivAt_e8Theta ht0).differentiableAt).differentiableWithinAt
    · intro t ht
      have ht0 := hpos t (interior_subset ht)
      have hd : HasDerivAt (fun t => M * t - e8Theta t) (M * 1 - deriv e8Theta t) t :=
        ((hasDerivAt_id t).const_mul M).sub (hasDerivAt_e8Theta ht0).differentiableAt.hasDerivAt
      rw [hd.deriv]
      linarith [hderiv t (interior_subset ht)]
  have := hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  simp only at this
  linarith

/-- Mean-value lower bound for Θ on a bracketed interval. -/
theorem theta_sub_ge {da db : VD} (hda : da.Sound) (hdb : db.Sound)
    {x1 x2 : ℚ} (hx1 : 0 < x1)
    (hA : 2 * x2 * da.Hhi ≤ 1 - 2 * da.v) (hB : 1 - 2 * db.v ≤ 2 * x1 * db.Hlo)
    {x y : ℝ} (hxl : (x1 : ℝ) ≤ x) (hxy : x ≤ y) (hyu : y ≤ (x2 : ℝ)) :
    ((PsiLB da db : ℚ) : ℝ) * (y - x) ≤ e8Theta y - e8Theta x := by
  set m : ℝ := ((PsiLB da db : ℚ) : ℝ)
  have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have hpos : ∀ t ∈ Icc x y, 0 < t := fun t ht => lt_of_lt_of_le hx1R (hxl.trans ht.1)
  have hderiv : ∀ t ∈ Icc x y, m ≤ deriv e8Theta t := by
    intro t ht
    have ht0 := hpos t ht
    rw [deriv_e8Theta_eq_Psi ht0]
    obtain ⟨h1, h2⟩ := contact_mem_of_brackets hda hdb hx1 hA hB (hxl.trans ht.1)
      (ht.2.trans hyu)
    exact PsiLB_le_Psi hda hdb h1 h2
  have hcont : ContinuousOn (fun t => e8Theta t - m * t) (Icc x y) := by
    apply ContinuousOn.sub _ (continuousOn_const.mul continuousOn_id)
    exact continuousOn_e8Theta_pos.mono (fun t ht => hpos t ht)
  have hmono : MonotoneOn (fun t => e8Theta t - m * t) (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont
    · intro t ht
      have ht0 := hpos t (interior_subset ht)
      exact ((hasDerivAt_e8Theta ht0).differentiableAt.sub
        (differentiableAt_id.const_mul m)).differentiableWithinAt
    · intro t ht
      have ht0 := hpos t (interior_subset ht)
      have hd : HasDerivAt (fun t => e8Theta t - m * t) (deriv e8Theta t - m * 1) t :=
        (hasDerivAt_e8Theta ht0).differentiableAt.hasDerivAt.sub ((hasDerivAt_id t).const_mul m)
      rw [hd.deriv]
      linarith [hderiv t (interior_subset ht)]
  have := hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  simp only at this
  linarith

/-- `Θ(x)/x` lower bound from a point to its right: `Θ(x) ≥ x · Θ(X)/X` for `0 < x ≤ X`. -/
theorem theta_ge_ratio {x X : ℝ} (hx : 0 < x) (hxX : x ≤ X) :
    x * (e8Theta X / X) ≤ e8Theta x := by
  have hX : 0 < X := lt_of_lt_of_le hx hxX
  have h := antitoneOn_e8Theta_div (show x ∈ Ioi (0 : ℝ) from hx) (show X ∈ Ioi (0 : ℝ) from hX) hxX
  simp only at h
  calc x * (e8Theta X / X) ≤ x * (e8Theta x / x) := mul_le_mul_of_nonneg_left h hx.le
    _ = e8Theta x := by field_simp

end CKLaneP

end


