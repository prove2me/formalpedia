-- Prove2me | Definitions.Def_CK_CKLaneE_CertPDVac
-- name    : CK_CKLaneE_CertPDVac
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:44:34.314405+00:00
-- url     : https://prove2.me/theorems/75474cbc-df24-4951-a202-7e6ef741ca71
-- title:
--   Courtade–Kumar proof module `CKLaneE.CertPDVac` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.CertPDVac` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.CertPDVac` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.CertPDVac (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/CertPDVac.lean)

import Definitions.Def_CK_CKLaneE_CertLS

-- ===== source module CKLaneE.CertPDVac =====
section

/-!
# Lane E: parent-dominance and chart-exclusion certificates for population leaves

* `PD.check`: on the whole box `phi(m,E) ≥ psi(m,E)`, contradicting the chart's active-psi premise.
  `eta(E) ≥ (1-2u0) J(u0)` (`E ≤ H u0`, `eta` antitone), `F(q,E) ≤ qHi J(v2)`
  (`v2 ≤ radialContact(qHi,E1)`), `psi = eta(E+1-H m) ≤ (1-2u1) J(u1)` (`H u1 ≤ E+1-H m`).
* `Vac.check`: the box misses the chart (mean, ratio strips, low entropy, information, entropy cap).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.PD

open GeneralCK GeneralCK.Scalar CKLaneE.FP CKLaneE.Chart CKLaneE.LS
open CKLaneE.NLS (H_le_H box_geometry)

def qHi (B : Box3) : ℚ := 1 - 2 * mLo B
def Jl (v : ℚ) : ℚ := lamLo v / LqHi
def Jh (v : ℚ) : ℚ := lamHi v / LqLo

def check (B : Box3) (u0 u1 v2 : ℚ) : Bool :=
  boxOk B && decide (B.E1 ≤ B.E2) && ptOk (mLo B) && ptOk (mHi B) && ptOk u0 && ptOk u1 &&
    ptOk v2 &&
    decide (u0 < 1 / 2 ∧ u1 < 1 / 2 ∧ v2 < 1 / 2 ∧ 0 < qHi B ∧ B.E2 ≤ Hlo u0 ∧
      Hhi u1 ≤ B.E1 + 1 - Hhi (mHi B) ∧ qHi B * Hhi v2 ≤ B.E1 * (1 - 2 * v2) ∧
      0 ≤ lamLo u0 ∧ 0 ≤ lamHi v2 ∧
      (1 - 2 * u1) * Jh u1 ≤ (1 - 2 * u0) * Jl u0 - qHi B * Jh v2)

theorem eta_H_eq {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 2) : eta (H u) = (1 - 2 * u) * J u := by
  rw [eta_eq_profile (H_nonneg hu.le (by linarith)) (H_le_one u), entropyInverse_H_lower hu.le hu']

theorem Jl_le {v : ℚ} (hpt : ptOk v = true) (hlam : 0 ≤ lamLo v) :
    ((Jl v : ℚ) : ℝ) ≤ J (v : ℝ) := by
  obtain ⟨hl, _⟩ := lam_bounds hpt
  obtain ⟨_, hL2⟩ := log_two_mem
  have hL := log_two_pos
  have hlam' : (0 : ℝ) ≤ ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  unfold J
  have e : ((Jl v : ℚ) : ℝ) = ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) := by
    simp only [Jl]; push_cast; ring
  rw [e]
  calc ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((lamLo v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_left hlam' hL hL2
    _ ≤ Real.log ((1 - (v : ℝ)) / v) / Real.log 2 := div_le_div_of_nonneg_right hl hL.le

theorem le_Jh {v : ℚ} (hpt : ptOk v = true) (hv12 : (v : ℝ) ≤ 1 / 2) :
    J (v : ℝ) ≤ ((Jh v : ℚ) : ℝ) := by
  obtain ⟨_, hu⟩ := lam_bounds hpt
  obtain ⟨hL1, _⟩ := log_two_mem
  have hL := log_two_pos
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (ptOk_pos hpt).1
  have hJ0 : 0 ≤ J (v : ℝ) := J_nonneg hv0 hv12
  have hlog0 : 0 ≤ Real.log ((1 - (v : ℝ)) / v) := by
    have := hJ0; unfold J at this
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hL))
  unfold J
  have e : ((Jh v : ℚ) : ℝ) = ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := by
    simp only [Jh]; push_cast; ring
  rw [e]
  calc Real.log ((1 - (v : ℝ)) / v) / Real.log 2 ≤ ((lamHi v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right hu hL.le
    _ ≤ ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left (hlog0.trans hu) LqLo_pos hL1

set_option maxHeartbeats 1000000 in
theorem check_sound (B : Box3) (u0 u1 v2 : ℚ) (hw : check B u0 u1 v2 = true) : Good B := by
  intro k μ hμ hin
  exfalso
  obtain ⟨hr1, hr2, hb1, hb2, hE1, hE2⟩ := hin
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨hbox, _⟩, hmLo⟩, hmHi⟩, hu0⟩, hu1⟩, hv2⟩,
    ⟨qu0, qu1, qv2, qq, qE2, qu1c, qv2c, qlam0, qlam2, qfin⟩⟩ := hw
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have hE0 : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  obtain ⟨R1, _, R2, B1, _, B2, hE1pos⟩ := boxOk_real hbox
  obtain ⟨_, _, gmL, gmH, _, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have hm_def : μ.midpoint = (μ.a + μ.b) / 2 := rfl
  have hm0 : 0 < μ.midpoint := by rw [hm_def]; linarith
  have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
  have hmHhalf : (B.b2 : ℝ) * (1 + B.r2) / 2 ≤ 1 / 2 := by nlinarith
  have hm12 : μ.midpoint ≤ 1 / 2 := by rw [hm_def]; linarith
  -- real forms of the rational side conditions
  have cast_lt_half : ∀ {x : ℚ}, x < 1 / 2 → (x : ℝ) < 1 / 2 := by
    intro x hx
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    push_cast at h; linarith
  have hu0R := cast_lt_half qu0
  have hu1R := cast_lt_half qu1
  have hv2R := cast_lt_half qv2
  have hu0p : (0 : ℝ) < u0 := by exact_mod_cast (ptOk_pos hu0).1
  have hu1p : (0 : ℝ) < u1 := by exact_mod_cast (ptOk_pos hu1).1
  have hv2p : (0 : ℝ) < v2 := by exact_mod_cast (ptOk_pos hv2).1
  have cqHi : ((qHi B : ℚ) : ℝ) = 1 - 2 * ((mLo B : ℚ) : ℝ) := by push_cast [qHi]; ring
  have hqHi : (0 : ℝ) < ((qHi B : ℚ) : ℝ) := by exact_mod_cast qq
  -- (i) eta(E) ≥ (1-2u0) Jl u0
  obtain ⟨Hu0L, _⟩ := H_bounds hu0
  have hEH : μ.meanEntropy ≤ H (u0 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr qE2
    linarith
  have heta1 : eta (H (u0 : ℝ)) ≤ eta μ.meanEntropy :=
    eta_antitoneOn ⟨hE0, (hEH.trans (H_le_one _))⟩ ⟨hE0.trans_le hEH, H_le_one _⟩ hEH
  rw [eta_H_eq hu0p hu0R.le] at heta1
  have hJl := Jl_le hu0 qlam0
  have i1 : (1 - 2 * (u0 : ℝ)) * ((Jl u0 : ℚ) : ℝ) ≤ eta μ.meanEntropy := by
    have := mul_le_mul_of_nonneg_left hJl (by linarith : (0 : ℝ) ≤ 1 - 2 * (u0 : ℝ))
    linarith
  -- (ii) F(|1-2m|, E) ≤ qHi * Jh v2
  have hq_le : |1 - 2 * μ.midpoint| ≤ ((qHi B : ℚ) : ℝ) := by
    rw [abs_of_nonneg (by linarith), cqHi, c_mLo, hm_def]; linarith
  have hJh0 : (0 : ℝ) ≤ ((Jh v2 : ℚ) : ℝ) := by
    have : (0 : ℝ) ≤ ((lamHi v2 : ℚ) : ℝ) := by exact_mod_cast qlam2
    simp only [Jh]; push_cast
    exact div_nonneg this LqLo_pos.le
  obtain ⟨_, Hv2H⟩ := H_bounds hv2
  have hcont : ((qHi B : ℚ) : ℝ) * H (v2 : ℝ) ≤ (B.E1 : ℝ) * (1 - 2 * v2) := by
    have h := (Rat.cast_le (K := ℝ)).mpr qv2c
    push_cast at h
    have := mul_le_mul_of_nonneg_left Hv2H hqHi.le
    linarith
  have hrc : (v2 : ℝ) ≤ radialContact ((qHi B : ℚ) : ℝ) (B.E1 : ℝ) :=
    (le_radialContact_iff hqHi hE1pos hv2p.le hv2R.le).mpr hcont
  have i2 : F |1 - 2 * μ.midpoint| μ.meanEntropy ≤ ((qHi B : ℚ) : ℝ) * ((Jh v2 : ℚ) : ℝ) := by
    set q := |1 - 2 * μ.midpoint| with hqdef
    by_cases hq0 : q = 0
    · rw [hq0]; unfold F; rw [if_pos rfl]; positivity
    · have hqpos : 0 < q := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hq0)
      unfold F; rw [if_neg hq0]
      have h1 : radialContact ((qHi B : ℚ) : ℝ) μ.meanEntropy ≤ radialContact q μ.meanEntropy :=
        radialContact_anti_radius hqpos hq_le hE0
      have h2 : radialContact ((qHi B : ℚ) : ℝ) (B.E1 : ℝ) ≤
          radialContact ((qHi B : ℚ) : ℝ) μ.meanEntropy :=
        radialContact_mono_entropy hqHi hE1pos hE1
      have hJ : J (radialContact q μ.meanEntropy) ≤ J (v2 : ℝ) :=
        J_antitone hv2p (radialContact_lt_half hqpos hE0).le (hrc.trans (h2.trans h1))
      have hJ' := hJ.trans (le_Jh hv2 hv2R.le)
      have hJ0 : 0 ≤ J (radialContact q μ.meanEntropy) :=
        J_nonneg (radialContact_pos hqpos hE0) (radialContact_lt_half hqpos hE0).le
      calc q * J (radialContact q μ.meanEntropy) ≤ ((qHi B : ℚ) : ℝ) * J (radialContact q μ.meanEntropy) :=
            mul_le_mul_of_nonneg_right hq_le hJ0
        _ ≤ ((qHi B : ℚ) : ℝ) * ((Jh v2 : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hJ' hqHi.le
  -- (iii) psi(m,E) ≤ (1-2u1) Jh u1
  obtain ⟨_, Hu1H⟩ := H_bounds hu1
  obtain ⟨_, HmH⟩ := H_bounds hmHi
  rw [c_mHi] at HmH
  have hHm : H μ.midpoint ≤ ((Hhi (mHi B) : ℚ) : ℝ) := by
    rw [hm_def]; exact (H_le_H (by linarith) gmH hmHhalf).trans HmH
  have hEC : μ.meanEntropy ≤ H μ.midpoint := by
    have hcap : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
      unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop at this
    linarith
  have harg : H (u1 : ℝ) ≤ μ.meanEntropy + 1 - H μ.midpoint := by
    have h := (Rat.cast_le (K := ℝ)).mpr qu1c
    push_cast at h
    linarith
  have harg1 : μ.meanEntropy + 1 - H μ.midpoint ≤ 1 := by linarith
  have hHu1pos : 0 < H (u1 : ℝ) := H_pos hu1p (by linarith)
  have heta3 : eta (μ.meanEntropy + 1 - H μ.midpoint) ≤ eta (H (u1 : ℝ)) :=
    eta_antitoneOn ⟨hHu1pos, H_le_one _⟩ ⟨hHu1pos.trans_le harg, harg1⟩ harg
  rw [eta_H_eq hu1p hu1R.le] at heta3
  have hJu1 := le_Jh hu1 hu1R.le
  have i3 : psi μ.midpoint μ.meanEntropy ≤ (1 - 2 * (u1 : ℝ)) * ((Jh u1 : ℚ) : ℝ) := by
    unfold psi
    have := mul_le_mul_of_nonneg_left hJu1 (by linarith : (0 : ℝ) ≤ 1 - 2 * (u1 : ℝ))
    linarith
  -- final comparison
  have hfinR : (1 - 2 * (u1 : ℝ)) * ((Jh u1 : ℚ) : ℝ) ≤
      (1 - 2 * (u0 : ℝ)) * ((Jl u0 : ℚ) : ℝ) - ((qHi B : ℚ) : ℝ) * ((Jh v2 : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr qfin
    push_cast at h
    linarith
  have hphi : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy := by
    unfold phi; linarith
  exact absurd hμ.hactive (not_lt.mpr hphi)

end CKLaneE.PD

namespace CKLaneE.Vac

open GeneralCK CKLaneE.FP CKLaneE.Chart CKLaneE.LS
open CKLaneE.NLS (H_le_H box_geometry)

def check (B : Box3) : Bool :=
  decide (B.E2 ≤ 1 / 1000000) ||
  boxOk B &&
    (decide (B.b2 * (1 + B.r2) ≤ 1 / 16) || decide (B.r2 ≤ 1 / 32768) ||
      decide (B.b2 ≤ 17 / 40 ∧ B.r2 ≤ 1 / 16384) ||
      decide (B.b2 * (1 + B.r2) ≤ 1 / 4 ∧ B.r2 ≤ 1 / 256) ||
      (ptOk (mHi B) && decide (Hhi (mHi B) - B.E1 ≤ 1 / 100)) ||
      (ptOk (aHi B) && ptOk B.b2 && decide (CHi B < B.E1)))

set_option maxHeartbeats 1000000 in
theorem check_sound (B : Box3) (hw : check B = true) : Good B := by
  intro k μ hμ hin
  exfalso
  obtain ⟨hr1, hr2, hb1, hb2, hE1, hE2⟩ := hin
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
  rcases hw with hlow | ⟨hbox, hc⟩
  · have h := (Rat.cast_le (K := ℝ)).mpr hlow
    push_cast at h
    linarith [hμ.hE]
  obtain ⟨R1, _, R2, B1, _, B2, _⟩ := boxOk_real hbox
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  obtain ⟨gaL, gaH, gmL, gmH, _, _, _⟩ := box_geometry R1 R2 B1 hb0 hr1 hr2 hb1 hb2
  have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
  have hr2pos : (0 : ℝ) < B.r2 := lt_of_lt_of_le R1 (le_trans hr1 hr2)
  have hsumle : μ.a + μ.b ≤ (B.b2 : ℝ) * (1 + B.r2) := by linarith
  rcases hc with (((((hc | hc) | hc) | hc) | hc) | hc)
  · have h := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at h
    linarith [hμ.hmean]
  · have h := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at h
    linarith [hμ.hratio]
  · obtain ⟨h1, h2⟩ := hc
    have h1' := (Rat.cast_le (K := ℝ)).mpr h1
    have h2' := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at h1' h2'
    have := hμ.hstrip (by linarith)
    linarith
  · obtain ⟨h1, h2⟩ := hc
    have h1' := (Rat.cast_le (K := ℝ)).mpr h1
    have h2' := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at h1' h2'
    have := hμ.hsmall (by linarith)
    linarith
  · obtain ⟨hpt, hinf⟩ := hc
    obtain ⟨_, HmH⟩ := H_bounds hpt
    rw [c_mHi] at HmH
    have hmHhalf : (B.b2 : ℝ) * (1 + B.r2) / 2 ≤ 1 / 2 := by nlinarith
    have hHm : H ((μ.a + μ.b) / 2) ≤ ((Hhi (mHi B) : ℚ) : ℝ) :=
      (H_le_H (by linarith) gmH hmHhalf).trans HmH
    have h := (Rat.cast_le (K := ℝ)).mpr hinf
    push_cast at h
    have hinfo := hμ.hinfo
    unfold InteriorLaw.information InteriorLaw.midpoint at hinfo
    linarith
  · obtain ⟨⟨hpa, hpb⟩, hcap⟩ := hc
    obtain ⟨_, HaH⟩ := H_bounds hpa
    obtain ⟨_, HbH⟩ := H_bounds hpb
    rw [c_aHi] at HaH
    have haHhalf : (B.r2 : ℝ) * B.b2 ≤ 1 / 2 := by nlinarith
    have hHa : H μ.a ≤ ((Hhi (aHi B) : ℚ) : ℝ) := (H_le_H ha0.le gaH haHhalf).trans HaH
    have hHb : H μ.b ≤ ((Hhi B.b2 : ℚ) : ℝ) := (H_le_H hb0.le hb2 B2).trans HbH
    have hcapR : ((CHi B : ℚ) : ℝ) < B.E1 := by exact_mod_cast hcap
    rw [c_CHi] at hcapR
    have hEle : μ.meanEntropy ≤ (H μ.a + H μ.b) / 2 := by
      unfold InteriorLaw.meanEntropy; linarith [μ.e_le_cap, μ.f_le_cap]
    linarith

end CKLaneE.Vac

#check @CKLaneE.PD.check_sound
#check @CKLaneE.Vac.check_sound
#print axioms CKLaneE.PD.check_sound
#print axioms CKLaneE.Vac.check_sound

end


