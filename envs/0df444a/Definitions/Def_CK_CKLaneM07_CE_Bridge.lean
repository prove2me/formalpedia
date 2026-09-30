-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_Bridge
-- name    : CK_CKLaneM07_CE_Bridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:47:27.108477+00:00
-- url     : https://prove2.me/theorems/742b4764-70ac-4afd-80b2-15928065c2f9
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.Bridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.Bridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.Bridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.Bridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/Bridge.lean)

import Definitions.Def_CK_CKLaneM07_CE_ChainSound
import Definitions.Def_CK_CKLaneN1_CEStat
import Definitions.Def_CK_GeneralCK_PureGapMeanStationarity
import Definitions.Def_CK_GeneralCK_PhysicalSlope

-- ===== source module CKLaneM07.CE.Bridge =====
section

/-!
# Lane M07 / CE-stat: bridge from a physical Case-E stationary point to the chart chain

For `CKLaneN1.CEStat.PointFree e f c` the chart values
`a = ι e`, `b = ι f`, `t_A = rc(c - a, E/2)`, `t_B = rc(1 - a - c, E/2)`, `t_C = rc(1 - 2c, f)`,
`t_D = rc(b - a, E/2)`, `u_E = ι(E/2)` (with `E = e + f`, `rc = radialContact`) satisfy every residual
equation of the chain (`RealPt.Valid`), and the chain's natural-log pure gap is
`canonicalPureGap (ι e) c e f · log 2`.  Stationarity enters only through
`deriv_canonicalPureGap_right` and `deriv_F_radius_slope` (corpus).
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open GeneralCK CKLaneN1.CEStat

/-- the chart values of a physical point -/
noncomputable def realOf (e f c : ℝ) : RealPt where
  A := chartA e f c
  tC := chartTC f c
  tA := radialContact (c - entropyInverse e) ((e + f) / 2)
  tB := radialContact (1 - entropyInverse e - c) ((e + f) / 2)
  a := entropyInverse e
  b := entropyInverse f
  tD := radialContact (entropyInverse f - entropyInverse e) ((e + f) / 2)
  uE := entropyInverse ((e + f) / 2)

/-- elementary facts at a Case-E point -/
structure PtFacts (e f c : ℝ) : Prop where
  he : 0 < e
  hef : e < f
  hf1 : f ≤ 1
  hc2 : c < 1 / 2
  ha0 : 0 < entropyInverse e
  hab : entropyInverse e < entropyInverse f
  hbt : entropyInverse f < chartTC f c
  htc : chartTC f c < c
  hHa : H (entropyInverse e) = e
  hHb : H (entropyInverse f) = f

theorem ptFacts {e f c : ℝ} (hp : PointFree e f c) : PtFacts e f c := by
  obtain ⟨hbt, htc⟩ := chart_order hp
  obtain ⟨he, hef, hf1, hbc, hc2, -⟩ := hp
  have hf0 : 0 < f := he.trans hef
  have he1 : e ≤ 1 := (hef.trans_le hf1).le
  refine ⟨he, hef, hf1, hc2, entropyInverse_pos he he1, ?_, hbt, htc,
    (entropyInverse_spec he.le he1).2.2, (entropyInverse_spec hf0.le hf1).2.2⟩
  exact entropyInverse_strictMonoOn ⟨he.le, he1⟩ ⟨hf0.le, hf1⟩ hef

section facts

variable {e f c : ℝ} (P : PtFacts e f c)
include P

theorem PtFacts.hf0 : 0 < f := P.he.trans P.hef
theorem PtFacts.hE : 0 < e + f := by linarith [P.he, P.hf0]
theorem PtFacts.hh : 0 < (e + f) / 2 := by linarith [P.hE]
theorem PtFacts.hb2 : entropyInverse f < 1 / 2 := by linarith [P.hbt, P.htc, P.hc2]
theorem PtFacts.ha2 : entropyInverse e < 1 / 2 := by linarith [P.hab, P.hb2]
theorem PtFacts.hca : 0 < c - entropyInverse e := by linarith [P.hab, P.hbt, P.htc]
theorem PtFacts.hcen : 0 < 1 - entropyInverse e - c := by linarith [P.ha2, P.hc2]
theorem PtFacts.hcr : 0 < 1 - 2 * c := by linarith [P.hc2]
theorem PtFacts.hba : 0 < entropyInverse f - entropyInverse e := by linarith [P.hab]
theorem PtFacts.he1 : e < 1 := lt_of_lt_of_le P.hef P.hf1
theorem PtFacts.hh1 : (e + f) / 2 < 1 := by linarith [P.hef, P.hf1]

end facts

theorem realOf_B {e f c : ℝ} (P : PtFacts e f c) :
    (realOf e f c).B = (1 - entropyInverse e - c) / (e + f) := by
  unfold RealPt.B realOf
  simp only
  have hc := P.hcen
  have hv := radialContact_lt_half hc P.hh
  rw [LnR_contact hc hv (radialContact_equation hc P.hh)]
  have := P.hE.ne'
  have := log2_pos'.ne'
  field_simp

theorem realOf_A {e f c : ℝ} : (realOf e f c).A = (c - entropyInverse e) / (e + f) := rfl

theorem LnR_tC {e f c : ℝ} (P : PtFacts e f c) :
    LnR (chartTC f c) = 2 * f * Real.log 2 / (1 - 2 * c) := by
  unfold chartTC
  exact LnR_contact P.hcr (radialContact_lt_half P.hcr P.hf0) (radialContact_equation P.hcr P.hf0)

theorem realOf_lam {e f c : ℝ} (P : PtFacts e f c) : (realOf e f c).lam = f / (e + f) := by
  unfold RealPt.lam
  rw [realOf_B P, realOf_A]
  have hT : (realOf e f c).tC = chartTC f c := rfl
  rw [hT, LnR_tC P]
  have hE := P.hE.ne'
  have hL := log2_pos'.ne'
  have hc := P.hcr.ne'
  have hBA : (1 - entropyInverse e - c) / (e + f) - (c - entropyInverse e) / (e + f) =
      (1 - 2 * c) / (e + f) := by
    rw [div_sub_div_same]; congr 1; ring
  rw [hBA]
  field_simp

theorem realOf_E {e f c : ℝ} (P : PtFacts e f c) : (realOf e f c).E = e + f := by
  unfold RealPt.E
  rw [realOf_B P, realOf_A]
  have ha : (realOf e f c).a = entropyInverse e := rfl
  rw [ha]
  have := P.hE.ne'
  have h2 : 1 - 2 * entropyInverse e ≠ 0 := by linarith [P.ha2]
  have e1 : (c - entropyInverse e) / (e + f) + (1 - entropyInverse e - c) / (e + f) =
      (1 - 2 * entropyInverse e) / (e + f) := by field_simp; ring
  rw [e1]
  field_simp

theorem realOf_c {e f c : ℝ} (P : PtFacts e f c) : (realOf e f c).c = c := by
  unfold RealPt.c
  rw [realOf_E P, realOf_B P, realOf_A]
  have := P.hE.ne'
  field_simp
  ring

theorem LnR_a {e f c : ℝ} (P : PtFacts e f c) :
    LnR (entropyInverse e) = 2 * e * Real.log 2 / (1 - 2 * entropyInverse e) := by
  have hz : 0 < 1 - 2 * entropyInverse e := by linarith [P.ha2]
  apply LnR_contact hz P.ha2
  rw [P.hHa]; ring

/-- every residual equation of the chain holds at a physical Case-E point -/
theorem realOf_valid {e f c : ℝ} (hp : PointFree e f c) : (realOf e f c).Valid := by
  have P := ptFacts hp
  have hB := realOf_B P
  have hlam := realOf_lam P
  have hE := realOf_E P
  have hL := log2_pos'
  have hEne := P.hE.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos P.hca P.hE
  · exact ⟨radialContact_pos P.hca P.hh, radialContact_lt_half P.hca P.hh⟩
  · show chartA e f c * LnR (radialContact (c - entropyInverse e) ((e + f) / 2)) - Real.log 2 = 0
    rw [LnR_contact P.hca (radialContact_lt_half P.hca P.hh) (radialContact_equation P.hca P.hh)]
    unfold chartA
    have := P.hca.ne'
    field_simp
    ring
  · exact ⟨radialContact_pos P.hcen P.hh, radialContact_lt_half P.hcen P.hh⟩
  · -- stationarity
    obtain ⟨he, hef, hf1, hbc, hc2, hs⟩ := hp
    have hac : entropyInverse e < c := by linarith [P.hca]
    have hsum : entropyInverse e + c < 1 := by linarith [P.hcen]
    have hd := deriv_canonicalPureGap_right hac hsum hc2 he P.hf0
    rw [hs, deriv_F_radius_slope P.hca P.hh, deriv_F_radius_slope P.hcen P.hh,
      deriv_F_radius_slope P.hcr P.hf0] at hd
    have htA := radialContact_pos P.hca P.hh
    have htA' := radialContact_lt_half P.hca P.hh
    have htB := radialContact_pos P.hcen P.hh
    have htB' := radialContact_lt_half P.hcen P.hh
    have htC := radialContact_pos P.hcr P.hf0
    have htC' := radialContact_lt_half P.hcr P.hf0
    show UpsR (radialContact (1 - entropyInverse e - c) ((e + f) / 2)) -
      (UpsR (radialContact (c - entropyInverse e) ((e + f) / 2)) + UpsR (chartTC f c)) = 0
    unfold chartTC
    rw [UpsR_eq htA htA', UpsR_eq htB htB', UpsR_eq htC htC']
    have : radialSlope (radialContact (c - entropyInverse e) ((e + f) / 2)) -
        radialSlope (radialContact (1 - entropyInverse e - c) ((e + f) / 2)) +
        radialSlope (radialContact (1 - 2 * c) f) = 0 := hd.symm
    linear_combination (-Real.log 2) * this
  · exact ⟨P.ha0, P.ha2⟩
  · rw [hB, realOf_A]
    exact add_pos (div_pos P.hca P.hE) (div_pos P.hcen P.hE)
  · show LnR (entropyInverse e) * ((realOf e f c).A + (realOf e f c).B) -
      2 * (1 - (realOf e f c).lam) * Real.log 2 = 0
    rw [LnR_a P, hB, realOf_A, hlam]
    have h2 : 1 - 2 * entropyInverse e ≠ 0 := by linarith [P.ha2]
    field_simp
    ring
  · exact ⟨P.ha0.trans P.hab, P.hb2⟩
  · show HnR (entropyInverse f) - (realOf e f c).lam * (realOf e f c).E * Real.log 2 = 0
    rw [HnR_eq_H, P.hHb, hlam, hE]
    field_simp
    ring
  · exact P.hba
  · exact ⟨radialContact_pos P.hba P.hh, radialContact_lt_half P.hba P.hh⟩
  · show (entropyInverse f - entropyInverse e) *
      LnR (radialContact (entropyInverse f - entropyInverse e) ((e + f) / 2)) -
      (realOf e f c).E * Real.log 2 = 0
    rw [LnR_contact P.hba (radialContact_lt_half P.hba P.hh) (radialContact_equation P.hba P.hh), hE]
    have := P.hba.ne'
    field_simp
    ring
  · exact ⟨entropyInverse_pos P.hh (le_of_lt P.hh1), entropyInverse_lt_half P.hh.le P.hh1⟩
  · show HnR (entropyInverse ((e + f) / 2)) - 1 / 2 * ((realOf e f c).E * Real.log 2) = 0
    rw [HnR_eq_H, (entropyInverse_spec P.hh.le P.hh1.le).2.2, hE]
    ring

/-- the chain's pure gap is `canonicalPureGap · log 2` -/
theorem realOf_G {e f c : ℝ} (hp : PointFree e f c) :
    (realOf e f c).G = canonicalPureGap (entropyInverse e) c e f * Real.log 2 := by
  have P := ptFacts hp
  have hcR := realOf_c P
  have htA := radialContact_pos P.hca P.hh
  have htA' := radialContact_lt_half P.hca P.hh
  have htB := radialContact_pos P.hcen P.hh
  have htB' := radialContact_lt_half P.hcen P.hh
  have htC := radialContact_pos P.hcr P.hf0
  have htC' := radialContact_lt_half P.hcr P.hf0
  have htD := radialContact_pos P.hba P.hh
  have htD' := radialContact_lt_half P.hba P.hh
  have huE := entropyInverse_pos P.hh (le_of_lt P.hh1)
  have huE' := entropyInverse_lt_half P.hh.le P.hh1
  have ha0 := P.ha0
  have ha2 := P.ha2
  have hb0 : 0 < entropyInverse f := P.ha0.trans P.hab
  have hb2 := P.hb2
  have hF1 : F (c - entropyInverse e) ((e + f) / 2) =
      (c - entropyInverse e) * J (radialContact (c - entropyInverse e) ((e + f) / 2)) := by
    simp only [F, P.hca.ne', if_false]
  have hF2 : F (entropyInverse f - entropyInverse e) ((e + f) / 2) =
      (entropyInverse f - entropyInverse e) *
        J (radialContact (entropyInverse f - entropyInverse e) ((e + f) / 2)) := by
    simp only [F, P.hba.ne', if_false]
  have hF3 : F (1 - entropyInverse e - c) ((e + f) / 2) =
      (1 - entropyInverse e - c) * J (radialContact (1 - entropyInverse e - c) ((e + f) / 2)) := by
    simp only [F, P.hcen.ne', if_false]
  have hF4 : F (1 - 2 * c) f = (1 - 2 * c) * J (radialContact (1 - 2 * c) f) := by
    simp only [F, P.hcr.ne', if_false]
  have hra : radialContact (1 - 2 * entropyInverse e) e = entropyInverse e := by
    apply radialContact_eq_of_equation (by linarith) P.he ha0 ha2
    rw [P.hHa]; ring
  have hF5 : F (1 - 2 * entropyInverse e) e = (1 - 2 * entropyInverse e) * J (entropyInverse e) := by
    have h2 : (1 - 2 * entropyInverse e) ≠ 0 := by linarith
    simp only [F, h2, if_false, hra]
  have heta_e : eta e = (1 - 2 * entropyInverse e) * J (entropyInverse e) := by
    simp only [eta, P.he1.ne, if_false]
  have hf1' : f ≠ 1 := by
    intro hf
    have : entropyInverse f = 1 / 2 := by rw [hf, GeneralCK.Scalar.entropyInverse_one]
    linarith
  have heta_f : eta f = (1 - 2 * entropyInverse f) * J (entropyInverse f) := by
    simp only [eta, hf1', if_false]
  have heta_h : eta ((e + f) / 2) =
      (1 - 2 * entropyInverse ((e + f) / 2)) * J (entropyInverse ((e + f) / 2)) := by
    simp only [eta, P.hh1.ne, if_false]
  have hcorr : entropyCorrection e f =
      (entropyInverse f - entropyInverse e) * (J (entropyInverse e) - J (entropyInverse f)) / 2 -
        F (entropyInverse f - entropyInverse e) ((e + f) / 2) := by
    unfold entropyCorrection atomCorrection interiorCost
    rw [P.hHa, P.hHb, abs_of_neg (by linarith [P.hab] : entropyInverse e - entropyInverse f < 0),
      neg_sub]
  have hcan : canonicalPureGap (entropyInverse e) c e f =
      (c - entropyInverse e) * J (radialContact (c - entropyInverse e) ((e + f) / 2)) +
      ((entropyInverse f - entropyInverse e) * (J (entropyInverse e) - J (entropyInverse f)) / 2 -
        (entropyInverse f - entropyInverse e) *
          J (radialContact (entropyInverse f - entropyInverse e) ((e + f) / 2))) -
      ((1 - 2 * entropyInverse ((e + f) / 2)) * J (entropyInverse ((e + f) / 2)) -
        (1 - entropyInverse e - c) * J (radialContact (1 - entropyInverse e - c) ((e + f) / 2))) +
      (((1 - 2 * entropyInverse e) * J (entropyInverse e) -
          (1 - 2 * entropyInverse e) * J (entropyInverse e)) +
        ((1 - 2 * entropyInverse f) * J (entropyInverse f) -
          (1 - 2 * c) * J (radialContact (1 - 2 * c) f))) / 2 := by
    unfold canonicalPureGap radialPhi
    rw [hF1, hcorr, hF2, heta_h, hF3, heta_e, hF5, heta_f, hF4]
  have hG : (realOf e f c).G =
      -((entropyInverse f - entropyInverse e) *
          JnR (radialContact (entropyInverse f - entropyInverse e) ((e + f) / 2))) +
      1 / 2 * (-(entropyInverse f - entropyInverse e) *
          (JnR (entropyInverse f) - JnR (entropyInverse e))) +
      -((1 - 2 * entropyInverse ((e + f) / 2)) * JnR (entropyInverse ((e + f) / 2))) +
      1 / 2 * ((1 - 2 * entropyInverse f) * JnR (entropyInverse f)) +
      (c - entropyInverse e) * JnR (radialContact (c - entropyInverse e) ((e + f) / 2)) +
      (1 - entropyInverse e - c) * JnR (radialContact (1 - entropyInverse e - c) ((e + f) / 2)) +
      -(1 / 2 * ((1 - 2 * c) * JnR (radialContact (1 - 2 * c) f))) := by
    unfold RealPt.G
    rw [hcR]
    rfl
  rw [hG, hcan, JnR_eq htD (by linarith), JnR_eq hb0 (by linarith), JnR_eq ha0 (by linarith),
    JnR_eq huE (by linarith), JnR_eq htA (by linarith), JnR_eq htB (by linarith),
    JnR_eq htC (by linarith)]
  ring

end CKLaneM07.CE

end


