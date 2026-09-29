-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCheckT
-- name    : CK_CKLaneC2R_EndpointCheckT
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:02:14.893985+00:00
-- url     : https://prove2.me/theorems/701e94d7-d765-41ee-88f1-ee93e0776a6d
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCheckT` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCheckT` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCheckT` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCheckT (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCheckT.lean)

import Definitions.Def_CK_CKLaneC2R_EndpointCheck
import Definitions.Def_CK_CKLaneC2R_CompactCheckT

-- ===== source module CKLaneC2R.EndpointCheckT =====
section

/-!
# Lane C2: table-deduplicated endpoint checker

Same semantics as `CKLaneC2R.Endpoint.ecellOk`, but every executable logarithm datum is checked
once per cell (`allCheck table`), and witnesses look their datums up in the table.
-/

namespace CKLaneC2R.Endpoint

open GeneralCK GeneralCK.Certificates
open ReflectionFastTranscendental CorrectionIntegerLogTableKernel
open CKLaneC2R.T (memD logCheckT entCheckT bCheckT)

structure ECellT extends ECell where
  table : List Datum

def pointOkT (T : List Datum) (x : ℤ) (w : EntropyWitness) : Bool :=
  entCheckT T (DyadicContact.point x) w

def contactOkT (T : List Datum) (Y c : DI) (wl wh : EntropyWitness) : Bool :=
  decide (0 ≤ Y.lo) && decide (0 ≤ c.lo) && decide (c.lo ≤ c.hi) && decide (c.hi ≤ S40) &&
    pointOkT T c.lo wl && pointOkT T c.hi wh &&
    decide (c.lo * S40 ≤ Y.lo * wl.output.lo) && decide (Y.hi * wh.output.hi ≤ c.hi * S40)

def entET (c : ECellT) : Bool :=
  decide (0 ≤ c.A.lo) && decide (c.A.hi ≤ S40) && decide (0 ≤ c.toECell.B.lo) &&
  decide (c.toECell.B.hi ≤ S40) &&
  pointOkT c.table c.A.lo c.eAl && pointOkT c.table c.A.hi c.eAh &&
  pointOkT c.table c.toECell.B.lo c.eBl && pointOkT c.table c.toECell.B.hi c.eBh &&
  decide (0 < c.toECell.E.lo)

def conET (c : ECellT) : Bool :=
  contactOkT c.table c.toECell.RM c.cm c.ecmL c.ecmH &&
  contactOkT c.table c.toECell.RP c.cp c.ecpL c.ecpH &&
  bCheckT c.table c.cm c.bcm && bCheckT c.table c.cp c.bcp &&
  logCheckT c.table (one.add c.A) c.lp c.lpw && logCheckT c.table (one.sub c.A) c.lm c.lmw

/-- The table-deduplicated endpoint cell checker. -/
def ecellOkT (c : ECellT) : Bool :=
  boxE c.toECell && allCheck c.table && entET c && conET c && finE c.toECell

theorem point_entropyT {T : List Datum} (hT : allCheck T = true) {x : ℤ} {w : EntropyWitness}
    (h : pointOkT T x w = true) :
    w.output.Contains (Reflection.biasE ((x : ℝ) / ((S40 : ℤ) : ℝ))) :=
  CKLaneC2R.T.entCheckT_sound hT h (DyadicContact.point_contains 40 x)

theorem emono_containsT {T : List Datum} (hT : allCheck T = true) {d : DI} {wl wh : EntropyWitness}
    (hl : pointOkT T d.lo wl = true) (hh : pointOkT T d.hi wh = true)
    (h0 : 0 ≤ d.lo) (h1 : d.hi ≤ S40) {x : ℝ} (hx : d.Contains x) :
    (emono wl wh).Contains (Reflection.biasE x) := by
  have hs := scale_pos'
  have el := point_entropyT hT hl
  have eh := point_entropyT hT hh
  have hxl : (d.lo : ℝ) / ((S40 : ℤ) : ℝ) ≤ x := by
    rw [div_le_iff₀ hs]; linarith [hx.1]
  have hxh : x ≤ (d.hi : ℝ) / ((S40 : ℤ) : ℝ) := by
    rw [le_div_iff₀ hs]; linarith [hx.2]
  have hlo0 : (0 : ℝ) ≤ (d.lo : ℝ) / ((S40 : ℤ) : ℝ) := div_nonneg (by exact_mod_cast h0) hs.le
  have hhi1 : (d.hi : ℝ) / ((S40 : ℤ) : ℝ) ≤ 1 := (div_le_one hs).mpr (by exact_mod_cast h1)
  have hx0 : 0 ≤ x := le_trans hlo0 hxl
  have hx1 : x ≤ 1 := le_trans hxh hhi1
  have m1 : Reflection.biasE ((d.hi : ℝ) / ((S40 : ℤ) : ℝ)) ≤ Reflection.biasE x :=
    Reflection.biasE_antitone ⟨hx0, hx1⟩ ⟨le_trans hx0 hxh, hhi1⟩ hxh
  have m2 : Reflection.biasE x ≤ Reflection.biasE ((d.lo : ℝ) / ((S40 : ℤ) : ℝ)) :=
    Reflection.biasE_antitone ⟨hlo0, le_trans hxl hx1⟩ ⟨hx0, hx1⟩ hxl
  have k1 := mul_le_mul_of_nonneg_left m1 hs.le
  have k2 := mul_le_mul_of_nonneg_left m2 hs.le
  constructor
  · show ((wh.output.lo : ℤ) : ℝ) ≤ ((S40 : ℤ) : ℝ) * Reflection.biasE x
    linarith [eh.1]
  · show ((S40 : ℤ) : ℝ) * Reflection.biasE x ≤ ((wl.output.hi : ℤ) : ℝ)
    linarith [el.2]

theorem contact_soundT {T : List Datum} (hT : allCheck T = true) {Y cI : DI} {wl wh : EntropyWitness} (hok : contactOkT T Y cI wl wh = true)
    {y : ℝ} (hy : Y.Contains y) : cI.Contains (Reflection.regularContact y) := by
  simp only [contactOkT, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hY0, hc0⟩, hord⟩, hc1⟩, hpl⟩, hph⟩, hlo⟩, hhi⟩ := hok
  have hs := scale_pos'
  have el := point_entropyT hT hpl
  have eh := point_entropyT hT hph
  have hlo' : (cI.lo : ℝ) * ((S40 : ℤ) : ℝ) ≤ (Y.lo : ℝ) * (wl.output.lo : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (Y.hi : ℝ) * (wh.output.hi : ℝ) ≤ (cI.hi : ℝ) * ((S40 : ℤ) : ℝ) := by
    exact_mod_cast hhi
  have hY0' : (0 : ℝ) ≤ Y.lo := by exact_mod_cast hY0
  have hYh0 : (0 : ℝ) ≤ Y.hi := by
    have h1 := hy.1
    have h2 := hy.2
    linarith
  apply DyadicInterval.contains_toReal_iff.mp
  apply RegularContactBounds.contact_contains (Y := Y.toReal) (DyadicInterval.contains_toReal_iff.mpr hy)
  · show (0 : ℝ) ≤ (Y.lo : ℝ) / ((S40 : ℤ) : ℝ)
    exact div_nonneg hY0' hs.le
  · show (0 : ℝ) ≤ (cI.lo : ℝ) / ((S40 : ℤ) : ℝ)
    exact div_nonneg (by exact_mod_cast hc0) hs.le
  · show (cI.hi : ℝ) / ((S40 : ℤ) : ℝ) ≤ 1
    exact (div_le_one hs).mpr (by exact_mod_cast hc1)
  · show (cI.lo : ℝ) / ((S40 : ℤ) : ℝ) ≤ (cI.hi : ℝ) / ((S40 : ℤ) : ℝ)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hord) hs.le
  · show (cI.lo : ℝ) / ((S40 : ℤ) : ℝ) ≤
      (Y.lo : ℝ) / ((S40 : ℤ) : ℝ) * Reflection.biasE ((cI.lo : ℝ) / ((S40 : ℤ) : ℝ))
    have k := mul_le_mul_of_nonneg_left el.1 hY0'
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
    have k2 : (cI.lo : ℝ) * ((S40 : ℤ) : ℝ) ≤
        ((Y.lo : ℝ) * Reflection.biasE ((cI.lo : ℝ) / ((S40 : ℤ) : ℝ))) * ((S40 : ℤ) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right k2 hs
  · show (Y.hi : ℝ) / ((S40 : ℤ) : ℝ) * Reflection.biasE ((cI.hi : ℝ) / ((S40 : ℤ) : ℝ)) ≤
      (cI.hi : ℝ) / ((S40 : ℤ) : ℝ)
    have k := mul_le_mul_of_nonneg_left eh.2 hYh0
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
    have k2 : ((Y.hi : ℝ) * Reflection.biasE ((cI.hi : ℝ) / ((S40 : ℤ) : ℝ))) * ((S40 : ℤ) : ℝ) ≤
        (cI.hi : ℝ) * ((S40 : ℤ) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right k2 hs

theorem ecellOkT_sound (c : ECellT) (h : ecellOkT c = true) {a z : ℝ}
    (ha1 : (c.al : ℝ) ≤ a) (ha2 : a ≤ (c.au : ℝ)) (hz1 : (c.zl : ℝ) ≤ z) (hz2 : z ≤ (c.zu : ℝ))
    (hz : z < 1) : 0 < Reflection.curvature a (a * z) := by
  simp only [ecellOkT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hbox, hT⟩, hent⟩, hcon⟩, hfin⟩ := h
  simp only [boxE, Bool.and_eq_true, decide_eq_true_eq] at hbox
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hal, halu⟩, hau⟩, hzl⟩, hzlu⟩, hzu⟩, hA1⟩, hA2⟩, hZ1⟩, hZ2⟩ := hbox
  simp only [entET, Bool.and_eq_true, decide_eq_true_eq] at hent
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hA0, hAS⟩, hB0⟩, hBS⟩, hpAl⟩, hpAh⟩, hpBl⟩, hpBh⟩, hEpos⟩ := hent
  simp only [conET, Bool.and_eq_true] at hcon
  obtain ⟨⟨⟨⟨⟨hcm, hcp⟩, hbm⟩, hbp⟩, hlpw⟩, hlmw⟩ := hcon
  simp only [finE, Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨⟨⟨homa, hsm⟩, hsp⟩, hNpos⟩ := hfin
  -- the point
  have hal' : (0 : ℝ) < c.al := by exact_mod_cast hal
  have hau' : (c.au : ℝ) < 1 := by exact_mod_cast hau
  have hzl' : (0 : ℝ) < c.zl := by exact_mod_cast hzl
  have ha0 : 0 < a := lt_of_lt_of_le hal' ha1
  have ha1' : a < 1 := lt_of_le_of_lt ha2 hau'
  have hz0 : 0 < z := lt_of_lt_of_le hzl' hz1
  have hA : c.A.Contains a := contains_of_memQ hA1 hA2 ha1 ha2
  have hZ : c.Z.Contains z := contains_of_memQ hZ1 hZ2 hz1 hz2
  have hB : c.B.Contains (a * z) := DyadicInterval.mul_sound hA hZ
  -- entropies and mean entropy
  have hEa : c.EA.Contains (Reflection.biasE a) := emono_containsT hT hpAl hpAh hA0 hAS hA
  have hEb : c.EB.Contains (Reflection.biasE (a * z)) := emono_containsT hT hpBl hpBh hB0 hBS hB
  set e : ℝ := (Reflection.biasE a + Reflection.biasE (a * z)) / 2 with he_def
  have hE : c.E.Contains e := by
    have h0 := DyadicInterval.mul_sound (DyadicInterval.add_sound hEa hEb)
      (DyadicEntropy.half_contains 40)
    rw [he_def, div_eq_mul_inv]
    exact h0
  have he0 : 0 < e := pos_of_contains hEpos hE
  have hEi : c.E.recip.Contains e⁻¹ := DyadicInterval.recip_sound hEpos hE
  -- contact arguments
  have hRM : c.RM.Contains (a * (1 - z) / 2 / e) := by
    have h0 := DyadicInterval.mul_sound (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound hA (DyadicInterval.sub_sound one_contains hZ))
      (DyadicEntropy.half_contains 40)) hEi
    simp only [div_eq_mul_inv]
    exact h0
  have hRP : c.RP.Contains (a * (1 + z) / 2 / e) := by
    have h0 := DyadicInterval.mul_sound (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound hA (DyadicInterval.add_sound one_contains hZ))
      (DyadicEntropy.half_contains 40)) hEi
    simp only [div_eq_mul_inv]
    exact h0
  set cmv : ℝ := Reflection.regularContact (a * (1 - z) / 2 / e) with hcmv
  set cpv : ℝ := Reflection.regularContact (a * (1 + z) / 2 / e) with hcpv
  have hCm : c.cm.Contains cmv := contact_soundT hT hcm hRM
  have hCp : c.cp.Contains cpv := contact_soundT hT hcp hRP
  -- contact-side enclosures
  have hcmok := hcm
  have hcpok := hcp
  simp only [contactOkT, Bool.and_eq_true, decide_eq_true_eq] at hcmok hcpok
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hcm0⟩, _⟩, hcm1⟩, hcmL⟩, hcmH⟩, _⟩, _⟩ := hcmok
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hcp0⟩, _⟩, hcp1⟩, hcpL⟩, hcpH⟩, _⟩, _⟩ := hcpok
  have hEcm : (emono c.ecmL c.ecmH).Contains (Reflection.biasE cmv) :=
    emono_containsT hT hcmL hcmH hcm0 hcm1 hCm
  have hEcp : (emono c.ecpL c.ecpH).Contains (Reflection.biasE cpv) :=
    emono_containsT hT hcpL hcpH hcp0 hcp1 hCp
  have hBcm : c.bcm.output.Contains (Reflection.biasB cmv) := CKLaneC2R.T.bCheckT_sound hT hbm hCm
  have hBcp : c.bcp.output.Contains (Reflection.biasB cpv) := CKLaneC2R.T.bCheckT_sound hT hbp hCp
  -- artanh
  have hlp : c.lp.Contains (Real.log (1 + a)) :=
    CKLaneC2R.T.logCheckT_sound hT hlpw (1 + a) (DyadicInterval.add_sound one_contains hA)
  have hlm : c.lm.Contains (Real.log (1 - a)) :=
    CKLaneC2R.T.logCheckT_sound hT hlmw (1 - a) (DyadicInterval.sub_sound one_contains hA)
  have hL : c.L.Contains (Real.log ((1 + a) / (1 - a)) / 2) := by
    rw [Real.log_div (by linarith) (by linarith), div_eq_mul_inv]
    exact DyadicInterval.mul_sound (DyadicInterval.sub_sound hlp hlm)
      (DyadicEntropy.half_contains 40)
  -- secants and base
  have hSM : c.SM.Contains (Reflection.biasS cmv a e) :=
    secI_contains hCm hEcm hBcm hA hL hE hsm
  have hSP : c.SP.Contains (Reflection.biasS cpv a e) :=
    secI_contains hCp hEcp hBcp hA hL hE hsp
  have hOma : (one.sub (c.A.mul c.A)).Contains (1 - a * a) :=
    DyadicInterval.sub_sound one_contains (DyadicInterval.mul_sound hA hA)
  have hbase : c.base.Contains (2 * a * (a * z) * ((1 - a * a) * (1 - a * a))⁻¹) :=
    DyadicInterval.mul_sound (DyadicInterval.mul_sound (DyadicInterval.mul_sound two_contains hA) hB)
      (DyadicInterval.recip_sound homa (DyadicInterval.mul_sound hOma hOma))
  have hN : c.N.Contains (2 * a * (a * z) * ((1 - a * a) * (1 - a * a))⁻¹ +
      Reflection.biasS cmv a e - Reflection.biasS cpv a e) :=
    DyadicInterval.sub_sound (DyadicInterval.add_sound hbase hSM) hSP
  have hnum := pos_of_contains hNpos hN
  -- the regular normalized value
  have hval : 0 < RegularReflectionExpression.normalizedValue a z := by
    have hsq : (1 - a ^ 2) ^ 2 = (1 - a * a) * (1 - a * a) := by ring
    have hnum' : 0 < 2 * a * (a * z) / (1 - a ^ 2) ^ 2 + Reflection.biasS cmv a e -
        Reflection.biasS cpv a e := by
      rw [hsq, div_eq_mul_inv]
      exact hnum
    have hden : 0 < a ^ 3 * (a * z) := by positivity
    simp only [RegularReflectionExpression.normalizedValue]
    exact div_pos hnum' hden
  exact Reflection.curvature_pos_of_regular_normalizedValue_pos ha0 ha1' hz0 hz hval

end CKLaneC2R.Endpoint

end


