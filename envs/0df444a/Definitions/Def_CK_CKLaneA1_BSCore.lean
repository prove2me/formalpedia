-- Prove2me | Definitions.Def_CK_CKLaneA1_BSCore
-- name    : CK_CKLaneA1_BSCore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:06:16.759674+00:00
-- url     : https://prove2.me/theorems/06260e9e-36a6-4424-842c-61f78a5227b9
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSCore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSCore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSCore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSCore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSCore.lean)

import Definitions.Def_CK_CKLaneA1_BSAnalysis

/-!
# CKLaneA1.BSCore — the both-small cell core

Interval versions of the scaled both-small formulas `bsC` (normalized gap coefficient
`ν τ coef`) and `bsM` (`m11 / w`), a one-sided contact bracket for cells touching `w = 0`
or the diagonal, and the core soundness theorem.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates
open GeneralCK.Certificates.Reflection (biasE biasB)

def bsCIv (tau p om qu qw sh Sp kh qjh nu nus Rh Wh hh hms : DI) : DI :=
  let rSp := Sp.recip
  let A1 := (qjh.add (((Iv.two.mul p).mul qu).mul Rh)).sub Iv.one
  let Uh := (tau.mul A1).add (om.mul sh)
  let Z := hms.sub ((kh.add qw).mul rSp)
  let zh := (qu.add ((sh.mul kh).mul rSp)).neg
  let mh := ((qu.add qw).add ((p.mul sh).mul Uh)).sub ((p.mul Wh).mul (zh.mul zh))
  let nT := ((((Iv.two.mul tau).mul om).mul nu).sub (((p.mul tau).mul A1).mul nus)).add
    (hms.mul (nus.sub ((((Iv.two.mul p).mul tau).mul Rh).mul nu)))
  let V1 := Uh.sub ((Wh.mul zh).mul Z)
  (mh.mul (nT.sub (((nu.mul tau).mul Wh).mul (Z.mul Z)))).sub (((nu.mul tau).mul p).mul (V1.mul V1))

theorem bsCIv_contains {tau p om qu qw sh Sp kh qjh nu nus Rh Wh hh hms : DI}
    {rtau rp rom rqu rqw rsh rSp rkh rqjh rnu rnus rRh rWh rhh rhms : ℝ}
    (htau : tau.Contains rtau) (hp : p.Contains rp) (hom : om.Contains rom)
    (hqu : qu.Contains rqu) (hqw : qw.Contains rqw) (hsh : sh.Contains rsh)
    (hSp : Sp.Contains rSp) (hkh : kh.Contains rkh) (hqjh : qjh.Contains rqjh)
    (hnu : nu.Contains rnu) (hnus : nus.Contains rnus) (hRh : Rh.Contains rRh)
    (hWh : Wh.Contains rWh) (hhh : hh.Contains rhh) (hhms : hms.Contains rhms)
    (hSp0 : 0 < Sp.lo) :
    (bsCIv tau p om qu qw sh Sp kh qjh nu nus Rh Wh hh hms).Contains
      (bsC rtau rp rom rqu rqw rsh rSp rkh rqjh rnu rnus rRh rWh rhh rhms) := by
  open DyadicInterval in
  have hrSp := recip_sound hSp0 hSp
  have hA1 := sub_sound (add_sound hqjh (mul_sound (mul_sound (mul_sound Iv.two_contains hp) hqu) hRh))
    Iv.one_contains
  have hU := add_sound (mul_sound htau hA1) (mul_sound hom hsh)
  have hZ := sub_sound hhms (mul_sound (add_sound hkh hqw) hrSp)
  have hz := neg_sound (add_sound hqu (mul_sound (mul_sound hsh hkh) hrSp))
  have hm := sub_sound (add_sound (add_sound hqu hqw) (mul_sound (mul_sound hp hsh) hU))
    (mul_sound (mul_sound hp hWh) (mul_sound hz hz))
  have hnT := add_sound (sub_sound (mul_sound (mul_sound (mul_sound Iv.two_contains htau) hom) hnu)
      (mul_sound (mul_sound (mul_sound hp htau) hA1) hnus))
    (mul_sound hhms (sub_sound hnus (mul_sound (mul_sound (mul_sound (mul_sound Iv.two_contains hp)
      htau) hRh) hnu)))
  have hV1 := sub_sound hU (mul_sound (mul_sound hWh hz) hZ)
  have hfin := sub_sound (mul_sound hm (sub_sound hnT (mul_sound (mul_sound (mul_sound hnu htau) hWh)
      (mul_sound hZ hZ)))) (mul_sound (mul_sound (mul_sound hnu htau) hp) (mul_sound hV1 hV1))
  simpa only [bsC, bsCIv, div_eq_mul_inv] using hfin

def bsMIv (tau p qu sh Sp kh F Wh hh : DI) : DI :=
  let zh := (qu.add ((sh.mul kh).mul Sp.recip)).neg
  ((qu.mul ((Iv.one.add tau).add (((Iv.two.mul p).mul tau).mul F))).add
    (sh.mul (hh.sub (p.mul tau)))).sub ((p.mul Wh).mul (zh.mul zh))

theorem bsMIv_contains {tau p qu sh Sp kh F Wh hh : DI}
    {rtau rp rqu rsh rSp rkh rF rWh rhh : ℝ}
    (htau : tau.Contains rtau) (hp : p.Contains rp) (hqu : qu.Contains rqu)
    (hsh : sh.Contains rsh) (hSp : Sp.Contains rSp) (hkh : kh.Contains rkh)
    (hF : F.Contains rF) (hWh : Wh.Contains rWh) (hhh : hh.Contains rhh) (hSp0 : 0 < Sp.lo) :
    (bsMIv tau p qu sh Sp kh F Wh hh).Contains (bsM rtau rp rqu rsh rSp rkh rF rWh rhh) := by
  open DyadicInterval in
  have hrSp := recip_sound hSp0 hSp
  have hz := neg_sound (add_sound hqu (mul_sound (mul_sound hsh hkh) hrSp))
  have hfin := sub_sound (add_sound (mul_sound hqu (add_sound (add_sound Iv.one_contains htau)
      (mul_sound (mul_sound (mul_sound Iv.two_contains hp) htau) hF)))
      (mul_sound hsh (sub_sound hhh (mul_sound hp htau)))) (mul_sound (mul_sound hp hWh) (mul_sound hz hz))
  simpa only [bsM, bsMIv, div_eq_mul_inv] using hfin

/-! ## Contact atoms from real bracket bounds -/

theorem cAtoms_of_bounds {n : ℕ} {L2 : DI} {cd : CData} (hL : L2.Contains (Real.log 2))
    (hlogs : cLogsOK cd = true) (hg0 : 0 ≤ cd.clo) (hg1 : cd.clo ≤ cd.chi) (hg2 : cd.chi < SCz)
    (hq : 0 < (Iv.one.sub ((Iv.pt cd.chi).mul (Iv.pt cd.chi))).lo)
    {C : ℝ} (hC0 : 0 < C) (hC1 : C < 1)
    (hlC : (cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ) ≤ C)
    (hCh : C ≤ (cd.chi:ℝ)/(DyadicInterval.scale 64 : ℝ)) :
    (cC cd).Contains C ∧ (cE n L2 cd).Contains (biasE C) ∧ (cB n L2 cd).Contains (biasB C) ∧
      (cLoC n cd).Contains (Real.log ((1+C)/(1-C)) / C) := by
  have hs := SC_pos
  have hl4 := Bool.and_eq_true_iff.mp hlogs
  have hl3 := Bool.and_eq_true_iff.mp hl4.1
  have hl2 := Bool.and_eq_true_iff.mp hl3.1
  set l : ℝ := (cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ) with hl_def
  set hi : ℝ := (cd.chi:ℝ)/(DyadicInterval.scale 64 : ℝ) with hhi_def
  have hl0 : 0 ≤ l := div_nonneg (by exact_mod_cast hg0) hs.le
  have hlh : l ≤ hi := div_le_div_of_nonneg_right (by exact_mod_cast hg1) hs.le
  have hh1 : hi < 1 := by
    rw [hhi_def, div_lt_one hs]
    have : (cd.chi:ℝ) < (SCz:ℝ) := by exact_mod_cast hg2
    simpa [SCz_real] using this
  have hpL := lpIv_contains (n := n) hL hl2.1
  have hmL := lmIv_contains (n := n) hL hl2.2
  have hpH := lpIv_contains (n := n) hL hl3.2
  have hmH := lmIv_contains (n := n) hL hl4.2
  have hEL : (cEL n L2 cd).Contains (biasE l) := EptIv_contains hL hpL hmL
  have hEH : (cEH n L2 cd).Contains (biasE hi) := EptIv_contains hL hpH hmH
  have hBL : (cBL n L2 cd).Contains (biasB l) := BptIv_contains hL hpL hmL (by linarith) (by linarith)
  have hBH : (cBH n L2 cd).Contains (biasB hi) := BptIv_contains hL hpH hmH (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have : (cd.clo:ℝ) = (DyadicInterval.scale 64 : ℝ) * l := by rw [hl_def]; field_simp
      change (cd.clo:ℝ) ≤ _; rw [this]; exact mul_le_mul_of_nonneg_left hlC hs.le
    · have : (cd.chi:ℝ) = (DyadicInterval.scale 64 : ℝ) * hi := by rw [hhi_def]; field_simp
      change _ ≤ (cd.chi:ℝ); rw [this]; exact mul_le_mul_of_nonneg_left hCh hs.le
  · exact Iv.hull_contains hEH hEL
      (Certificates.Reflection.biasE_antitone ⟨hC0.le, hC1.le⟩ ⟨hl0.trans hlh, hh1.le⟩ hCh)
      (Certificates.Reflection.biasE_antitone ⟨hl0, hlh.trans hh1.le⟩ ⟨hC0.le, hC1.le⟩ hlC)
  · exact Iv.hull_contains hBL hBH (biasB_mono hl0 hlC hC1) (biasB_mono hC0.le hCh hh1)
  · have hb2 := LoC_bounds hl0 hlC hCh hh1 hC0 n
    have hsqL : ((Iv.pt cd.clo).mul (Iv.pt cd.clo)).Contains (l^2) := by
      rw [pow_two]; exact DyadicInterval.mul_sound (Iv.pt_contains cd.clo) (Iv.pt_contains cd.clo)
    have hsq : ((Iv.pt cd.chi).mul (Iv.pt cd.chi)).Contains (hi^2) := by
      rw [pow_two]; exact DyadicInterval.mul_sound (Iv.pt_contains cd.chi) (Iv.pt_contains cd.chi)
    have hsL := serState_sound hsqL n
    have hsH := serState_sound hsq n
    have hlo := DyadicInterval.mul_sound Iv.two_contains hsL.1
    have hhiI := DyadicInterval.add_sound (DyadicInterval.mul_sound Iv.two_contains hsH.1)
      (DyadicInterval.mul_sound (DyadicInterval.mul_sound Iv.two_contains hsH.2)
        (DyadicInterval.recip_sound hq (DyadicInterval.sub_sound Iv.one_contains hsq)))
    exact Iv.hull_contains hlo hhiI hb2.1 (by linarith [hb2.2])

/-- Two-sided bracket (as in `FECore`) or one-sided bracket with `clo = 0` and only a lower
bound `Ylo` for the contact argument. -/
def bsBracketOK (n : ℕ) (L2 : DI) (two : Bool) (Y : DI) (Ylo : ℤ) (cd : CData) : Bool :=
  if two then cBracketOK n L2 Y cd
  else cLogsOK cd && decide (cd.clo = 0 ∧ 0 ≤ cd.chi ∧ cd.chi < SCz ∧ 0 < Ylo) &&
    decide ((cEH n L2 cd).hi ≤ ((Iv.pt Ylo).mul (Iv.pt cd.chi)).lo)

theorem bsBracket_bounds {n : ℕ} {L2 : DI} {two : Bool} {Y : DI} {Ylo : ℤ} {cd : CData}
    (hL : L2.Contains (Real.log 2)) (h : bsBracketOK n L2 two Y Ylo cd = true)
    {y C : ℝ} (hy2 : two = true → Y.Contains y)
    (hy1 : two = false → (Ylo:ℝ)/(DyadicInterval.scale 64 : ℝ) ≤ y)
    (hC0 : 0 < C) (hC1 : C < 1) (heq : biasE C = y * C) :
    cLogsOK cd = true ∧ 0 ≤ cd.clo ∧ cd.clo ≤ cd.chi ∧ cd.chi < SCz ∧
      (cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ) ≤ C ∧ C ≤ (cd.chi:ℝ)/(DyadicInterval.scale 64 : ℝ) := by
  have hs := SC_pos
  cases two with
  | false =>
    simp only [bsBracketOK, Bool.false_eq_true, if_false] at h
    have h0 := Bool.and_eq_true_iff.mp h
    have h1 := Bool.and_eq_true_iff.mp h0.1
    have hg : cd.clo = 0 ∧ 0 ≤ cd.chi ∧ cd.chi < SCz ∧ 0 < Ylo := of_decide_eq_true h1.2
    have hcmp : (cEH n L2 cd).hi ≤ ((Iv.pt Ylo).mul (Iv.pt cd.chi)).lo := of_decide_eq_true h0.2
    have hyl := hy1 rfl
    have hl4 := Bool.and_eq_true_iff.mp h1.1
    have hl3 := Bool.and_eq_true_iff.mp hl4.1
    set hi : ℝ := (cd.chi:ℝ)/(DyadicInterval.scale 64 : ℝ) with hhi_def
    have hh0 : 0 ≤ hi := div_nonneg (by exact_mod_cast hg.2.1) hs.le
    have hh1 : hi < 1 := by
      rw [hhi_def, div_lt_one hs]
      have : (cd.chi:ℝ) < (SCz:ℝ) := by exact_mod_cast hg.2.2.1
      simpa [SCz_real] using this
    have hpH := lpIv_contains (n := n) hL hl3.2
    have hmH := lmIv_contains (n := n) hL hl4.2
    have hEH : (cEH n L2 cd).Contains (biasE hi) := EptIv_contains hL hpH hmH
    have hYlo0 : (0:ℝ) < (Ylo:ℝ)/(DyadicInterval.scale 64 : ℝ) :=
      div_pos (by exact_mod_cast hg.2.2.2) hs
    have hy0 : 0 < y := hYlo0.trans_le hyl
    have hyh : biasE hi ≤ y * hi := by
      have hm := DyadicInterval.mul_sound (Iv.pt_contains Ylo) (Iv.pt_contains cd.chi)
      have h1 : (DyadicInterval.scale 64 : ℝ) * biasE hi ≤
          (DyadicInterval.scale 64 : ℝ) * ((Ylo:ℝ)/(DyadicInterval.scale 64 : ℝ) * hi) := by
        exact hEH.2.trans ((show (((cEH n L2 cd).hi : ℤ) : ℝ) ≤
          (((Iv.pt Ylo).mul (Iv.pt cd.chi)).lo : ℝ) by exact_mod_cast hcmp).trans hm.1)
      have h2 := le_of_mul_le_mul_left h1 hs
      exact h2.trans (mul_le_mul_of_nonneg_right hyl hh0)
    have hl0 : (0:ℝ) ≤ (cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ) := by rw [hg.1]; simp
    have hyl0 : y * ((cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ)) ≤
        biasE ((cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ)) := by
      rw [hg.1]; simp only [Int.cast_zero, zero_div, mul_zero]
      simpa [biasE] using log_two_pos.le
    have hlh : (cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ) ≤ hi := by rw [hg.1]; simp [hh0]
    have hb := Certificates.Reflection.contact_bracket hC0.le hC1.le hl0 hh1.le hlh hy0 heq hyl0 hyh
    exact ⟨h1.1, by simp [hg.1], by rw [hg.1]; exact hg.2.1, hg.2.2.1, hb.1, hb.2⟩
  | true =>
    simp only [bsBracketOK, if_true] at h
    have hY := hy2 rfl
    have h0 := Bool.and_eq_true_iff.mp h
    have h1 := Bool.and_eq_true_iff.mp h0.1
    have hg : 0 ≤ cd.clo ∧ cd.clo ≤ cd.chi ∧ cd.chi < SCz ∧ 0 < Y.lo := of_decide_eq_true h1.2
    have hcmp : (Y.mul (Iv.pt cd.clo)).hi ≤ (cEL n L2 cd).lo ∧
        (cEH n L2 cd).hi ≤ (Y.mul (Iv.pt cd.chi)).lo := of_decide_eq_true h0.2
    have hl4 := Bool.and_eq_true_iff.mp h1.1
    have hl3 := Bool.and_eq_true_iff.mp hl4.1
    have hl2 := Bool.and_eq_true_iff.mp hl3.1
    set l : ℝ := (cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ) with hl_def
    set hi : ℝ := (cd.chi:ℝ)/(DyadicInterval.scale 64 : ℝ) with hhi_def
    have hl0 : 0 ≤ l := div_nonneg (by exact_mod_cast hg.1) hs.le
    have hlh : l ≤ hi := div_le_div_of_nonneg_right (by exact_mod_cast hg.2.1) hs.le
    have hh1 : hi < 1 := by
      rw [hhi_def, div_lt_one hs]
      have : (cd.chi:ℝ) < (SCz:ℝ) := by exact_mod_cast hg.2.2.1
      simpa [SCz_real] using this
    have hy0 : 0 < y := Iv.contains_pos hY hg.2.2.2
    have hpL := lpIv_contains (n := n) hL hl2.1
    have hmL := lmIv_contains (n := n) hL hl2.2
    have hpH := lpIv_contains (n := n) hL hl3.2
    have hmH := lmIv_contains (n := n) hL hl4.2
    have hEL : (cEL n L2 cd).Contains (biasE l) := EptIv_contains hL hpL hmL
    have hEH : (cEH n L2 cd).Contains (biasE hi) := EptIv_contains hL hpH hmH
    have hyl : y * l ≤ biasE l := by
      have hm := DyadicInterval.mul_sound hY (Iv.pt_contains cd.clo)
      have h1 : (DyadicInterval.scale 64 : ℝ) * (y * l) ≤ (DyadicInterval.scale 64 : ℝ) * biasE l :=
        hm.2.trans ((show (((Y.mul (Iv.pt cd.clo)).hi : ℤ) : ℝ) ≤ ((cEL n L2 cd).lo : ℝ) by
          exact_mod_cast hcmp.1).trans hEL.1)
      exact le_of_mul_le_mul_left h1 hs
    have hyh : biasE hi ≤ y * hi := by
      have hm := DyadicInterval.mul_sound hY (Iv.pt_contains cd.chi)
      have h1 : (DyadicInterval.scale 64 : ℝ) * biasE hi ≤ (DyadicInterval.scale 64 : ℝ) * (y * hi) :=
        hEH.2.trans ((show (((cEH n L2 cd).hi : ℤ) : ℝ) ≤ ((Y.mul (Iv.pt cd.chi)).lo : ℝ) by
          exact_mod_cast hcmp.2).trans hm.1)
      exact le_of_mul_le_mul_left h1 hs
    have hb := Certificates.Reflection.contact_bracket hC0.le hC1.le hl0 hh1.le hlh hy0 heq hyl hyh
    exact ⟨h1.1, hg.1, hg.2.1, hg.2.2.1, hb.1, hb.2⟩

end CKLaneA1


