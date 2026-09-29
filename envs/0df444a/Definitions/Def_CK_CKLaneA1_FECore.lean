-- Prove2me | Definitions.Def_CK_CKLaneA1_FECore
-- name    : CK_CKLaneA1_FECore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T16:09:37.723717+00:00
-- url     : https://prove2.me/theorems/46ac9a9d-061e-42e7-b8c4-e4af4940ae98
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FECore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FECore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FECore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FECore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FECore.lean)

import Definitions.Def_CK_CKLaneA1_Analysis

/-!
# CKLaneA1.FECore — the contact-bracket and scaled-kernel cell core

Given interval enclosures of the probability atoms at a point `(u,w)`, `feCore` checks
(by kernel-evaluated integer arithmetic) a contact bracket and the positivity of lower
bounds for `(1/jn u) * actualDetGapCoefficient u w` and `m11 u w`.  `feCore_sound` is the
one-time soundness theorem.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates
open GeneralCK.Certificates.Reflection (biasE biasB)

/-- The scale `2^64` as an integer. -/
def SCz : ℤ := DyadicInterval.scale 64

theorem SCz_real : ((SCz:ℤ):ℝ) = (DyadicInterval.scale 64 : ℝ) := rfl

/-- `log(1+c/SC)` and `log(1-c/SC)`. -/
def lpIv (n : ℕ) (L2 : DI) (c : ℤ) (e : ℕ) : DI := (logIv L2 SCz (SCz + c) e n).neg
def lmIv (n : ℕ) (L2 : DI) (c : ℤ) (e : ℕ) : DI := logIv L2 (SCz - c) SCz e n

theorem lpIv_contains {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {c : ℤ} {e : ℕ}
    (hc : logOK SCz (SCz + c) e = true) :
    (lpIv n L2 c e).Contains (Real.log (1 + (c:ℝ)/(DyadicInterval.scale 64 : ℝ))) := by
  have h := DyadicInterval.neg_sound (logIv_contains (n := n) hL hc)
  have hs := SC_pos
  have hab := (of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1 : 0 < SCz ∧ 0 < SCz + c)
  have hb : (0:ℝ) < ((SCz + c : ℤ):ℝ) := by exact_mod_cast hab.2
  have he : -Real.log (((SCz:ℤ):ℝ) / ((SCz + c : ℤ):ℝ)) =
      Real.log (1 + (c:ℝ)/(DyadicInterval.scale 64 : ℝ)) := by
    rw [← Real.log_inv, inv_div]
    congr 1
    rw [show (SCz + c : ℤ) = DyadicInterval.scale 64 + c from rfl, SCz_real]; push_cast; field_simp
  rw [he] at h; exact h

theorem lmIv_contains {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {c : ℤ} {e : ℕ}
    (hc : logOK (SCz - c) SCz e = true) :
    (lmIv n L2 c e).Contains (Real.log (1 - (c:ℝ)/(DyadicInterval.scale 64 : ℝ))) := by
  have h := logIv_contains (n := n) hL hc
  have hs := SC_pos
  have he : (((SCz - c : ℤ)):ℝ) / ((SCz:ℤ):ℝ) = 1 - (c:ℝ)/(DyadicInterval.scale 64 : ℝ) := by
    rw [show (SCz - c : ℤ) = DyadicInterval.scale 64 - c from rfl, SCz_real]; push_cast; field_simp
  rw [he] at h; exact h

def EptIv (L2 lp lm : DI) (c : ℤ) : DI :=
  L2.sub ((((Iv.one.add (Iv.pt c)).mul lp).add ((Iv.one.sub (Iv.pt c)).mul lm)).mul Iv.two.recip)

def BptIv (L2 lp lm : DI) : DI := L2.sub ((lm.add lp).mul Iv.two.recip)

theorem two_recip_contains : Iv.two.recip.Contains ((2:ℝ)⁻¹) := by
  have h : 0 < Iv.two.lo := by decide +kernel
  exact DyadicInterval.recip_sound h Iv.two_contains

theorem EptIv_contains {L2 lp lm : DI} {c : ℤ} (hL : L2.Contains (Real.log 2))
    (hp : lp.Contains (Real.log (1 + (c:ℝ)/(DyadicInterval.scale 64 : ℝ))))
    (hm : lm.Contains (Real.log (1 - (c:ℝ)/(DyadicInterval.scale 64 : ℝ)))) :
    (EptIv L2 lp lm c).Contains (biasE ((c:ℝ)/(DyadicInterval.scale 64 : ℝ))) := by
  rw [biasE_eq_expl]
  open DyadicInterval in
  exact sub_sound hL (mul_sound (add_sound (mul_sound (add_sound Iv.one_contains (Iv.pt_contains c)) hp)
    (mul_sound (sub_sound Iv.one_contains (Iv.pt_contains c)) hm)) two_recip_contains)

theorem BptIv_contains {L2 lp lm : DI} {c : ℤ} (hL : L2.Contains (Real.log 2))
    (hp : lp.Contains (Real.log (1 + (c:ℝ)/(DyadicInterval.scale 64 : ℝ))))
    (hm : lm.Contains (Real.log (1 - (c:ℝ)/(DyadicInterval.scale 64 : ℝ))))
    (hc0 : -1 < (c:ℝ)/(DyadicInterval.scale 64 : ℝ)) (hc1 : (c:ℝ)/(DyadicInterval.scale 64 : ℝ) < 1) :
    (BptIv L2 lp lm).Contains (biasB ((c:ℝ)/(DyadicInterval.scale 64 : ℝ))) := by
  rw [biasB_eq_expl hc0 hc1]
  open DyadicInterval in
  exact sub_sound hL (mul_sound (add_sound hm hp) two_recip_contains)

/-- Contact-bracket data of one cell (`C ∈ [clo, chi]/2^64`) with log exponents. -/
structure CData where
  clo : ℤ
  chi : ℤ
  ePlo : ℕ
  eMlo : ℕ
  ePhi : ℕ
  eMhi : ℕ
  deriving Repr

def cLogsOK (cd : CData) : Bool :=
  logOK SCz (SCz + cd.clo) cd.ePlo && logOK (SCz - cd.clo) SCz cd.eMlo &&
  logOK SCz (SCz + cd.chi) cd.ePhi && logOK (SCz - cd.chi) SCz cd.eMhi

def cEL (n : ℕ) (L2 : DI) (cd : CData) : DI :=
  EptIv L2 (lpIv n L2 cd.clo cd.ePlo) (lmIv n L2 cd.clo cd.eMlo) cd.clo
def cEH (n : ℕ) (L2 : DI) (cd : CData) : DI :=
  EptIv L2 (lpIv n L2 cd.chi cd.ePhi) (lmIv n L2 cd.chi cd.eMhi) cd.chi
def cBL (n : ℕ) (L2 : DI) (cd : CData) : DI :=
  BptIv L2 (lpIv n L2 cd.clo cd.ePlo) (lmIv n L2 cd.clo cd.eMlo)
def cBH (n : ℕ) (L2 : DI) (cd : CData) : DI :=
  BptIv L2 (lpIv n L2 cd.chi cd.ePhi) (lmIv n L2 cd.chi cd.eMhi)

def cBracketOK (n : ℕ) (L2 : DI) (Y : DI) (cd : CData) : Bool :=
  cLogsOK cd && decide (0 ≤ cd.clo ∧ cd.clo ≤ cd.chi ∧ cd.chi < SCz ∧ 0 < Y.lo) &&
  decide ((Y.mul (Iv.pt cd.clo)).hi ≤ (cEL n L2 cd).lo ∧ (cEH n L2 cd).hi ≤ (Y.mul (Iv.pt cd.chi)).lo)

def cC (cd : CData) : DI := Iv.mk cd.clo cd.chi
def cE (n : ℕ) (L2 : DI) (cd : CData) : DI := Iv.mk (cEH n L2 cd).lo (cEL n L2 cd).hi
def cB (n : ℕ) (L2 : DI) (cd : CData) : DI := Iv.mk (cBL n L2 cd).lo (cBH n L2 cd).hi

def cLoC (n : ℕ) (cd : CData) : DI :=
  let sL := serState ((Iv.pt cd.clo).mul (Iv.pt cd.clo)) n
  let sH := serState ((Iv.pt cd.chi).mul (Iv.pt cd.chi)) n
  let hsq := (Iv.pt cd.chi).mul (Iv.pt cd.chi)
  Iv.mk (Iv.two.mul sL.1).lo ((Iv.two.mul sH.1).add ((Iv.two.mul sH.2).mul (Iv.one.sub hsq).recip)).hi

def cFoC (LoC E B C : DI) : DI :=
  LoC.add ((Iv.two.mul E).mul ((Iv.one.sub (C.mul C)).mul B).recip)

def cG (E B C : DI) : DI :=
  ((DyadicInterval.ofInt 64 8).mul (((E.mul E).mul E).mul ((Iv.two.mul B).sub (C.mul C)))).mul
    (((Iv.one.sub (C.mul C)).mul (Iv.one.sub (C.mul C))).mul ((B.mul B).mul B)).recip

/-- Soundness of the contact bracket and of the `C, E, B, LoC` enclosures. -/
theorem cAtoms_sound {n : ℕ} {L2 Y : DI} {cd : CData} (hL : L2.Contains (Real.log 2))
    (h : cBracketOK n L2 Y cd = true)
    (hq : 0 < (Iv.one.sub ((Iv.pt cd.chi).mul (Iv.pt cd.chi))).lo)
    {y C : ℝ} (hy : Y.Contains y) (hC0 : 0 < C) (hC1 : C < 1) (heq : biasE C = y * C) :
    (cC cd).Contains C ∧ (cE n L2 cd).Contains (biasE C) ∧ (cB n L2 cd).Contains (biasB C) ∧
      (cLoC n cd).Contains (Real.log ((1+C)/(1-C)) / C) := by
  have hs := SC_pos
  have h0 := Bool.and_eq_true_iff.mp h
  have h1 := Bool.and_eq_true_iff.mp h0.1
  have hlogs := h1.1
  have hg : 0 ≤ cd.clo ∧ cd.clo ≤ cd.chi ∧ cd.chi < SCz ∧ 0 < Y.lo := of_decide_eq_true h1.2
  have hcmp : (Y.mul (Iv.pt cd.clo)).hi ≤ (cEL n L2 cd).lo ∧
      (cEH n L2 cd).hi ≤ (Y.mul (Iv.pt cd.chi)).lo := of_decide_eq_true h0.2
  have hl4 := Bool.and_eq_true_iff.mp hlogs
  have hl3 := Bool.and_eq_true_iff.mp hl4.1
  have hl2 := Bool.and_eq_true_iff.mp hl3.1
  -- the endpoints as reals
  set l : ℝ := (cd.clo:ℝ)/(DyadicInterval.scale 64 : ℝ) with hl_def
  set hi : ℝ := (cd.chi:ℝ)/(DyadicInterval.scale 64 : ℝ) with hhi_def
  have hl0 : 0 ≤ l := div_nonneg (by exact_mod_cast hg.1) hs.le
  have hlh : l ≤ hi := div_le_div_of_nonneg_right (by exact_mod_cast hg.2.1) hs.le
  have hh1 : hi < 1 := by
    rw [hhi_def, div_lt_one hs]
    have : (cd.chi:ℝ) < (SCz:ℝ) := by exact_mod_cast hg.2.2.1
    simpa [SCz_real] using this
  have hy0 : 0 < y := Iv.contains_pos hy hg.2.2.2
  -- logs and E, B at the endpoints
  have hpL := lpIv_contains (n := n) hL hl2.1
  have hmL := lmIv_contains (n := n) hL hl2.2
  have hpH := lpIv_contains (n := n) hL hl3.2
  have hmH := lmIv_contains (n := n) hL hl4.2
  have hEL : (cEL n L2 cd).Contains (biasE l) := EptIv_contains hL hpL hmL
  have hEH : (cEH n L2 cd).Contains (biasE hi) := EptIv_contains hL hpH hmH
  have hBL : (cBL n L2 cd).Contains (biasB l) := BptIv_contains hL hpL hmL (by linarith) (by linarith)
  have hBH : (cBH n L2 cd).Contains (biasB hi) := BptIv_contains hL hpH hmH (by linarith) (by linarith)
  -- the bracket
  have hyl : y * l ≤ biasE l := by
    have hm := DyadicInterval.mul_sound hy (Iv.pt_contains cd.clo)
    have h1 : (DyadicInterval.scale 64 : ℝ) * (y * l) ≤ (DyadicInterval.scale 64 : ℝ) * biasE l := by
      have := hm.2.trans ((show (((Y.mul (Iv.pt cd.clo)).hi : ℤ) : ℝ) ≤ ((cEL n L2 cd).lo : ℝ) by
        exact_mod_cast hcmp.1).trans hEL.1)
      exact this
    exact le_of_mul_le_mul_left h1 hs
  have hyh : biasE hi ≤ y * hi := by
    have hm := DyadicInterval.mul_sound hy (Iv.pt_contains cd.chi)
    have h1 : (DyadicInterval.scale 64 : ℝ) * biasE hi ≤ (DyadicInterval.scale 64 : ℝ) * (y * hi) := by
      exact hEH.2.trans ((show (((cEH n L2 cd).hi : ℤ) : ℝ) ≤ ((Y.mul (Iv.pt cd.chi)).lo : ℝ) by
        exact_mod_cast hcmp.2).trans hm.1)
    exact le_of_mul_le_mul_left h1 hs
  have hb := Certificates.Reflection.contact_bracket hC0.le hC1.le hl0 hh1.le hlh hy0 heq hyl hyh
  have hlC : l ≤ C := hb.1
  have hCh : C ≤ hi := hb.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- C
    refine ⟨?_, ?_⟩
    · have : (cd.clo:ℝ) = (DyadicInterval.scale 64 : ℝ) * l := by rw [hl_def]; field_simp
      change (cd.clo:ℝ) ≤ _; rw [this]; exact mul_le_mul_of_nonneg_left hlC hs.le
    · have : (cd.chi:ℝ) = (DyadicInterval.scale 64 : ℝ) * hi := by rw [hhi_def]; field_simp
      change _ ≤ (cd.chi:ℝ); rw [this]; exact mul_le_mul_of_nonneg_left hCh hs.le
  · -- E
    exact Iv.hull_contains hEH hEL
      (Certificates.Reflection.biasE_antitone ⟨hC0.le, hC1.le⟩ ⟨hl0.trans hlh, hh1.le⟩ hCh)
      (Certificates.Reflection.biasE_antitone ⟨hl0, hlh.trans hh1.le⟩ ⟨hC0.le, hC1.le⟩ hlC)
  · -- B
    exact Iv.hull_contains hBL hBH (biasB_mono hl0 hlC hC1) (biasB_mono hC0.le hCh hh1)
  · -- LoC
    have hb2 := LoC_bounds hl0 hlC hCh hh1 hC0 n
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

/-- The cell core check. -/
def feCore (n : ℕ) (L2 : DI) (cd : CData) (It Iqu Iku Iu IJw Iqw Is IS : DI) (useJ : Bool)
    (Ij : DI) : Bool :=
  let Y := IS.mul (Iv.two.mul Is).recip
  let C := cC cd
  let E := cE n L2 cd
  let B := cB n L2 cd
  let FoC := cFoC (cLoC n cd) E B C
  let F := C.mul FoC
  let R := FoC.mul ((Iv.two.mul E).mul IS.recip)
  let W := (cG E B C).mul IS.recip
  let hh := Iv.one.sub (Iv.two.mul Iu)
  let qjD := ((Iqu.mul IJw).sub Iku).mul Is.recip
  let tjD := ((It.mul IJw).sub Iv.one).mul Is.recip
  let qj := if useJ then Iv.meet qjD (Iqu.mul Ij) else qjD
  let tj := if useJ then Iv.meet tjD (It.mul Ij) else tjD
  let tc := feTcoefIvJ It Iqu Iku IJw Iqw Is IS R W hh qj tj
  let mm := feM11Iv It Iqu Iku IJw Is IS F W hh
  cBracketOK n L2 Y cd &&
  decide (0 < Is.lo ∧ 0 < IS.lo ∧ 0 < (Iv.two.mul Is).lo ∧
    0 < (Iv.one.sub ((Iv.pt cd.chi).mul (Iv.pt cd.chi))).lo ∧
    0 < ((Iv.one.sub (C.mul C)).mul B).lo ∧
    0 < (((Iv.one.sub (C.mul C)).mul (Iv.one.sub (C.mul C))).mul ((B.mul B).mul B)).lo ∧
    0 < tc.lo ∧ 0 < mm.lo)

theorem feCore_sound {n : ℕ} {L2 : DI} {cd : CData} {It Iqu Iku Iu IJw Iqw Is IS : DI}
    {useJ : Bool} {Ij : DI}
    (hL : L2.Contains (Real.log 2)) (h : feCore n L2 cd It Iqu Iku Iu IJw Iqw Is IS useJ Ij = true)
    {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2)
    (ht : It.Contains (1 / jn u)) (hqu : Iqu.Contains (qp u)) (hku : Iku.Contains (qp u * jn u))
    (huI : Iu.Contains u) (hJw : IJw.Contains (jn w)) (hqw : Iqw.Contains (qp w))
    (hs : Is.Contains (w - u)) (hS : IS.Contains (entropySum u w))
    (hj : useJ = true → Ij.Contains ((jn w - jn u) / (w - u))) :
    0 < (1 / jn u) * actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  unfold feCore at h
  simp only [] at h
  have h0 := Bool.and_eq_true_iff.mp h
  have hg : 0 < Is.lo ∧ 0 < IS.lo ∧ 0 < (Iv.two.mul Is).lo ∧
    0 < (Iv.one.sub ((Iv.pt cd.chi).mul (Iv.pt cd.chi))).lo ∧
    0 < ((Iv.one.sub ((cC cd).mul (cC cd))).mul (cB n L2 cd)).lo ∧
    0 < (((Iv.one.sub ((cC cd).mul (cC cd))).mul (Iv.one.sub ((cC cd).mul (cC cd)))).mul
      (((cB n L2 cd).mul (cB n L2 cd)).mul (cB n L2 cd))).lo ∧ _ ∧ _ := of_decide_eq_true h0.2
  obtain ⟨hs0, hS0, h2s0, hq0, hfb0, hg0, htc0, hmm0⟩ := hg
  -- the contact
  obtain ⟨hC0, hC1, heq⟩ := contact_facts hu huw hw
  have hY := DyadicInterval.mul_sound hS (DyadicInterval.recip_sound h2s0
    (DyadicInterval.mul_sound Iv.two_contains hs))
  have heq' : biasE (contact u w) = (entropySum u w * (2 * (w - u))⁻¹) * contact u w := by
    rw [heq, div_eq_mul_inv]
  obtain ⟨hCI, hEI, hBI, hLI⟩ := cAtoms_sound hL h0.1 hq0 hY hC0 hC1 heq'
  set C := contact u w with hC_def
  -- derived contact quantities
  have hFoC : (cFoC (cLoC n cd) (cE n L2 cd) (cB n L2 cd) (cC cd)).Contains (foc C) := by
    unfold cFoC foc
    exact DyadicInterval.add_sound hLI (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound Iv.two_contains hEI)
      (DyadicInterval.recip_sound hfb0 (DyadicInterval.mul_sound
        (DyadicInterval.sub_sound Iv.one_contains (DyadicInterval.mul_sound hCI hCI)) hBI)))
  have hF : ((cC cd).mul (cFoC (cLoC n cd) (cE n L2 cd) (cB n L2 cd) (cC cd))).Contains (Fs C) := by
    rw [Fs_eq_foc hC0 hC1]
    exact DyadicInterval.mul_sound hCI hFoC
  have hrS := DyadicInterval.recip_sound hS0 hS
  have hR : ((cFoC (cLoC n cd) (cE n L2 cd) (cB n L2 cd) (cC cd)).mul
      ((Iv.two.mul (cE n L2 cd)).mul IS.recip)).Contains (regularFsGap u w) := by
    rw [regularFsGap_eq_foc hu huw hw]
    exact DyadicInterval.mul_sound hFoC (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound Iv.two_contains hEI) hrS)
  have hGI : (cG (cE n L2 cd) (cB n L2 cd) (cC cd)).Contains (gW C) := by
    unfold cG gW
    open DyadicInterval in
    exact mul_sound (mul_sound (Iv.ofInt_contains 8) (mul_sound (mul_sound (mul_sound hEI hEI) hEI)
      (sub_sound (mul_sound Iv.two_contains hBI) (mul_sound hCI hCI))))
      (recip_sound hg0 (mul_sound (mul_sound (sub_sound Iv.one_contains (mul_sound hCI hCI))
        (sub_sound Iv.one_contains (mul_sound hCI hCI))) (mul_sound (mul_sound hBI hBI) hBI)))
  have hW1 : ((cG (cE n L2 cd) (cB n L2 cd) (cC cd)).mul IS.recip).Contains (regularWeight u w) := by
    rw [regularWeight_eq_gW hu huw hw]
    exact DyadicInterval.mul_sound hGI hrS
  have hW2 : ((cG (cE n L2 cd) (cB n L2 cd) (cC cd)).mul IS.recip).Contains (weight u w) := by
    rw [weight_eq_gW hu huw hw]
    exact DyadicInterval.mul_sound hGI hrS
  have hhh : (Iv.one.sub (Iv.two.mul Iu)).Contains (1 - 2*u) :=
    DyadicInterval.sub_sound Iv.one_contains (DyadicInterval.mul_sound Iv.two_contains huI)
  have hrs := DyadicInterval.recip_sound hs0 hs
  have hJu : jn u ≠ 0 := (jn_pos hu (by linarith)).ne'
  have hd : w - u ≠ 0 := (sub_pos.mpr huw).ne'
  have hqjD : (((Iqu.mul IJw).sub Iku).mul Is.recip).Contains
      ((qp u * jn w - qp u * jn u) / (w - u)) := by
    rw [div_eq_mul_inv]
    exact DyadicInterval.mul_sound (DyadicInterval.sub_sound (DyadicInterval.mul_sound hqu hJw) hku) hrs
  have htjD : (((It.mul IJw).sub Iv.one).mul Is.recip).Contains ((1 / jn u * jn w - 1) / (w - u)) := by
    rw [div_eq_mul_inv (1 / jn u * jn w - 1)]
    exact DyadicInterval.mul_sound (DyadicInterval.sub_sound (DyadicInterval.mul_sound ht hJw)
      Iv.one_contains) hrs
  have hqj : (if useJ then Iv.meet (((Iqu.mul IJw).sub Iku).mul Is.recip) (Iqu.mul Ij)
      else ((Iqu.mul IJw).sub Iku).mul Is.recip).Contains ((qp u * jn w - qp u * jn u) / (w - u)) := by
    cases hu' : useJ
    · simpa using hqjD
    · simp only [if_true]
      refine Iv.meet_contains hqjD ?_
      have e : (qp u * jn w - qp u * jn u) / (w - u) = qp u * ((jn w - jn u) / (w - u)) := by ring
      rw [e]; exact DyadicInterval.mul_sound hqu (hj hu')
  have htj : (if useJ then Iv.meet (((It.mul IJw).sub Iv.one).mul Is.recip) (It.mul Ij)
      else ((It.mul IJw).sub Iv.one).mul Is.recip).Contains ((1 / jn u * jn w - 1) / (w - u)) := by
    cases hu' : useJ
    · simpa using htjD
    · simp only [if_true]
      refine Iv.meet_contains htjD ?_
      have e : (1 / jn u * jn w - 1) / (w - u) = 1 / jn u * ((jn w - jn u) / (w - u)) := by
        field_simp
      rw [e]; exact DyadicInterval.mul_sound ht (hj hu')
  have htc := feTcoefIvJ_contains ht hqu hku hJw hqw hs hS hR hW1 hhh hqj htj hS0
  have hmm := feM11Iv_contains ht hqu hku hJw hs hS hF hW2 hhh hS0
  rw [← tcoef_identity hu huw hw] at htc
  rw [← m11_identity hu huw hw] at hmm
  exact ⟨Iv.contains_pos htc htc0, Iv.contains_pos hmm hmm0⟩

#print axioms cAtoms_sound
#print axioms feCore_sound

end CKLaneA1


