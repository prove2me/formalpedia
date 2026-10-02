-- Prove2me | Definitions.Def_CK_CKLaneM06_CapSec
-- name    : CK_CKLaneM06_CapSec
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:36:00.180633+00:00
-- url     : https://prove2.me/theorems/e4a943ac-b742-4746-a422-cab3ffc19963
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapSec` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapSec` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapSec` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapSec (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapSec.lean)

import Definitions.Def_CK_CKLaneM06_CapTree

-- ===== source module CKLaneM06.CapSec =====
section

/-!
# Lane M06: secant cap box checker (archived secant criterion, `CAP_COVER` / `EXPANDED_CAP_COVER`)

For cross-half boxes with a large entropy drop, where the normalized trapezoid bound is too lossy,
the archived secant endpoint criterion `G(S) = j + λS - P(Δ+S) + P(S) ≥ 0` is checked directly:

    sPup u - sPlo u' ≤ jLo + dLo² · lam · S

* `jLo ≤ j` : `j = (b-a)(J a - J b)/2`, `J` antitone, so `j ≥ dLo · (J a1 - J b0)/2`; the rational
  value is `dLo · (lamLo a1 - lamHi b0) / (2 LqHi)` (lane E rational logs).
* `P(Δ + S) ≤ P(S + DHi) ≤ sPup u` : `P` monotone (`eta` antitone), `eta h ≤ (1-2u) J u` for `H u ≤ h`.
* `P(S) ≥ sPlo u'` : `eta h ≥ eta (H u') = (1-2u') J u'` for `h ≤ H u'`.
* `lam` : the certified slopes of the trapezoid checker (κ log-sum, M07; or the mean-contact plane).

No margin is stored; every enclosure is recomputed from the box by the kernel.
`secCheck_sound : secCheck B S w = true → CapOn B S`, and the tree type `CTree2` (leaves: trapezoid
witnesses, secant witnesses, vacuous boxes) with `CTree2.sound`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06.Cap

open GeneralCK CKLaneE.FP

/-! ## Profile bounds (corpus `eta_eq_profile`, `entropyInverse_*`, `eta_antitoneOn`) -/

theorem cs_eta_H {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 2) : eta (H u) = (1 - 2 * u) * J u := by
  rw [eta_eq_profile (H_nonneg hu.le (by linarith)) (H_le_one u), entropyInverse_H_lower hu.le hu']

/-- The statement of corpus `eta_le_of_witness` (PsiLowEntropyLeafReplay.lean), reproved from the same
corpus lemmas so that the import closure stays small. -/
theorem cs_eta_le {h v X : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hv0 : 0 < v) (hv1 : v ≤ 1 / 2)
    (hHv : H v ≤ h) (hJ : J v ≤ X) : eta h ≤ (1 - 2 * v) * X := by
  have hspec := entropyInverse_spec hh0.le hh1
  have hu0 : 0 < entropyInverse h := entropyInverse_pos hh0 hh1
  have hu1 : entropyInverse h ≤ 1 / 2 := hspec.2.1
  have hvu : v ≤ entropyInverse h := by
    have hmono := entropyInverse_mono (H_nonneg hv0.le (by linarith)) hh1 hHv
    rwa [entropyInverse_H_lower hv0.le hv1] at hmono
  have hJu : J (entropyInverse h) ≤ J v := J_antitone hv0 hu1 hvu
  have hJu0 : 0 ≤ J (entropyInverse h) := J_nonneg hu0 hu1
  rw [eta_eq_profile hh0.le hh1]
  calc (1 - 2 * entropyInverse h) * J (entropyInverse h)
      ≤ (1 - 2 * v) * J v := mul_le_mul (by linarith) hJu hJu0 (by linarith)
    _ ≤ (1 - 2 * v) * X := mul_le_mul_of_nonneg_left hJ (by linarith)

/-- Lower profile witness: `h ≤ H v` gives `(1-2v) J v ≤ eta h`. -/
theorem cs_eta_ge {h v : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hv0 : 0 < v) (hv1 : v ≤ 1 / 2)
    (hHv : h ≤ H v) : (1 - 2 * v) * J v ≤ eta h := by
  rw [← cs_eta_H hv0 hv1]
  exact eta_antitoneOn ⟨hh0, hh1⟩ ⟨lt_of_lt_of_le hh0 hHv, H_le_one v⟩ hHv

/-- `P` is monotone on `[0,1)`. -/
theorem cs_P_mono {t1 t2 : ℝ} (h0 : 0 ≤ t1) (h12 : t1 ≤ t2) (h2 : t2 < 1) :
    Scalar.P t1 ≤ Scalar.P t2 := by
  unfold Scalar.P
  exact eta_antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

/-- `J` is antitone on `(0,1)`. -/
theorem cs_J_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) : J y ≤ J x := by
  unfold J
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  refine div_le_div_of_nonneg_right ?_ log_two_pos.le
  apply Real.log_le_log (div_pos (by linarith) hy0)
  rw [div_le_div_iff₀ hy0 hx]
  nlinarith

theorem cs_J_ge {v : ℚ} (hpt : ptOk v = true) (hlam : 0 ≤ lamLo v) :
    ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ J (v : ℝ) := by
  obtain ⟨hl, _⟩ := lam_bounds hpt
  obtain ⟨_, hL2⟩ := log_two_mem
  have hL := log_two_pos
  have hlam' : (0 : ℝ) ≤ ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  unfold J
  calc ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((lamLo v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_left hlam' hL hL2
    _ ≤ Real.log ((1 - (v : ℝ)) / v) / Real.log 2 := div_le_div_of_nonneg_right hl hL.le

theorem cs_J_le {v : ℚ} (hpt : ptOk v = true) (hlam : 0 ≤ lamHi v) :
    J (v : ℝ) ≤ ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := by
  obtain ⟨_, hu⟩ := lam_bounds hpt
  obtain ⟨hL1, _⟩ := log_two_mem
  have hL := log_two_pos
  have hLlo := LqLo_pos
  have hlam' : (0 : ℝ) ≤ ((lamHi v : ℚ) : ℝ) := by exact_mod_cast hlam
  unfold J
  calc Real.log ((1 - (v : ℝ)) / v) / Real.log 2 ≤ ((lamHi v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right hu hL.le
    _ ≤ ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := div_le_div_of_nonneg_left hlam' hLlo hL1

/-! ## Rational profile enclosures -/

/-- Upper value of `P` at a checked upper anchor. -/
def sPup (u : ℚ) : ℚ := (1 - 2 * u) * (lamHi u / LqLo)

/-- Lower value of `P` at a checked lower anchor. -/
def sPlo (u : ℚ) : ℚ := (1 - 2 * u) * (lamLo u / LqHi)

/-- Upper anchor: `H u ≤ 1 - y`. -/
def sUpOk (u y : ℚ) : Bool := ptOk u && decide (u < 1 / 2 ∧ 0 ≤ lamHi u ∧ Hhi u ≤ 1 - y)

/-- Lower anchor: `1 - y ≤ H u`. -/
def sLoOk (u y : ℚ) : Bool := ptOk u && decide (u ≤ 1 / 2 ∧ 0 ≤ lamLo u ∧ 1 - y ≤ Hlo u)

theorem sPup_sound {u y : ℚ} (h : sUpOk u y = true) {x : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ (y : ℝ))
    (hy1 : (y : ℝ) < 1) : Scalar.P x ≤ ((sPup u : ℚ) : ℝ) := by
  simp only [sUpOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpt, hu2, hlam, hH⟩ := h
  have hu := ptOk_pos hpt
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu.1
  have hu12 : (u : ℝ) ≤ 1 / 2 := by
    have := qle hu2.le; push_cast at this; exact this
  obtain ⟨_, hHhi⟩ := H_bounds hpt
  have hHq : ((Hhi u : ℚ) : ℝ) ≤ 1 - (y : ℝ) := by
    have := qle hH; push_cast at this; exact this
  have hmono := cs_P_mono hx0 hxy hy1
  have hJ := cs_J_le hpt hlam
  have hPy : Scalar.P (y : ℝ) ≤ (1 - 2 * (u : ℝ)) * (((lamHi u : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ)) := by
    unfold Scalar.P
    exact cs_eta_le (by linarith) (by linarith) hu0 hu12 (by linarith) hJ
  have e : ((sPup u : ℚ) : ℝ) = (1 - 2 * (u : ℝ)) * (((lamHi u : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ)) := by
    simp only [sPup]; push_cast; ring
  rw [e]
  linarith

theorem sPlo_sound {u y : ℚ} (h : sLoOk u y = true) (hy0 : (0 : ℝ) ≤ y) (hy1 : (y : ℝ) < 1) :
    ((sPlo u : ℚ) : ℝ) ≤ Scalar.P (y : ℝ) := by
  simp only [sLoOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpt, hu2, hlam, hH⟩ := h
  have hu := ptOk_pos hpt
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu.1
  have hu12 : (u : ℝ) ≤ 1 / 2 := by
    have := qle hu2; push_cast at this; exact this
  obtain ⟨hHlo, _⟩ := H_bounds hpt
  have hHq : 1 - (y : ℝ) ≤ ((Hlo u : ℚ) : ℝ) := by
    have := qle hH; push_cast at this; exact this
  have hJ := cs_J_ge hpt hlam
  have hge := cs_eta_ge (h := 1 - (y : ℝ)) (by linarith) (by linarith) hu0 hu12 (by linarith)
  have e : ((sPlo u : ℚ) : ℝ) = (1 - 2 * (u : ℝ)) * (((lamLo u : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) := by
    simp only [sPlo]; push_cast; ring
  rw [e]
  unfold Scalar.P
  have h12 : (0 : ℝ) ≤ 1 - 2 * (u : ℝ) := by linarith
  calc (1 - 2 * (u : ℝ)) * (((lamLo u : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) ≤ (1 - 2 * (u : ℝ)) * J u :=
        mul_le_mul_of_nonneg_left hJ h12
    _ ≤ eta (1 - (y : ℝ)) := hge

/-! ## Interior cost lower bound -/

namespace CBox

variable (B : CBox)

/-- Rational lower bound of `ln((1-a1)/a1) - ln((1-b0)/b0)`. -/
def jnum : ℚ := lamLo B.a1 - lamHi B.b0

/-- Rational lower bound of `interiorCost` on the box. -/
def jLo : ℚ := B.dLo * B.jnum / (2 * LqHi)

end CBox

theorem jLo_le {B : CBox} (hbox : B.boxOk = true) (hj : 0 ≤ B.jnum) {a b : ℝ} (ha0 : (B.a0 : ℝ) ≤ a)
    (ha1 : a ≤ B.a1) (hb0 : (B.b0 : ℝ) ≤ b) (hb1 : b ≤ B.b1) (hab : a < b) :
    ((B.jLo : ℚ) : ℝ) ≤ interiorCost a b := by
  obtain ⟨_, _, _, _, _, _, _, _, pa1, pb0, _, _⟩ := boxOk_facts hbox
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hapos : 0 < a := lt_of_lt_of_le A0 ha0
  obtain ⟨hd0, hd⟩ := dLo_facts ha1 hb0 hab
  have hJa : J (B.a1 : ℝ) ≤ J a := cs_J_anti hapos ha1 (by linarith)
  have hJb : J b ≤ J (B.b0 : ℝ) := cs_J_anti B0 hb0 (by linarith)
  have hL := log_two_pos
  obtain ⟨_, hL2⟩ := log_two_mem
  obtain ⟨la1, _⟩ := lam_bounds pa1
  obtain ⟨_, ub0⟩ := lam_bounds pb0
  have hjR : (0 : ℝ) ≤ ((B.jnum : ℚ) : ℝ) := by exact_mod_cast hj
  have ejn : ((B.jnum : ℚ) : ℝ) = ((lamLo B.a1 : ℚ) : ℝ) - ((lamHi B.b0 : ℚ) : ℝ) := by
    unfold CBox.jnum; push_cast; ring
  have hdiff : ((B.jnum : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ J a - J b := by
    have h1 : ((B.jnum : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((B.jnum : ℚ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_left hjR hL hL2
    have h2 : ((B.jnum : ℚ) : ℝ) / Real.log 2 ≤ J (B.a1 : ℝ) - J (B.b0 : ℝ) := by
      unfold J
      rw [← sub_div]
      refine div_le_div_of_nonneg_right ?_ hL.le
      rw [ejn]
      linarith
    linarith
  have ejl : ((B.jLo : ℚ) : ℝ) = ((B.dLo : ℚ) : ℝ) * (((B.jnum : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ)) / 2 := by
    unfold CBox.jLo; push_cast; ring
  rw [ejl]
  unfold interiorCost
  have hq0 : (0 : ℝ) ≤ ((B.jnum : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) := by
    have := LqLo_pos
    have hqq : (0 : ℝ) < ((LqHi : ℚ) : ℝ) := by linarith
    exact div_nonneg hjR hqq.le
  have := mul_le_mul hd hdiff hq0 (by linarith)
  linarith

/-! ## Certified slope (same slopes as the trapezoid checker) -/

theorem slope_box {B : CBox} (hbox : B.boxOk = true) {w : CWit} (hslope : w.slopeOk B = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a < μ.b) (ha0 : (B.a0 : ℝ) ≤ μ.a) (ha1 : μ.a ≤ B.a1)
    (hb0 : (B.b0 : ℝ) ≤ μ.b) (hb1 : μ.b ≤ B.b1) :
    ∃ lamAct : ℝ, interiorCost μ.a μ.b + lamAct * μ.meanDeficit ≤ μ.cost ∧
      (μ.b - μ.a) ^ 2 * ((w.lam B : ℚ) : ℝ) ≤ lamAct ∧ (0 : ℝ) ≤ ((w.lam B : ℚ) : ℝ) := by
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hd20 : 0 ≤ (μ.b - μ.a) ^ 2 := sq_nonneg _
  unfold CWit.slopeOk at hslope
  unfold CWit.lam
  split_ifs at hslope ⊢ with hpl
  · have hl := (plane_coeffs hbox hslope ha0 ha1 hb0 hb1).2.1
    refine ⟨2 * ((B.planeL : ℚ) : ℝ) * (μ.b - μ.a) ^ 2,
      plane_slope_box hbox hslope μ hab ha0 ha1 hb0 hb1, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
  · have hk := hslope
    simp only [CBox.kapOk, decide_eq_true_eq] at hk
    have hk0 : (0 : ℝ) ≤ w.kap := by exact_mod_cast hk.1
    have hapos : 0 < μ.a := lt_of_lt_of_le A0 ha0
    have hbpos : 0 < μ.b := lt_of_lt_of_le B0 hb0
    have hV : 0 < μ.b * (1 - μ.a) := mul_pos hbpos (by linarith)
    have hV1 : 0 < 2 * (B.b1 : ℝ) * (1 - B.a0) := by nlinarith
    have hVle : 2 * (μ.b * (1 - μ.a)) ≤ 2 * (B.b1 : ℝ) * (1 - B.a0) := by nlinarith
    refine ⟨(w.kap : ℝ) * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))),
      kappa_slope_box hbox hslope μ hab ha0 ha1 hb0 hb1, ?_, ?_⟩
    · push_cast
      have h1 : (w.kap : ℝ) / (2 * (B.b1 : ℝ) * (1 - B.a0)) ≤ (w.kap : ℝ) / (2 * (μ.b * (1 - μ.a))) :=
        div_le_div_of_nonneg_left hk0 (by positivity) hVle
      calc (μ.b - μ.a) ^ 2 * ((w.kap : ℝ) / (2 * (B.b1 : ℝ) * (1 - B.a0)))
          ≤ (μ.b - μ.a) ^ 2 * ((w.kap : ℝ) / (2 * (μ.b * (1 - μ.a)))) :=
            mul_le_mul_of_nonneg_left h1 hd20
        _ = (w.kap : ℝ) * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) := by ring
    · push_cast
      exact div_nonneg hk0 hV1.le

/-! ## The secant checker -/

/-- Secant witness: upper anchor `u` (for `P(S + DHi)`), lower anchor `u2` (for `P(S)`), slope
choice and log-sum constant.  No margin is stored. -/
structure SWit where
  u : ℚ
  u2 : ℚ
  plane : Bool
  kap : ℚ
  deriving DecidableEq, Repr

/-- The slope part of a secant witness, in the trapezoid checker's witness format. -/
def SWit.cw (w : SWit) : CWit := ⟨0, 0, w.plane, w.kap⟩

/-- The Boolean secant checker of one cap box at depth `S`. -/
def secCheck (B : CBox) (S : ℚ) (w : SWit) : Bool :=
  B.boxOk && decide (0 ≤ S ∧ S + B.DHi < 1 ∧ 0 ≤ B.jnum) &&
    sUpOk w.u (S + B.DHi) && sLoOk w.u2 S && w.cw.slopeOk B &&
    decide (sPup w.u - sPlo w.u2 ≤ B.jLo + B.dLo * B.dLo * w.cw.lam B * S)

set_option maxHeartbeats 1000000 in
/-- **Soundness of the secant cap box checker.** -/
theorem secCheck_sound {B : CBox} {S : ℚ} {w : SWit} (hc : secCheck B S w = true) : CapOn B S := by
  intro k μ hab hsum ha0 ha1 hb0 hb1 hs
  simp only [secCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
  obtain ⟨hbox, hS0, hSI, hj, hu, hu2, hslope, hfin⟩ := hc
  obtain ⟨A0, _, A1, B0, _, B1⟩ := box_real hbox
  have hS0R : (0 : ℝ) ≤ S := by exact_mod_cast hS0
  set Δ := μ.entropyDrop with hΔ
  set s := μ.meanDeficit with hsd
  have hΔdef : Δ = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hΔ0 : 0 ≤ Δ := μ.entropyDrop_nonneg
  have hsS : s ≤ (S : ℝ) := by rw [hsd, meanDeficit_eq]; exact hs
  have hDHi := drop_le_DHi hbox ha0 ha1 hb0 hb1
  rw [← hΔdef] at hDHi
  have hSIR : (S : ℝ) + ((B.DHi : ℚ) : ℝ) < 1 := by have := qlt hSI; push_cast at this; exact this
  have hI : Δ + (S : ℝ) < 1 := by linarith
  -- `P(Δ + S) ≤ P(S + DHi) ≤ sPup u`
  have hPup : Scalar.P (Δ + S) ≤ ((sPup w.u : ℚ) : ℝ) :=
    sPup_sound hu (x := Δ + (S : ℝ)) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
  -- `sPlo u2 ≤ P(S)`
  have hPlo : ((sPlo w.u2 : ℚ) : ℝ) ≤ Scalar.P (S : ℝ) := sPlo_sound hu2 hS0R (by linarith)
  -- `jLo ≤ j`
  have hjLo := jLo_le hbox hj ha0 ha1 hb0 hb1 hab
  -- the slope
  obtain ⟨lamAct, hslopeAct, hlamAct, hlam0⟩ := slope_box hbox hslope μ hab ha0 ha1 hb0 hb1
  obtain ⟨hd0, hd⟩ := dLo_facts ha1 hb0 hab
  have hfinR : ((sPup w.u : ℚ) : ℝ) - ((sPlo w.u2 : ℚ) : ℝ) ≤
      ((B.jLo : ℚ) : ℝ) + ((B.dLo : ℚ) : ℝ) * ((B.dLo : ℚ) : ℝ) * ((w.cw.lam B : ℚ) : ℝ) * S := by
    have := qle hfin; push_cast at this; exact this
  have hdd : ((B.dLo : ℚ) : ℝ) * ((B.dLo : ℚ) : ℝ) ≤ (μ.b - μ.a) ^ 2 := by nlinarith
  have hl1 : ((B.dLo : ℚ) : ℝ) * ((B.dLo : ℚ) : ℝ) * ((w.cw.lam B : ℚ) : ℝ) ≤ lamAct :=
    (mul_le_mul_of_nonneg_right hdd hlam0).trans hlamAct
  have hl2 := mul_le_mul_of_nonneg_right hl1 hS0R
  have hend : 0 ≤ Scalar.gap (interiorCost μ.a μ.b) lamAct Δ S := by
    unfold Scalar.gap
    linarith
  exact psi_gap_le_cost_of_endpoint μ hslopeAct hsS hI hend

/-! ## Refinement trees with trapezoid and secant leaves -/

/-- A refinement tree whose leaves carry trapezoid witnesses, secant witnesses, or are vacuous. -/
inductive CTree2 where
  | leaf (w : CWit)
  | sec (w : SWit)
  | vac
  | node (ax : ℕ) (l r : CTree2)
  deriving Repr

/-- One reflective Boolean check of a whole refinement subtree. -/
def CTree2.check (S : ℚ) : CTree2 → CBox → Bool
  | leaf w, B => Cap.check B S w
  | sec w, B => secCheck B S w
  | vac, B => vacOk B
  | node ax l r, B => decide (ax < 2) && l.check S (cstep B (2 * ax)) && r.check S (cstep B (2 * ax + 1))

theorem CTree2.sound (S : ℚ) : ∀ (T : CTree2) (B : CBox), T.check S B = true → CapOn B S
  | leaf _, _, h => check_sound h
  | sec _, _, h => secCheck_sound h
  | vac, _, h => vac_sound h
  | node ax l r, B, h => by
      simp only [CTree2.check, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hax, hl⟩, hr⟩ := h
      exact CapOn.merge hax (CTree2.sound S l _ hl) (CTree2.sound S r _ hr)

/-- Per archived node: a checked refinement subtree certifies the node's exact box. -/
theorem CTree2.sound_path {R : CBox} {S : ℚ} {p : List ℕ} {T : CTree2}
    (h : T.check S (cpathBox R p) = true) : CapOn (cpathBox R p) S :=
  CTree2.sound S T _ h

end CKLaneM06.Cap

end


