-- Prove2me | Definitions.Def_CK_CKLaneN1_CapSlope
-- name    : CK_CKLaneN1_CapSlope
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:01:09.492607+00:00
-- url     : https://prove2.me/theorems/4d78e38c-e27e-45c8-82a3-8464193eb48f
-- title:
--   Courtade–Kumar proof module `CKLaneN1.CapSlope` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.CapSlope` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.CapSlope` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.CapSlope (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/CapSlope.lean)

import Definitions.Def_CK_CKLaneN1_Tree
import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryThetaBracketBridge

-- ===== source module CKLaneN1.CapSlope =====
section

set_option autoImplicit false

/-!
# Lane N1: exact-rational radial-slope bounds and the capital-exclusion leaf checker

`Θ = e8Theta`, `Θ(x) = radialSlope (radialContact (2x) 1)` with
`radialSlope v = J v + (1 - 2v) hn v / (2 log 2 · v (1-v) kap v)`.

For a rational `v` accepted by `CKLaneE.FP.ptOk` (certified `log v`, `log (1 - v)`, `log 2`), the
rationals `slopeLo v ≤ radialSlope v ≤ slopeHi v` are computed exactly. With contact brackets
(`1 - 2v ≤ 2x·H(v)` resp. `2x·H(v) ≤ 1 - 2v`) they bound `Θ(x)` (corpus bridge
`ZeroCapLeftStationaryThetaBracket`).

Leaf claim (box `[U0,U1] × [W0,W1]`): `Θ(U + 2W) ≤ Θ(U) + Θ(W)` on the whole box, from
`Θ(U + 2W) ≤ Θ(U1 + 2W1) ≤ slopeHi vS ≤ slopeLo vA + slopeLo vW ≤ Θ(U0) + Θ(W0) ≤ Θ(U) + Θ(W)`.
-/

namespace CKLaneN1.Capital

open GeneralCK CKLaneE.FP GeneralCK.Certificates.Mixed

/-- Leaf witness: dyadic contact proposals at `U0`, `W0` (upper) and `U1 + 2 W1` (lower). -/
structure CapWit where
  vA : ℚ
  vW : ℚ
  vS : ℚ
  deriving Repr

/-- Lower bound of `kap v = -(log v + log (1 - v))/2`. -/
def kapLoQ (v : ℚ) : ℚ := -(lHi v + l1Hi v) / 2
/-- Upper bound of `kap v`. -/
def kapHiQ (v : ℚ) : ℚ := -(lLo v + l1Lo v) / 2

/-- Lower bound of `radialSlope v`. -/
def slopeLo (v : ℚ) : ℚ :=
  lamLo v / LqHi + (1 - 2 * v) * HnumLo v / (2 * LqHi * v * (1 - v) * kapHiQ v)

/-- Upper bound of `radialSlope v`. -/
def slopeHi (v : ℚ) : ℚ :=
  lamHi v / LqLo + (1 - 2 * v) * HnumHi v / (2 * LqLo * v * (1 - v) * kapLoQ v)

def slopeLoOk (v : ℚ) : Bool :=
  ptOk v && decide (v < 1 / 2) && decide (0 ≤ lamLo v) && decide (0 ≤ HnumLo v) &&
    decide (0 < kapLoQ v)

def slopeHiOk (v : ℚ) : Bool :=
  ptOk v && decide (v < 1 / 2) && decide (0 < kapLoQ v)

theorem LqLo_le' : ((LqLo : ℚ) : ℝ) ≤ Real.log 2 := log_two_mem.1
theorem LqHi_ge' : Real.log 2 ≤ ((LqHi : ℚ) : ℝ) := log_two_mem.2

theorem hn_bounds {v : ℚ} (h : ptOk v = true) :
    ((HnumLo v : ℚ) : ℝ) ≤ hn (v : ℝ) ∧ hn (v : ℝ) ≤ ((HnumHi v : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := ptOk_sound h
  obtain ⟨hv0, hv1⟩ := ptOk_pos h
  have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
  have hv1R : (v : ℝ) < 1 := by exact_mod_cast hv1
  have hc : (0 : ℝ) ≤ 1 - v := by linarith
  have e1 := mul_le_mul_of_nonneg_left h2 hv0R.le
  have e2 := mul_le_mul_of_nonneg_left h4 hc
  have e3 := mul_le_mul_of_nonneg_left h1 hv0R.le
  have e4 := mul_le_mul_of_nonneg_left h3 hc
  have hhn : hn (v : ℝ) = -((v : ℝ) * Real.log v) - ((1 - (v : ℝ)) * Real.log (1 - v)) := by
    unfold hn; ring
  simp only [HnumLo, HnumHi]
  push_cast
  rw [hhn]
  constructor <;> linarith

theorem kap_bounds {v : ℚ} (h : ptOk v = true) :
    ((kapLoQ v : ℚ) : ℝ) ≤ kap (v : ℝ) ∧ kap (v : ℝ) ≤ ((kapHiQ v : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := ptOk_sound h
  obtain ⟨hv0, hv1⟩ := ptOk_pos h
  have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
  have hv1R : (v : ℝ) < 1 := by exact_mod_cast hv1
  have hk : kap (v : ℝ) = -(Real.log v + Real.log (1 - v)) / 2 := by
    unfold kap
    rw [Real.log_mul hv0R.ne' (by linarith)]
  simp only [kapLoQ, kapHiQ]
  push_cast
  rw [hk]
  constructor <;> linarith

theorem J_ge {v : ℚ} (h : ptOk v = true) (hlam : 0 ≤ lamLo v) :
    ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ J (v : ℝ) := by
  obtain ⟨hl, -⟩ := lam_bounds h
  have hL := log_two_pos
  have hlamR : (0 : ℝ) ≤ ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  unfold J
  calc ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((lamLo v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_left hlamR hL LqHi_ge'
    _ ≤ Real.log ((1 - (v : ℝ)) / v) / Real.log 2 := div_le_div_of_nonneg_right hl hL.le

theorem J_le {v : ℚ} (h : ptOk v = true) (hv2 : (v : ℝ) ≤ 1 / 2) :
    J (v : ℝ) ≤ ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := by
  obtain ⟨-, hu⟩ := lam_bounds h
  obtain ⟨hv0, -⟩ := ptOk_pos h
  have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
  have hL := log_two_pos
  have hq : 1 ≤ (1 - (v : ℝ)) / v := by rw [le_div_iff₀ hv0R]; linarith
  have hlog0 : 0 ≤ Real.log ((1 - (v : ℝ)) / v) := Real.log_nonneg hq
  have hlamR : (0 : ℝ) ≤ ((lamHi v : ℚ) : ℝ) := hlog0.trans hu
  unfold J
  calc Real.log ((1 - (v : ℝ)) / v) / Real.log 2 ≤ ((lamHi v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right hu hL.le
    _ ≤ ((lamHi v : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) :=
        div_le_div_of_nonneg_left hlamR LqLo_pos LqLo_le'

theorem hn_nonneg' {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : 0 ≤ hn v := by
  rw [hn_eq_H_mul_log]
  exact mul_nonneg (H_nonneg hv0.le hv1.le) log_two_pos.le

theorem slopeLo_le {v : ℚ} (h : slopeLoOk v = true) :
    ((slopeLo v : ℚ) : ℝ) ≤ radialSlope (v : ℝ) := by
  simp only [slopeLoOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hpt, hv2⟩, hlam⟩, hH⟩, hk⟩ := h
  obtain ⟨hv0, hv1⟩ := ptOk_pos hpt
  have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
  have hv2R : (v : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h'
    linarith
  have hHR : (0 : ℝ) ≤ ((HnumLo v : ℚ) : ℝ) := by exact_mod_cast hH
  have hkR : (0 : ℝ) < ((kapLoQ v : ℚ) : ℝ) := by exact_mod_cast hk
  obtain ⟨hn1, -⟩ := hn_bounds hpt
  obtain ⟨hk1, hk2⟩ := kap_bounds hpt
  have hkap : 0 < kap (v : ℝ) := hkR.trans_le hk1
  have hL := log_two_pos
  have hr : (0 : ℝ) ≤ 1 - 2 * v := by linarith
  have hvv : (0 : ℝ) < (v : ℝ) * (1 - v) := mul_pos hv0R (by linarith)
  have hD : 0 < 2 * Real.log 2 * (v : ℝ) * (1 - v) * kap (v : ℝ) := by
    have := mul_pos (mul_pos (mul_pos two_pos hL) hvv) hkap
    nlinarith [this]
  have hDle : 2 * Real.log 2 * (v : ℝ) * (1 - v) * kap (v : ℝ) ≤
      2 * ((LqHi : ℚ) : ℝ) * (v : ℝ) * (1 - v) * ((kapHiQ v : ℚ) : ℝ) := by
    have h1 : Real.log 2 * kap (v : ℝ) ≤ ((LqHi : ℚ) : ℝ) * ((kapHiQ v : ℚ) : ℝ) :=
      mul_le_mul LqHi_ge' hk2 hkap.le (le_trans hL.le LqHi_ge')
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * ((v : ℝ) * (1 - v)) by positivity)
    nlinarith [h2]
  have hNle : (1 - 2 * (v : ℝ)) * ((HnumLo v : ℚ) : ℝ) ≤ (1 - 2 * (v : ℝ)) * hn (v : ℝ) :=
    mul_le_mul_of_nonneg_left hn1 hr
  have hN0 : 0 ≤ (1 - 2 * (v : ℝ)) * ((HnumLo v : ℚ) : ℝ) := mul_nonneg hr hHR
  have hT : (1 - 2 * (v : ℝ)) * ((HnumLo v : ℚ) : ℝ) /
      (2 * ((LqHi : ℚ) : ℝ) * (v : ℝ) * (1 - v) * ((kapHiQ v : ℚ) : ℝ)) ≤
      (1 - 2 * (v : ℝ)) * hn (v : ℝ) / (2 * Real.log 2 * (v : ℝ) * (1 - v) * kap (v : ℝ)) :=
    (div_le_div_of_nonneg_left hN0 hD hDle).trans (div_le_div_of_nonneg_right hNle hD.le)
  have hJ := J_ge hpt hlam
  simp only [slopeLo]
  push_cast
  unfold radialSlope
  linarith

theorem le_slopeHi {v : ℚ} (h : slopeHiOk v = true) :
    radialSlope (v : ℝ) ≤ ((slopeHi v : ℚ) : ℝ) := by
  simp only [slopeHiOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpt, hv2⟩, hk⟩ := h
  obtain ⟨hv0, hv1⟩ := ptOk_pos hpt
  have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
  have hv1R : (v : ℝ) < 1 := by exact_mod_cast hv1
  have hv2R : (v : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h'
    linarith
  have hkR : (0 : ℝ) < ((kapLoQ v : ℚ) : ℝ) := by exact_mod_cast hk
  obtain ⟨-, hn2⟩ := hn_bounds hpt
  obtain ⟨hk1, -⟩ := kap_bounds hpt
  have hkap : 0 < kap (v : ℝ) := hkR.trans_le hk1
  have hL := log_two_pos
  have hr : (0 : ℝ) ≤ 1 - 2 * v := by linarith
  have hvv : (0 : ℝ) < (v : ℝ) * (1 - v) := mul_pos hv0R (by linarith)
  have hhn0 := hn_nonneg' hv0R hv1R
  have hDlo : 0 < 2 * ((LqLo : ℚ) : ℝ) * (v : ℝ) * (1 - v) * ((kapLoQ v : ℚ) : ℝ) := by
    have := mul_pos (mul_pos (mul_pos two_pos LqLo_pos) hvv) hkR
    nlinarith [this]
  have hDle : 2 * ((LqLo : ℚ) : ℝ) * (v : ℝ) * (1 - v) * ((kapLoQ v : ℚ) : ℝ) ≤
      2 * Real.log 2 * (v : ℝ) * (1 - v) * kap (v : ℝ) := by
    have h1 : ((LqLo : ℚ) : ℝ) * ((kapLoQ v : ℚ) : ℝ) ≤ Real.log 2 * kap (v : ℝ) :=
      mul_le_mul LqLo_le' hk1 hkR.le hL.le
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * ((v : ℝ) * (1 - v)) by positivity)
    nlinarith [h2]
  have hNle : (1 - 2 * (v : ℝ)) * hn (v : ℝ) ≤ (1 - 2 * (v : ℝ)) * ((HnumHi v : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hn2 hr
  have hN0 : 0 ≤ (1 - 2 * (v : ℝ)) * ((HnumHi v : ℚ) : ℝ) :=
    mul_nonneg hr (hhn0.trans hn2)
  have hT : (1 - 2 * (v : ℝ)) * hn (v : ℝ) / (2 * Real.log 2 * (v : ℝ) * (1 - v) * kap (v : ℝ)) ≤
      (1 - 2 * (v : ℝ)) * ((HnumHi v : ℚ) : ℝ) /
      (2 * ((LqLo : ℚ) : ℝ) * (v : ℝ) * (1 - v) * ((kapLoQ v : ℚ) : ℝ)) :=
    (div_le_div_of_nonneg_right hNle (hDlo.le.trans hDle)).trans
      (div_le_div_of_nonneg_left hN0 hDlo hDle)
  have hJ := J_le hpt hv2R.le
  simp only [slopeHi]
  push_cast
  unfold radialSlope
  linarith

/-- `slopeLo v ≤ Θ(x)` from an upper contact bracket `radialContact (2x) 1 ≤ v`. -/
theorem theta_ge {x : ℝ} {v : ℚ} (hx : 0 < x) (hok : slopeLoOk v = true)
    (hres : 1 - 2 * (v : ℝ) ≤ 2 * x * ((Hlo v : ℚ) : ℝ)) :
    ((slopeLo v : ℚ) : ℝ) ≤ e8Theta x := by
  have hok' := hok
  simp only [slopeLoOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨hpt, hv2⟩, -⟩, -⟩, -⟩ := hok'
  obtain ⟨hv0, -⟩ := ptOk_pos hpt
  have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
  have hv2R : (v : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h'
    linarith
  have hc := ZeroCapLeftStationaryThetaBracket.contact_upper_of_entropy_lower hx hv0R.le hv2R.le
    (H_bounds hpt).1 hres
  exact (slopeLo_le hok).trans
    (ZeroCapLeftStationaryThetaBracket.e8Theta_lower_of_contact_upper hx hv0R hv2R hc)

/-- `Θ(x) ≤ slopeHi v` from a lower contact bracket `v ≤ radialContact (2x) 1`. -/
theorem theta_le {x : ℝ} {v : ℚ} (hx : 0 < x) (hok : slopeHiOk v = true)
    (hres : 2 * x * ((Hhi v : ℚ) : ℝ) ≤ 1 - 2 * (v : ℝ)) :
    e8Theta x ≤ ((slopeHi v : ℚ) : ℝ) := by
  have hok' := hok
  simp only [slopeHiOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨hpt, hv2⟩, -⟩ := hok'
  obtain ⟨hv0, -⟩ := ptOk_pos hpt
  have hv0R : (0 : ℝ) < v := by exact_mod_cast hv0
  have hv2R : (v : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h'
    linarith
  have hc := ZeroCapLeftStationaryThetaBracket.contact_lower_of_entropy_upper hx hv0R.le hv2R.le
    (H_bounds hpt).2 hres
  exact (ZeroCapLeftStationaryThetaBracket.e8Theta_upper_of_contact_lower hx hv0R hv2R hc).trans
    (le_slopeHi hok)

/-- Kernel check of one capital box. -/
def capLeafOK (B : B3) (w : CapWit) : Bool :=
  decide (0 < B.a0) && decide (0 < B.b0) &&
    slopeLoOk w.vA && slopeLoOk w.vW && slopeHiOk w.vS &&
    decide (1 - 2 * w.vA ≤ 2 * B.a0 * Hlo w.vA) &&
    decide (1 - 2 * w.vW ≤ 2 * B.b0 * Hlo w.vW) &&
    decide (2 * (B.a1 + 2 * B.b1) * Hhi w.vS ≤ 1 - 2 * w.vS) &&
    decide (slopeHi w.vS ≤ slopeLo w.vA + slopeLo w.vW)

theorem theta_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : e8Theta x ≤ e8Theta y :=
  strictMonoOn_e8Theta_pos.monotoneOn (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (hx.trans_le hxy)) hxy

/-- Soundness of one capital box. -/
theorem capLeaf_sound {B : B3} {w : CapWit} (h : capLeafOK B w = true) {U W : ℝ}
    (hU0 : (B.a0 : ℝ) ≤ U) (hU1 : U ≤ (B.a1 : ℝ)) (hW0 : (B.b0 : ℝ) ≤ W) (hW1 : W ≤ (B.b1 : ℝ)) :
    e8Theta (U + 2 * W) ≤ e8Theta U + e8Theta W := by
  simp only [capLeafOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha0, hb0⟩, hokA⟩, hokW⟩, hokS⟩, hrA⟩, hrW⟩, hrS⟩, hfin⟩ := h
  have ha0R : (0 : ℝ) < B.a0 := by exact_mod_cast ha0
  have hb0R : (0 : ℝ) < B.b0 := by exact_mod_cast hb0
  have hrA' : 1 - 2 * (w.vA : ℝ) ≤ 2 * (B.a0 : ℝ) * ((Hlo w.vA : ℚ) : ℝ) := by exact_mod_cast hrA
  have hrW' : 1 - 2 * (w.vW : ℝ) ≤ 2 * (B.b0 : ℝ) * ((Hlo w.vW : ℚ) : ℝ) := by exact_mod_cast hrW
  have hrS' : 2 * ((B.a1 : ℝ) + 2 * (B.b1 : ℝ)) * ((Hhi w.vS : ℚ) : ℝ) ≤ 1 - 2 * (w.vS : ℝ) := by
    exact_mod_cast hrS
  have hfin' : ((slopeHi w.vS : ℚ) : ℝ) ≤ ((slopeLo w.vA : ℚ) : ℝ) + ((slopeLo w.vW : ℚ) : ℝ) := by
    exact_mod_cast hfin
  have hUpos : 0 < U := ha0R.trans_le hU0
  have hWpos : 0 < W := hb0R.trans_le hW0
  have hSpos : 0 < (B.a1 : ℝ) + 2 * (B.b1 : ℝ) := by linarith
  have hA := theta_ge ha0R hokA hrA'
  have hW := theta_ge hb0R hokW hrW'
  have hS := theta_le hSpos hokS hrS'
  have h1 := theta_mono (show 0 < U + 2 * W by linarith) (show U + 2 * W ≤ (B.a1 : ℝ) + 2 * (B.b1 : ℝ)
    by linarith)
  have h2 := theta_mono ha0R hU0
  have h3 := theta_mono hb0R hW0
  linarith

/-- Root box of the capital certificate in `(U, W)`. -/
def capRoot : B3 := ⟨21 / 200, 128, 303 / 50, 128, 0, 0⟩

/-- A capital tree whose leaves all pass the kernel check certifies the inequality on the root. -/
theorem cap_cover {T : PT CapWit}
    (hT : T.allLeaves (fun p w => capLeafOK (capRoot.ofPath p) w) = true)
    {U W : ℝ} (hU0 : 21 / 200 ≤ U) (hU1 : U ≤ 128) (hW0 : 303 / 50 ≤ W) (hW1 : W ≤ 128) :
    e8Theta (U + 2 * W) ≤ e8Theta U + e8Theta W := by
  have hroot : capRoot.Mem U W 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [capRoot] <;> push_cast <;> linarith
  obtain ⟨q, hq, hmem⟩ := PT.cover capRoot T hroot
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hmem
  exact capLeaf_sound (PT.allLeaves_sound hT q hq) h1 h2 h3 h4

end CKLaneN1.Capital

end


