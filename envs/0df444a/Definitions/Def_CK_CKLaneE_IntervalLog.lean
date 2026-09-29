-- Prove2me | Definitions.Def_CK_CKLaneE_IntervalLog
-- name    : CK_CKLaneE_IntervalLog
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:02:44.819369+00:00
-- url     : https://prove2.me/theorems/5084eb88-9cc8-400d-97d4-e4ee3814ac40
-- title:
--   Courtade–Kumar proof module `CKLaneE.IntervalLog` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.IntervalLog` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.IntervalLog` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.IntervalLog (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/IntervalLog.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog
import Definitions.Def_CK_CKLaneE_SlopeBounds

-- ===== source module CKLaneE.IntervalLog =====
section

/-!
# Lane E: rational enclosures of `log`, `H` and the slope anchor, kernel-checkable

All executable data are `ℚ` / `ℤ` / `ℕ`.  Logarithms at rational points come from the corpus
checker `GeneralCK.Certificates.DyadicFastLog` (atanh series with outward dyadic rounding at
scale `2^64`), whose soundness theorem `DyadicFastLog.check_sound` is reused verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.IL

open GeneralCK GeneralCK.Certificates

abbrev prec : ℕ := 64
def terms : ℕ := 20

/-- Largest `e` (up to fuel) with `num * 2^e ≤ den`; only a reduction choice, validity is checked. -/
def redExp : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, e => e
  | fuel + 1, num, den, e =>
      if num * 2 ^ (e + 1) ≤ den then redExp fuel num den (e + 1) else e

def expOf (num den : ℕ) : ℕ := redExp 96 num den 0

def logApprox (num den : ℕ) : DyadicInterval prec :=
  DyadicFastLog.approximation prec (num : ℤ) (den : ℤ) (expOf num den) terms

def logOk (num den : ℕ) : Bool :=
  DyadicFastLog.check (num : ℤ) (den : ℤ) (expOf num den) terms (logApprox num den)

def toQlo (I : DyadicInterval prec) : ℚ := (I.lo : ℚ) / (2 ^ prec : ℚ)
def toQhi (I : DyadicInterval prec) : ℚ := (I.hi : ℚ) / (2 ^ prec : ℚ)

theorem contains_toQ {I : DyadicInterval prec} {x : ℝ} (h : I.Contains x) :
    ((toQlo I : ℚ) : ℝ) ≤ x ∧ x ≤ ((toQhi I : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  have hs : ((DyadicInterval.scale prec : ℤ) : ℝ) = (2 : ℝ) ^ prec := by
    simp [DyadicInterval.scale]
  rw [hs] at h1 h2
  have hp : (0 : ℝ) < (2 : ℝ) ^ prec := by positivity
  constructor
  · simp only [toQlo, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
    rw [div_le_iff₀ hp]
    linarith
  · simp only [toQhi, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
    rw [le_div_iff₀ hp]
    linarith

theorem logOk_sound {num den : ℕ} (h : logOk num den = true) :
    ((toQlo (logApprox num den) : ℚ) : ℝ) ≤ Real.log ((num : ℝ) / den) ∧
      Real.log ((num : ℝ) / den) ≤ ((toQhi (logApprox num den) : ℚ) : ℝ) := by
  have hc := DyadicFastLog.check_sound h
  simp only [Int.cast_natCast] at hc
  exact contains_toQ hc

/-! ## Rational points -/

def ptOk (q : ℚ) : Bool :=
  decide (0 < q ∧ q < 1) && logOk q.num.toNat q.den && logOk (q.den - q.num.toNat) q.den

def lLo (q : ℚ) : ℚ := toQlo (logApprox q.num.toNat q.den)
def lHi (q : ℚ) : ℚ := toQhi (logApprox q.num.toNat q.den)
def l1Lo (q : ℚ) : ℚ := toQlo (logApprox (q.den - q.num.toNat) q.den)
def l1Hi (q : ℚ) : ℚ := toQhi (logApprox (q.den - q.num.toNat) q.den)

theorem ptOk_pos {q : ℚ} (h : ptOk q = true) : 0 < q ∧ q < 1 := by
  simp only [ptOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem cast_num_toNat {q : ℚ} (hq : 0 < q) : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
  have h0 : 0 ≤ q.num := (Rat.num_pos.mpr hq).le
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

theorem num_toNat_le_den {q : ℚ} (hq : 0 < q) (hq1 : q < 1) : q.num.toNat ≤ q.den := by
  have h0 : 0 ≤ q.num := (Rat.num_pos.mpr hq).le
  have hlt : q.num < q.den := by
    exact Rat.num_lt_denom_iff.mpr hq1
  omega

theorem ptOk_sound {q : ℚ} (h : ptOk q = true) :
    ((lLo q : ℚ) : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ ((lHi q : ℚ) : ℝ) ∧
    ((l1Lo q : ℚ) : ℝ) ≤ Real.log (1 - (q : ℝ)) ∧ Real.log (1 - (q : ℝ)) ≤ ((l1Hi q : ℚ) : ℝ) := by
  have hq := ptOk_pos h
  simp only [ptOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := logOk_sound h.1.2
  have h2 := logOk_sound h.2
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hq_eq : (q : ℝ) = ((q.num.toNat : ℕ) : ℝ) / q.den := by
    rw [cast_num_toNat hq.1, Rat.cast_def]
  have hq1_eq : 1 - (q : ℝ) = (((q.den - q.num.toNat : ℕ) : ℕ) : ℝ) / q.den := by
    rw [Nat.cast_sub (num_toNat_le_den hq.1 hq.2), cast_num_toNat hq.1, Rat.cast_def]
    field_simp
  rw [← hq_eq] at h1
  rw [← hq1_eq] at h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-! ## Binary entropy -/

def LqLo : ℚ := 34657359 / 50000000
def LqHi : ℚ := 693147181 / 1000000000

/-- Reuses the corpus certificate `DyadicLogSeries.pilot_log_two`. -/
theorem log_two_mem : ((LqLo : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((LqHi : ℚ) : ℝ) := by
  have h := GeneralCK.Certificates.DyadicLogSeries.pilot_log_two
  constructor
  · simp only [LqLo]; push_cast; exact h.1
  · simp only [LqHi]; push_cast; exact h.2

def HnumLo (q : ℚ) : ℚ := -(q * lHi q) - (1 - q) * l1Hi q
def HnumHi (q : ℚ) : ℚ := -(q * lLo q) - (1 - q) * l1Lo q
def Hlo (q : ℚ) : ℚ := if 0 ≤ HnumLo q then HnumLo q / LqHi else 0
def Hhi (q : ℚ) : ℚ := HnumHi q / LqLo

theorem H_bounds {q : ℚ} (h : ptOk q = true) :
    ((Hlo q : ℚ) : ℝ) ≤ H (q : ℝ) ∧ H (q : ℝ) ≤ ((Hhi q : ℚ) : ℝ) := by
  have hq := ptOk_pos h
  obtain ⟨h1, h2, h3, h4⟩ := ptOk_sound h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1
  have hq1 : (q : ℝ) < 1 := by exact_mod_cast hq.2
  obtain ⟨hL1, hL2⟩ := log_two_mem
  have hL : 0 < Real.log 2 := log_two_pos
  have hLlo : (0 : ℝ) < ((LqLo : ℚ) : ℝ) := by simp only [LqLo]; norm_num
  set N : ℝ := -((q : ℝ) * Real.log q) - (1 - (q : ℝ)) * Real.log (1 - q) with hN
  have hHN : H (q : ℝ) = N / Real.log 2 := by rw [H_eq_logs]
  have hNlo : ((HnumLo q : ℚ) : ℝ) ≤ N := by
    simp only [HnumLo]; push_cast
    have a1 := mul_le_mul_of_nonneg_left h2 hq0.le
    have a2 := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 1 - q)
    linarith
  have hNhi : N ≤ ((HnumHi q : ℚ) : ℝ) := by
    simp only [HnumHi]; push_cast
    have a1 := mul_le_mul_of_nonneg_left h1 hq0.le
    have a2 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 - q)
    linarith
  have hHnn : 0 ≤ H (q : ℝ) := H_nonneg hq0.le hq1.le
  have hNnn : 0 ≤ N := by
    have := hHnn; rw [hHN] at this
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hL))
  constructor
  · simp only [Hlo]
    split_ifs with hc
    · push_cast
      rw [hHN]
      have hc' : (0 : ℝ) ≤ ((HnumLo q : ℚ) : ℝ) := by exact_mod_cast hc
      calc ((HnumLo q : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((HnumLo q : ℚ) : ℝ) / Real.log 2 :=
            div_le_div_of_nonneg_left hc' hL hL2
        _ ≤ N / Real.log 2 := div_le_div_of_nonneg_right hNlo hL.le
    · simpa using hHnn
  · simp only [Hhi]; push_cast
    rw [hHN]
    have hhnn : (0 : ℝ) ≤ ((HnumHi q : ℚ) : ℝ) := hNnn.trans hNhi
    calc N / Real.log 2 ≤ ((HnumHi q : ℚ) : ℝ) / Real.log 2 := div_le_div_of_nonneg_right hNhi hL.le
      _ ≤ ((HnumHi q : ℚ) : ℝ) / ((LqLo : ℚ) : ℝ) := div_le_div_of_nonneg_left hhnn hLlo hL1

/-! ## Slope anchors -/

def lamLo (v : ℚ) : ℚ := l1Lo v - lHi v
def P1up (v : ℚ) : ℚ := 2 + (1 - 2 * v) / (v * (1 - v) * lamLo v)

/-- `anchorOk v y`: `v` is a valid anchor certifying `P1 x ≤ P1up v` for all `0 ≤ x ≤ y`. -/
def anchorOk (v y : ℚ) : Bool :=
  ptOk v && decide (v < 1 / 2 ∧ 0 < lamLo v ∧ Hhi v ≤ 1 - y)

theorem anchorOk_sound {v y : ℚ} (h : anchorOk v y = true) {x : ℝ} (hx0 : 0 ≤ x)
    (hxy : x ≤ (y : ℝ)) : Scalar.P1 x ≤ ((P1up v : ℚ) : ℝ) := by
  simp only [anchorOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpt, hv2, hlam, hH⟩ := h
  have hv := ptOk_pos hpt
  obtain ⟨h1, h2, h3, h4⟩ := ptOk_sound hpt
  obtain ⟨_, hHhi⟩ := H_bounds hpt
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv.1
  have hv12 : (v : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h
    linarith
  have hHq : ((Hhi v : ℚ) : ℝ) ≤ 1 - (y : ℝ) := by exact_mod_cast hH
  have hxv : x ≤ 1 - H (v : ℝ) := by linarith
  have hA := P1_le_anchor hv0 hv12 hx0 hxv
  have hlamR : (0 : ℝ) < ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  have hlog : ((lamLo v : ℚ) : ℝ) ≤ Real.log ((1 - (v : ℝ)) / v) := by
    rw [Real.log_div (by linarith) hv0.ne']
    simp only [lamLo]; push_cast
    linarith
  have hvv : (0 : ℝ) < (v : ℝ) * (1 - v) := by nlinarith
  have hnum : (0 : ℝ) ≤ 1 - 2 * (v : ℝ) := by linarith
  have hfrac : (1 - 2 * (v : ℝ)) / ((v : ℝ) * (1 - v) * Real.log ((1 - v) / v)) ≤
      (1 - 2 * (v : ℝ)) / ((v : ℝ) * (1 - v) * ((lamLo v : ℚ) : ℝ)) := by
    apply div_le_div_of_nonneg_left hnum (by positivity)
    exact mul_le_mul_of_nonneg_left hlog hvv.le
  have heq : ((P1up v : ℚ) : ℝ) =
      2 + (1 - 2 * (v : ℝ)) / ((v : ℝ) * (1 - v) * ((lamLo v : ℚ) : ℝ)) := by
    simp only [P1up]; push_cast; ring
  rw [heq]
  linarith

end CKLaneE.IL

#check @CKLaneE.IL.logOk_sound
#check @CKLaneE.IL.ptOk_sound
#check @CKLaneE.IL.H_bounds
#check @CKLaneE.IL.anchorOk_sound
#print axioms CKLaneE.IL.logOk_sound
#print axioms CKLaneE.IL.ptOk_sound
#print axioms CKLaneE.IL.H_bounds
#print axioms CKLaneE.IL.anchorOk_sound

end


